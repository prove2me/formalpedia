-- Prove2me | Definitions.Def_LowDepthPRF_FunctionFamily
-- name    : LowDepthPRF_FunctionFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:43.355725+00:00
-- url     : https://prove2.me/theorems/d4ff2060-6f02-44a0-9d7b-064c918034b9
-- title:
--   Function families, $(s,d)$-function families, sums $\oplus$ and products $\times n$
-- statement:
--   A **function family** with key space $K$ is $F=\{F_k:\{0,1\}^a\to\{0,1\}^b,\ k\in K\}$. When keys are bit strings, $K=\{0,1\}^{\ell}$, $F$ is an **$(s,d)$-function family** (Definition 3.1) if its universal evaluation function $(k,x)\mapsto F_k(x)$ is computed by one circuit of size at most $s$ and depth at most $d$, with input $k$ followed by $x$. It has **evaluation size at most $s$** if some such circuit has size at most $s$.
--
--   The **sum** of families $F_1,\dots,F_n$ with the same input and output lengths (Definition 3.8) has key $(k_1,\dots,k_n)$ and
--
--   $$(F_{k_1}\oplus\cdots\oplus F_{k_n})(x)=F_{k_1}(x)\oplus\cdots\oplus F_{k_n}(x).$$
--
--   $F^{\oplus n}$ is the $n$-fold sum of one family. The **$n$-product** (Definition 3.9) evaluates $n$ independent keys on the same input, $x\mapsto(F_{k_1}(x),\dots,F_{k_n}(x))\in(\{0,1\}^b)^n$. The **output restriction** of Lemma 3.12 keeps the first $b'$ of the $b$ output bits.
--
--   These are the closure operations of §3: sums amplify randomness, and products extend the range.
--
--   **Formalization Note** $Y^n$ and $K^n$ are encoded as $nb$ and $n\ell$ bits, block $i$ occupying positions $ib,\dots,ib+b-1$. The size and depth claims printed inside Definitions 3.8 and 3.9 are not built into the definitions. The product's claim is a clause of Lemma 3.11.
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Definition 3.1, p.11 (pdf 13); Definition 3.8, p.12 (pdf 14); Definition 3.9, p.13 (pdf 15); Lemma 3.12, p.13 (pdf 15)

import Mathlib
import Definitions.Def_LowDepthPRF_Circuit

namespace LowDepthPRF

/-!
# Function families, (s, d)-function families, sums and products

Ding, Jain, Komargodski, *Pseudorandom Functions in NC¹ from LWE/LPN/CDH*, arXiv:2608.25213
(sha256 89a55849…), Definition 3.1, p.11; Definition 3.8, p.12; Definition 3.9, p.13; and the
output restriction of Lemma 3.12, p.13.

**Formalization Note.**
* A function family with key space `K` and inputs and outputs of `a` and `b` bits is a map
  `F : K → (Fin a → Bool) → (Fin b → Bool)`, `F k = F_k`. The adversaries of the paper see only
  inputs and outputs, so those are bit strings; keys may be any finite type.
* Definition 3.1 needs the key to be fed to a circuit, so `IsSizeDepth` is stated for bit-string
  keys `Fin kl → Bool`: the universal evaluation function `(k, x) ↦ F_k(x)` is computed by one
  well-formed circuit, of size at most `s` **and** depth at most `d`, whose input is `k` followed
  by `x` (`Fin.append`). The bounds are real numbers; for natural `s, d` this is the paper's
  notion.
* `Y^n` is encoded as `n·b` bits, block `i` occupying bits `i·b, …, i·b + b − 1`
  (`finProdFinEquiv`); keys of a product are encoded the same way.
* The size and depth clauses printed inside Definitions 3.8 and 3.9 are claims, not part of the
  definitions; they are not built in here.
-/

/-- A function family `{F_k : {0,1}^a → {0,1}^b, k ∈ K}`. -/
abbrev FunFam (K : Type) (a b : ℕ) : Type := K → (Fin a → Bool) → (Fin b → Bool)

/-- Definition 3.1: `F` is an `(s, d)`-function family — its universal evaluation function is
computed by one circuit of size at most `s` and depth at most `d`. -/
def IsSizeDepth {kl a b : ℕ} (F : FunFam (Fin kl → Bool) a b) (s d : ℝ) : Prop :=
  ComputesWithin (fun z : Fin (kl + a) → Bool =>
    F (fun i => z (Fin.castAdd a i)) (fun i => z (Fin.natAdd kl i))) s d

/-- "Evaluation size at most `s`" (Lemma 3.10): the universal evaluation function is computed by a
circuit of size at most `s`, of any depth. -/
def HasEvalSize {kl a b : ℕ} (F : FunFam (Fin kl → Bool) a b) (s : ℝ) : Prop :=
  ∃ d : ℝ, IsSizeDepth F s d

/-- XOR of finitely many bits (`false` for none). -/
def bigXor {n : ℕ} (v : Fin n → Bool) : Bool := (List.ofFn v).foldr xor false

/-- Flatten `n` blocks of `b` bits into `n·b` bits (block `i` is bits `i·b, …, i·b+b-1`). -/
def flatten {n b : ℕ} (v : Fin n → Fin b → Bool) : Fin (n * b) → Bool :=
  fun j => v (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2

/-- Cut `n·b` bits into `n` blocks of `b` bits (inverse of `flatten`). -/
def unflatten {n b : ℕ} (z : Fin (n * b) → Bool) : Fin n → Fin b → Bool :=
  fun i j => z (finProdFinEquiv (i, j))

/-- Definition 3.8: the sum `F_1 ⊕ ⋯ ⊕ F_n` of families with key spaces `K_i`: key
`(k_1, …, k_n)`, output `F_{k_1}(x) ⊕ ⋯ ⊕ F_{k_n}(x)`. -/
def sumFam {n a b : ℕ} {K : Fin n → Type} (F : (i : Fin n) → FunFam (K i) a b) :
    FunFam ((i : Fin n) → K i) a b :=
  fun k x j => bigXor (fun i => F i (k i) x j)

/-- `F^{⊕n}`, the `n`-fold sum of one family. -/
def sumPow {K : Type} {a b : ℕ} (F : FunFam K a b) (n : ℕ) : FunFam (Fin n → K) a b :=
  sumFam (K := fun _ => K) (fun _ => F)

/-- Definition 3.9: the `n`-product `F^{×n}` with key `(k_1, …, k_n) ∈ K^n` encoded as `n·kl` bits:
`x ↦ (F_{k_1}(x), …, F_{k_n}(x)) ∈ Y^n`, encoded as `n·b` bits. -/
def prodFam {kl a b : ℕ} (F : FunFam (Fin kl → Bool) a b) (n : ℕ) :
    FunFam (Fin (n * kl) → Bool) a (n * b) :=
  fun k x => flatten (fun i => F (unflatten k i) x)

/-- Output restriction (Lemma 3.12): keep the first `b'` of the `b` output bits. -/
def restrictFam {K : Type} {a b : ℕ} (F : FunFam K a b) (b' : ℕ) (h : b' ≤ b) : FunFam K a b' :=
  fun k x j => F k x (Fin.castLE h j)

end LowDepthPRF


