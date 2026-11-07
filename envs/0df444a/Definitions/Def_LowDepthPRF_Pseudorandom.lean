-- Prove2me | Definitions.Def_LowDepthPRF_Pseudorandom
-- name    : LowDepthPRF_Pseudorandom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:45.027353+00:00
-- url     : https://prove2.me/theorems/d82a3661-a145-4357-b8dd-ed33f780f67c
-- title:
--   Strong and weak pseudorandomness, $n$-wise independent hashing
-- statement:
--   Let $F=\{F_k:\{0,1\}^a\to\{0,1\}^b\}_{k\in K}$ with $K$ finite and nonempty.
--
--   1. $F$ is **$(q,t,\epsilon)$-strong pseudorandom** (Definition 3.4) if $G_0\approx_{q,t,\epsilon}G_1$, where $G_0$ gives oracle access to $F_k$ for a uniform key $k$ and $G_1$ gives oracle access to a uniformly random function $R:\{0,1\}^a\to\{0,1\}^b$. It is $(q,\infty,\epsilon)$-strong pseudorandom if this holds against adversaries of every size.
--   2. $F$ is **$(q,t,\epsilon)$-weak pseudorandom** (Definition 3.5) if $G_0\approx_{0,t,\epsilon}G_1$, where $G_0$ draws $x=(x^{(1)},\dots,x^{(q)})$ and $k$ uniformly and gives $(x,F_k(x^{(1)}),\dots,F_k(x^{(q)}))$, and $G_1$ draws $x$ and an **independent** uniform $u\in(\{0,1\}^b)^q$ and gives $(x,u)$.
--   3. $H=\{H_k:X\to Y\}$ is an **$n$-wise independent hashing** (Definition 3.6) if, on every tuple of at most $n$ distinct inputs, the outputs are independent and uniform: for distinct $x^{(1)},\dots,x^{(q)}$ with $q\le n$ and every $y\in Y^q$,
--
--   $$\Pr_k\bigl[H_k(x^{(i)})=y^{(i)}\ \text{for all } i\bigr]=|Y|^{-q}.$$
--
--   Strong pseudorandomness is the PRF notion. Weak pseudorandomness is the WPRF notion that the construction starts from. Key-uniformity is $1$-wise independence.
--
--   **Formalization Note** The weak-game sample is encoded as $qa+qb$ bits: the inputs, then the outputs. Definition 3.6 defines $n$-wise independence as $(n,\infty,0)$-strong pseudorandomness, but with the strict "advantage less than $\epsilon$" of Definition 3.2 that is unsatisfiable at $\epsilon=0$. The definition here therefore uses the equivalent sentence the paper gives ("Equivalently, … independent and uniform").
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Definitions 3.4–3.5, pp.11–12 (pdf 13–14); Definition 3.6, p.12 (pdf 14)

import Mathlib
import Definitions.Def_LowDepthPRF_FunctionFamily
import Definitions.Def_LowDepthPRF_Game

namespace LowDepthPRF

/-!
# Strong and weak pseudorandomness, n-wise independent hashing

Ding, Jain, Komargodski, *Pseudorandom Functions in NC¹ from LWE/LPN/CDH*, arXiv:2608.25213
(sha256 89a55849…), Definitions 3.4 and 3.5, pp.11–12, and Definition 3.6, p.12.

**Formalization Note.**
* Strong game (Def 3.4): `G₀` draws a key `k` and gives oracle access to `F_k`; `G₁` draws a
  uniformly random function `R : {0,1}^a → {0,1}^b` and gives oracle access to `R`. No sample.
* Weak game with `q` samples (Def 3.5): `G₀` draws `x ∈ (X)^q` and a key `k` and gives the sample
  `(x, F_k(x^{(1)}), …, F_k(x^{(q)}))`; `G₁` draws `x` and an **independent** `u ∈ Y^q` and gives
  `(x, u)`. The sample is encoded as `q·a + q·b` bits: the `q` inputs, then the `q` outputs
  (`flatten`). There is no oracle and the adversary may make no oracle query (`q = 0` in `≈`).
* `TypePR ty` packages "`type ∈ {strong, weak}`" of Lemmas 3.10–3.12.
* Definition 3.6 defines an `n`-wise independent hashing as `(n, ∞, 0)`-strong pseudorandom and
  adds "Equivalently, on every set of at most `n` distinct inputs, the outputs are independent and
  uniform". With the strict "advantage less than `ε`" of Definition 3.2, `ε = 0` would be
  unsatisfiable, so `NWiseIndep` is defined by the "Equivalently" sentence (perfect
  indistinguishability), for families with arbitrary finite input and output sets.
-/

/-- The real strong-pseudorandomness game: oracle access to `F_k` for a uniform key `k`. -/
def strongReal {K : Type} [Fintype K] [Nonempty K] {a b : ℕ} (F : FunFam K a b) : Game 0 a b where
  Ω := K
  sample := fun _ i => i.elim0
  oracle := fun k => F k

/-- The ideal strong-pseudorandomness game: oracle access to a uniformly random function. -/
def strongIdeal (a b : ℕ) : Game 0 a b where
  Ω := (Fin a → Bool) → (Fin b → Bool)
  sample := fun _ i => i.elim0
  oracle := fun R => R

/-- The bit encoding `(x^{(1)}, …, x^{(q)}, y^{(1)}, …, y^{(q)})` of a weak-game sample. -/
def weakSample {q a b : ℕ} (x : Fin q → Fin a → Bool) (y : Fin q → Fin b → Bool) :
    Fin (q * a + q * b) → Bool :=
  Fin.append (flatten x) (flatten y)

/-- The real weak-pseudorandomness game with `q` samples: `(x, G(k, x))`. -/
def weakReal {K : Type} [Fintype K] [Nonempty K] {a b : ℕ} (G : FunFam K a b) (q : ℕ) :
    Game (q * a + q * b) 0 0 where
  Ω := (Fin q → Fin a → Bool) × K
  sample := fun ω => weakSample ω.1 (fun i => G ω.2 (ω.1 i))
  oracle := fun _ _ i => i.elim0

/-- The ideal weak-pseudorandomness game with `q` samples: `(x, u)` with `u` independent of `x`. -/
def weakIdeal (a b q : ℕ) : Game (q * a + q * b) 0 0 where
  Ω := (Fin q → Fin a → Bool) × (Fin q → Fin b → Bool)
  sample := fun ω => weakSample ω.1 ω.2
  oracle := fun _ _ i => i.elim0

/-- Definition 3.4: `F` is `(q, t, ε)`-strong pseudorandom. -/
def StrongPR {K : Type} [Fintype K] [Nonempty K] {a b : ℕ} (F : FunFam K a b) (q : ℕ)
    (t ε : ℝ) : Prop :=
  Indist (strongReal F) (strongIdeal a b) q t ε

/-- `F` is `(q, ∞, ε)`-strong pseudorandom (adversaries of every size). -/
def StrongPRAll {K : Type} [Fintype K] [Nonempty K] {a b : ℕ} (F : FunFam K a b) (q : ℕ)
    (ε : ℝ) : Prop :=
  IndistAll (strongReal F) (strongIdeal a b) q ε

/-- Definition 3.5: `G` is `(q, t, ε)`-weak pseudorandom (`q` samples, no oracle queries). -/
def WeakPR {K : Type} [Fintype K] [Nonempty K] {a b : ℕ} (G : FunFam K a b) (q : ℕ)
    (t ε : ℝ) : Prop :=
  Indist (weakReal G q) (weakIdeal a b q) 0 t ε

/-- `type ∈ {strong, weak}`. -/
inductive PRType
  | strong
  | weak

/-- `(q, t, ε)`-type pseudorandom. -/
def TypePR {K : Type} [Fintype K] [Nonempty K] {a b : ℕ} : PRType → FunFam K a b → ℕ → ℝ → ℝ →
    Prop
  | .strong, F, q, t, ε => StrongPR F q t ε
  | .weak, F, q, t, ε => WeakPR F q t ε

/-- Definition 3.6 ("Equivalently" sentence): `H` is an `n`-wise independent hashing — on every
tuple of at most `n` distinct inputs the outputs are independent and uniform: each output tuple
`y ∈ Y^{q}` has probability `1/|Y|^q` over a uniform key. -/
def NWiseIndep {K X Y : Type} [Fintype K] [Fintype Y] (H : K → X → Y) (n : ℕ) : Prop :=
  ∀ q ≤ n, ∀ x : Fin q → X, Function.Injective x → ∀ y : Fin q → Y,
    uprob (fun k : K => ∀ i, H k (x i) = y i) = 1 / (Fintype.card Y : ℝ) ^ q

end LowDepthPRF


