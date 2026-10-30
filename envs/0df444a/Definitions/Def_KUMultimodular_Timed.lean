-- Prove2me | Definitions.Def_KUMultimodular_Timed
-- name    : KUMultimodular_Timed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:56:43.507233+00:00
-- url     : https://prove2.me/theorems/f7ff1275-b160-40e0-976a-24881d1b08a4
-- title:
--   Bit-cost model: costed computations and the cited subroutines
-- statement:
--   A **costed computation** returning a value of type $\alpha$ is a pair $(v, c)$ of a value $v$ and a number $c \in \mathbb N$ of bit operations. Sequencing two computations adds their costs; returning a value costs nothing.
--
--   Write $\mathrm{bits}(n) = \lfloor \log_2 n\rfloor + 2$ for the bit size of $n \ge 1$ (and $\mathrm{bits}(0) = 1$), and for a list of naturals the sum of the bit sizes of its entries plus its length. The model charges:
--
--   1. **linear operations** (reading an input entry, one step of a traversal of a list, cutting a list into blocks, transposing or concatenating lists, addition and truncated subtraction of integers, and a look-up in a table stored in lexicographic order at a multi-index $(a_0,\dots,a_{k-1})$) the bit size of the data they touch;
--   2. **cited subroutines** the quasi-linear amount
--   $$\mathrm{ql}(S) = S\,(\lfloor \log_2 S\rfloor + 1)^4,$$
--   where $S$ is the total bit size of the arguments and of the result. Each returns the exact mathematical result. They are: integer multiplication and division with remainder, powers by repeated squaring (a sequence of multiplications), the list of primes up to $L$ (sieve of Eratosthenes, charged with $L$ added to $S$), the residues of $x$ modulo a list of moduli (remainder tree), Chinese remaindering (the least $y < \prod_h p_h$ with $y \equiv a_h \pmod{p_h}$ for all $h$), the value $(\sum_j c_j M^j) \bmod r'$, the $K$ lowest base-$M$ digits of an integer, addition in $\mathbb F_p$ (charged $\mathrm{ql}(3\,\mathrm{bits}(p))$), and **fast univariate multipoint evaluation over all of $\mathbb F_p$**: given $g_0,\dots,g_{p-1}\in\mathbb F_p$, the list $\bigl(\sum_j g_j a^j\bigr)_{a=0,\dots,p-1}$.
--
--   This is the accounting of Kedlaya and Umans, who bound the running time of their algorithms in bit operations by charging every step the cited cost of a standard subroutine (Figure 1 for univariate arithmetic; [Sho08, §5.4] for the sieve; [Ber, §18, §23] and [vzGG99, Theorems 10.24, 10.25] for remainder trees and Chinese remaindering). Each charge here is at least the cited cost up to a constant factor. The algorithms of Theorems 4.1, 4.2 and 4.4 are written step by step in this model; no subroutine acts on a multivariate polynomial or on the whole list of points.
--
--   **Formalization Note** `Timed α` is a structure with fields `val` and `cost` and a `Monad` instance; `tick n` charges `n`. The primitives are `addC`, `subC`, `mulC`, `divModC`, `powC`, `primesUpToC`, `remTreeC`, `crtC` (value `crtValue`), `evalAtModC`, `radixC`, `fpAddC`, `uniEvalAllC`, and the structural operations `mapT`, `chunksT`, `transposeT`, `flattenT`, `regroupT`, `reverseT`, `readC`.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), §2.2 Figure 1, p. 8, and proofs of Theorems 4.1 and 4.2, pp. 12–13 (costs of the cited subroutines)

import Mathlib

namespace KUMultimodular

/-! # A bit-cost model

Kedlaya–Umans (Dagstuhl Seminar Proceedings 08381 (2008), §2.2 and §4, pp. 8–16) count *bit
operations* and charge each step of their algorithms the cited cost of a standard subroutine
(fast integer and polynomial arithmetic, Figure 1 p. 8; the sieve of Eratosthenes, remainder trees
and fast Chinese remaindering, p. 13; fast univariate multipoint evaluation, p. 12). This file
fixes that model: a computation is a value together with its number of bit operations, linear
operations are charged the bit size of their operands, and each cited subroutine returns the exact
mathematical result and is charged `ql S = S · (⌊log₂ S⌋ + 1)⁴`, where `S` is the total bit size of
its arguments and result. -/

/-- A computation returning `val` after `cost` bit operations. -/
structure Timed (α : Type) where
  /-- the result -/
  val : α
  /-- the number of bit operations performed -/
  cost : ℕ

/-- `pure` costs nothing; `bind` adds the costs of both parts. -/
instance : Monad Timed where
  pure a := ⟨a, 0⟩
  bind x f := ⟨(f x.val).val, x.cost + (f x.val).cost⟩

/-- `n` bit operations of bookkeeping. -/
def tick (n : ℕ) : Timed Unit := ⟨(), n⟩

/-- Bit size of a natural number (`Nat.size n + 1`, so at least `1`). -/
def bits (n : ℕ) : ℕ := Nat.size n + 1

/-- The quasi-linear charge `S · (⌊log₂ S⌋ + 1)⁴` of a cited subroutine on data of total bit size `S`. -/
def ql (s : ℕ) : ℕ := s * (Nat.log 2 s + 1) ^ 4

/-- Bit size of a list of natural numbers: the sum of the entries' `bits`, plus its length. -/
def lsize (l : List ℕ) : ℕ := (l.map bits).sum + l.length

/-- Bit size of a residue in `ℤ/pℤ`, represented by its lift in `{0, …, p-1}`. -/
def zw {p : ℕ} (x : ZMod p) : ℕ := bits x.val

/-! ## Traversals (each step pays one tick, plus the weight of the entry it moves) -/

/-- Map a costed function over a list; each step costs one tick plus the cost of `f`. -/
def mapT {α β : Type} (f : α → Timed β) (l : List α) : Timed (List β) :=
  l.mapM (fun a => do tick 1; f a)

/-- Cut a list into consecutive blocks of length `n`; charged the weight of every moved entry. -/
def chunksT {α : Type} (w : α → ℕ) (n : ℕ) (l : List α) : Timed (List (List α)) :=
  ⟨l.toChunks n, (l.map (fun x => w x + 1)).sum + 1⟩

/-- Transpose a rectangular list of lists; charged the weight of every moved entry. -/
def transposeT {α : Type} (w : α → ℕ) (l : List (List α)) : Timed (List (List α)) :=
  ⟨l.transpose, ((l.map (fun r => (r.map (fun x => w x + 1)).sum)).sum) + l.length + 1⟩

/-- Concatenate a list of lists; charged the weight of every moved entry. -/
def flattenT {α : Type} (w : α → ℕ) (l : List (List α)) : Timed (List α) :=
  ⟨l.flatten, ((l.map (fun r => (r.map (fun x => w x + 1)).sum)).sum) + l.length + 1⟩

/-- Regroup `rows` (a list of lists of length `k`) by position: entry `h` of the result is the list
of the `h`-th entries of the rows. Charged the weight of every moved entry. -/
def regroupT {α : Type} (w : α → ℕ) (k : ℕ) (dflt : α) (rows : List (List α)) :
    Timed (List (List α)) :=
  ⟨(List.range k).map (fun h => rows.map (fun r => r.getD h dflt)),
    ((rows.map (fun r => (r.map (fun x => w x + 1)).sum)).sum) + k + rows.length + 1⟩

/-- Reverse a list of natural numbers; charged its bit size. -/
def reverseT (l : List ℕ) : Timed (List ℕ) := ⟨l.reverse, lsize l + 1⟩

/-- **Multi-dimensional table read**: the entry of the table `T` (stored in lexicographic order,
first index most significant, each index in `{0, …, radix-1}`) at the multi-index `idx`. Charged
linearly: the bit size of the indices, of the radix, and of the entry read (the table look-up of
Step 3 in the proof of Theorem 4.1, p. 12). -/
def readC {α : Type} (w : α → ℕ) (T : List α) (dflt : α) (idx : List ℕ) (radix : ℕ) : Timed α :=
  let v := T.getD (idx.foldl (fun acc a => acc * radix + a) 0) dflt
  ⟨v, lsize idx + bits radix + w v + 1⟩

/-! ## Linear integer primitives -/

/-- Addition, charged the bit sizes of operands and result. -/
def addC (a b : ℕ) : Timed ℕ := ⟨a + b, bits a + bits b + bits (a + b)⟩

/-- Truncated subtraction, charged the bit sizes of operands and result. -/
def subC (a b : ℕ) : Timed ℕ := ⟨a - b, bits a + bits b + bits (a - b)⟩

/-! ## Cited quasi-linear primitives (exact result, charge `ql` of total bit size) -/

/-- Fast integer multiplication (Figure 1, p. 8, read over `ℤ`). -/
def mulC (a b : ℕ) : Timed ℕ := ⟨a * b, ql (bits a + bits b + bits (a * b))⟩

/-- Fast integer division with remainder (Figure 1, "Remainder", read over `ℤ`). -/
def divModC (a b : ℕ) : Timed (ℕ × ℕ) :=
  ⟨(a / b, a % b), ql (bits a + bits b + bits (a / b) + bits (a % b))⟩

/-- Power `a ^ n` by repeated squaring with `mulC`, plus a parity test of `n` at each level. -/
def powC (a : ℕ) (n : ℕ) : Timed ℕ :=
  if h : n = 0 then pure 1 else do
    let s ← powC a (n / 2)
    let s2 ← mulC s s
    tick (bits n)
    if n % 2 = 1 then mulC s2 a else pure s2
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

/-- The primes `≤ L`, by the sieve of Eratosthenes ([Sho08, §5.4], cited p. 13). Charged `ql` of
`L` plus the bit size of the output. -/
def primesUpToC (L : ℕ) : Timed (List ℕ) :=
  let ps := (List.range (L + 1)).filter (fun n => decide (Nat.Prime n))
  ⟨ps, ql (L + 1 + bits L + lsize ps)⟩

/-- The residues of `x` modulo every modulus in `ps`, by a remainder tree ([Ber, §18],
[vzGG99, Theorem 10.24], cited p. 13). -/
def remTreeC (x : ℕ) (ps : List ℕ) : Timed (List ℕ) :=
  let res := ps.map (x % ·)
  ⟨res, ql (bits x + lsize ps + lsize res)⟩

/-- The value of Chinese remaindering: the least `y < ∏ ps` with `y ≡ res_h (mod ps_h)` for all
`h` (`0` if there is none). For pairwise coprime moduli it is the unique such `y`. -/
def crtValue (res ps : List ℕ) : ℕ :=
  ((List.range ps.prod).find? (fun y => (List.zip res ps).all (fun q => y % q.2 == q.1 % q.2))).getD 0

/-- Fast Chinese remaindering ([Ber, §23], [vzGG99, Theorem 10.25], cited p. 13). -/
def crtC (res ps : List ℕ) : Timed ℕ :=
  ⟨crtValue res ps, ql (lsize res + lsize ps + bits (crtValue res ps))⟩

/-- `(Σ_j cs_j · M^j) mod r'`: evaluation of a univariate integer polynomial at `M` followed by a
remainder (Figure 1 multiplication and remainder, read over `ℤ`; Step 2 of Algorithm
MULTIMODULAR-FOR-EXTENSION-RING, p. 15). Charged `ql` of the bit size of the coefficients, of `M`,
of `r'`, of the intermediate value and of the result. -/
def evalAtModC (cs : List ℕ) (M r' : ℕ) : Timed ℕ :=
  let s := (cs.mapIdx (fun j c => c * M ^ j)).sum
  ⟨s % r', ql (lsize cs + bits M + bits r' + bits s + bits (s % r'))⟩

/-- The `K` lowest base-`M` digits `⌊β / M^j⌋ mod M`, `j < K`, of `β` (radix conversion, Step 4 of
Algorithm MULTIMODULAR-FOR-EXTENSION-RING, p. 15; Figure 1). -/
def radixC (β M K : ℕ) : Timed (List ℕ) :=
  let ds := List.ofFn (fun j : Fin K => β / M ^ (j : ℕ) % M)
  ⟨ds, ql (bits β + bits M + K + lsize ds)⟩

/-- Addition in `𝔽_p` (Figure 1 arithmetic), charged `ql (3 · bits p)`. -/
def fpAddC {p : ℕ} (a b : ZMod p) : Timed (ZMod p) := ⟨a + b, ql (3 * bits p)⟩

/-- Bit size of a list of residues modulo `p`. -/
def zsize {p : ℕ} (l : List (ZMod p)) : ℕ := lsize (l.map ZMod.val)

/-- **Fast univariate multipoint evaluation over all of `𝔽_p`** (Figure 1 "Evaluation"; proof of
Theorem 4.1, p. 12): given the coefficient list `g = [g_0, …, g_{p-1}]` of a univariate polynomial,
return `[g(0), g(1), …, g(p-1)]`. Charged `ql` of the bit size of input and output. -/
def uniEvalAllC (p : ℕ) (g : List (ZMod p)) : Timed (List (ZMod p)) :=
  let res := (List.range p).map (fun a => (g.mapIdx (fun j gj => gj * ((a : ZMod p)) ^ j)).sum)
  ⟨res, ql (zsize g + zsize res + bits p)⟩

end KUMultimodular


