-- Prove2me | Definitions.Def_RandModSubsetSum_Types
-- name    : RandModSubsetSum_Types
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:18.619716+00:00
-- url     : https://prove2.me/theorems/54abba9c-080c-4f32-938f-c26d62bf5e50
-- title:
--   Entropy in bits, type classes, the m-type approximation $\lfloor P\rceil_m$ and image entropies
-- statement:
--   This module fixes the information-theoretic vocabulary of the paper (§2). All logarithms are to base two.
--
--   1. **Entropy.** For a distribution $P$ on a finite alphabet $A$, $H(P)=-\sum_{a\in A}P(a)\log_2 P(a)$ with $0\log 0=0$ (Definition 2.6). It is defined over a finite set of symbols, so integer symbols can be used directly.
--   2. **m-types and type classes.** $P$ is an *m-type* if it is a probability distribution with $mP(a)\in\mathbb Z_{\ge0}$ for every $a$; its *type class* is $T_m(P)=\{x\in A^m:\ \#\{k:x_k=a\}=mP(a)\ \forall a\}$ (Definitions 2.1–2.2).
--   3. **Deterministic m-type approximation** (Definition 2.2). For a distribution $P$ on an ordered finite alphabet, put $c_a=\lfloor mP(a)\rfloor$, $r_a=mP(a)-c_a$, $L=m-\sum_a c_a$, and let $S$ be the $L$ symbols with the largest remainders, ties broken by the fixed order. Then
--   $$\lfloor P\rceil_m(a)=\frac{c_a+\mathbf 1\{a\in S\}}{m}.$$
--   The module provides both the integer counts $c_a+\mathbf 1\{a\in S\}$ and the normalized type.
--   4. **Image entropy** $H(f(P))$ of the image distribution $f(P)(z)=\sum_{f(a)=z}P(a)$ (Definition 2.5), **total variation** $\|P-Q\|_{TV}=\tfrac12\sum_a|P(a)-Q(a)|$, and the **multinomial coefficient** $N!/\prod_i c_i!$.
--
--   These are used for the stratum sizes, the exact types of the representation family, the observation entropies and the type-class counts of the analysis.
--
--   **Formalization Note** The set $S$ is described by ranks: $a\in S$ iff fewer than $L$ symbols come strictly before $a$ in the order "larger remainder first, then smaller key". "Breaking ties according to the fixed order" is read as preferring the earlier symbol (the paper's "ties by increasing $r$", "by increasing $h$"). The entropy is not the published `WildeQIT.entropy`, which is defined on a `FinDist` over a finite type; here alphabets are finite sets of integers.
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Definitions 2.1–2.6, pp. 9–10; Appendix A, p. 55

import Mathlib

open scoped BigOperators

namespace RandModSubsetSum

/-- Entropy in bits of a (nonnegative) function `P` on a finite support set `s`:
`H(P) = −Σ_{a ∈ s} P(a) log₂ P(a)`, with `0 log 0 = 0` (Definition 2.6).
Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Definition 2.6, p. 10.

**Formalization Note.** `Real.negMulLog t = −t log t` (natural log) vanishes at `0`; dividing by
`log 2` gives bits ("All logarithms are to base two", p. 3). The alphabet is a `Finset`, so integer
symbols (`ℤ`) can be used directly; the sum is over the whole alphabet, and symbols of probability
zero contribute `0`. -/
noncomputable def entropyOn {α : Type*} (s : Finset α) (P : α → ℝ) : ℝ :=
  ∑ a ∈ s, Real.negMulLog (P a) / Real.log 2

/-- Entropy in bits of a distribution on a finite type (Definition 2.6, p. 10). -/
noncomputable def entropy {α : Type*} [Fintype α] (P : α → ℝ) : ℝ :=
  entropyOn Finset.univ P

/-- `P` is an **m-type** (an exact type for length `m`) on a finite alphabet (Definition 2.2,
p. 9): a probability distribution with `m P(a) ∈ ℤ_{≥0}` for every symbol `a`. -/
def IsMType {α : Type*} [Fintype α] (m : ℕ) (P : α → ℝ) : Prop :=
  (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1 ∧ ∀ a, ∃ k : ℕ, (m : ℝ) * P a = k

open Classical in
/-- The **type class** `T_m(P) = {x ∈ Aᵐ : P̂_x = P}` (Definition 2.1, p. 9): the words of
length `m` in which every symbol `a` occurs exactly `m P(a)` times.

**Formalization Note.** The condition is stated on counts, `#{k : x_k = a} = m P(a)`, which equals
`P̂_x = P` for `m ≥ 1`. -/
noncomputable def typeClass {α : Type*} [Fintype α] (m : ℕ) (P : α → ℝ) : Finset (Fin m → α) :=
  Finset.univ.filter
    (fun x => ∀ a, ((Finset.univ.filter (fun k => x k = a)).card : ℝ) = (m : ℝ) * P a)

open Classical in
/-- Integer counts of the **deterministic m-type approximation** `⌊P⌉_m` (Definition 2.2, p. 9),
on the alphabet `s` with the fixed order given by `key` (smaller key first):
put `c_a = ⌊m P(a)⌋`, `r_a = m P(a) − c_a`, `L = m − Σ_a c_a`; let `S` consist of the `L` symbols with
the largest remainders `r_a`, ties broken by the fixed order; then the count of `a` is
`c_a + 1{a ∈ S}`. Symbols outside `s` get count `0`.

**Formalization Note.** `S` is described by ranks: the rank of `a` is the number of symbols of `s`
strictly ahead of `a` in the order "larger remainder first, then smaller key"; `a ∈ S` iff its rank
is `< L`. For an injective `key` this is exactly the set of the first `L` symbols, and `S = ∅` when
`L = 0`. "Breaking ties according to the fixed order" is read as "the earlier symbol is preferred"
(§3.1: "ties by increasing r"; §4.3: "breaking ties by increasing h"). `⌊·⌋` is `Nat.floor`, which
equals the integer floor on the nonnegative values `m P(a)` of a distribution. -/
noncomputable def roundCount {α κ : Type*} [LinearOrder κ] (s : Finset α) (key : α → κ)
    (P : α → ℝ) (m : ℕ) (a : α) : ℕ :=
  let c : α → ℕ := fun b => ⌊(m : ℝ) * P b⌋₊
  let rem : α → ℝ := fun b => (m : ℝ) * P b - (c b : ℝ)
  let L : ℤ := (m : ℤ) - ∑ b ∈ s, (c b : ℤ)
  let rank : ℕ := (s.filter (fun b => rem a < rem b ∨ (rem b = rem a ∧ key b < key a))).card
  if a ∈ s then c a + (if (rank : ℤ) < L then 1 else 0) else 0

/-- The deterministic m-type approximation `⌊P⌉_m(a) = (c_a + 1{a∈S})/m` (Definition 2.2, p. 9). -/
noncomputable def typeRound {α κ : Type*} [LinearOrder κ] (s : Finset α) (key : α → κ)
    (P : α → ℝ) (m : ℕ) (a : α) : ℝ :=
  (roundCount s key P m a : ℝ) / m

open Classical in
/-- Entropy in bits of the **image distribution** `f(P)(z) = Σ_{a : f(a) = z} P(a)`
(Definition 2.5, p. 10) of a distribution `P` supported on the finite set `s`. -/
noncomputable def imageEntropy {α β : Type*} (s : Finset α) (P : α → ℝ) (f : α → β) : ℝ :=
  ∑ z ∈ s.image f, Real.negMulLog (∑ a ∈ s.filter (fun a => f a = z), P a) / Real.log 2

/-- Total variation distance `‖P − Q‖_TV = ½ Σ_a |P(a) − Q(a)|` of two distributions on a finite
type (Appendix A, p. 55). -/
noncomputable def tvDist {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ :=
  (1 / 2) * ∑ a, |P a - Q a|

/-- The multinomial coefficient `N! / Π_i (c_i)!` as a real number (the size of a type class with
counts `c`, p. 27). -/
noncomputable def multinom {ι : Type*} [Fintype ι] (N : ℕ) (c : ι → ℕ) : ℝ :=
  (N.factorial : ℝ) / ∏ i, ((c i).factorial : ℝ)

end RandModSubsetSum


