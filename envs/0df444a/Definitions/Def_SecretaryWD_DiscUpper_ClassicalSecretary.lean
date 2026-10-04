-- Prove2me | Definitions.Def_SecretaryWD_DiscUpper_ClassicalSecretary
-- name    : SecretaryWD_DiscUpper_ClassicalSecretary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:14:07.891111+00:00
-- url     : https://prove2.me/theorems/dae6693e-3584-46eb-a63d-8e252f7d1599
-- title:
--   Uniform arrival order, tie-break order, and the classical secretary rule
-- statement:
--   This file fixes three objects shared by the whole mission.
--
--   **Uniform arrival order.** For $n$ elements $\{0,\dots,n-1\}$, an arrival order is a permutation $\pi$ of $\{0,\dots,n-1\}$, read as *time $\mapsto$ element*: element $\pi(t)$ arrives at time $t$. The expectation of a quantity $f(\pi)$ over the uniformly random order is the finite average
--   $$\mathbb E_\pi[f(\pi)] = \frac{1}{n!}\sum_{\pi} f(\pi).$$
--
--   **Tie-break order.** Given values $v(e)\in\mathbb R$, element $e$ ranks above element $e'$ when $v(e)>v(e')$, or $v(e)=v(e')$ and $e<e'$. Equivalently, the pairs $(v(e), e)$ are compared lexicographically with the index order reversed. This is a strict total order on elements, so "the maximum" is always a single element even when values coincide.
--
--   **The classical secretary rule** (Section 2 of the paper). On $m$ arrivals whose ranks (in some linear order) are revealed one at a time, the rule observes the first $\lfloor m/e\rfloor$ arrivals without selecting any, and afterwards selects the first arrival that ranks strictly above every earlier arrival, the observed ones included. It may select nothing. Its output is the position of the selected arrival among the $m$ arrivals.
--
--   These are the building blocks of the discounted secretary algorithm of Theorem 4.4, which runs the classical rule on a subsequence of the arrivals.
--
--   **Formalization Note.** Positions and times are $0$-based: the paper's time $t=1,\dots,n$ is index $t-1$. The sample size is $\lfloor m/e\rfloor$ computed as `Nat.floor (m / Real.exp 1)`. The rule is stated for keys in an arbitrary linear order; the mission applies it to the tie-break keys $(v(e), e)$.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), pp. 3-4, Section 2 (random order; classical secretary algorithm)

import Mathlib

namespace SecretaryWD.DiscUpper

/-- The average of `f` over the uniformly random arrival order: `(1/n!) · ∑_π f π`, where
`π : Equiv.Perm (Fin n)` is read as *time ↦ element*. -/
noncomputable def uniformAvg {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∑ π : Equiv.Perm (Fin n), f π

/-- The tie-break key of element `e` under values `v`: compare `(v e, e)` lexicographically,
larger value first and, among equal values, the **smaller index** first (hence `OrderDual`). -/
def tieKey {k : ℕ} (v : Fin k → ℝ) (e : Fin k) : Lex (ℝ × (Fin k)ᵒᵈ) :=
  toLex (v e, OrderDual.toDual e)

/-- The classical secretary rule (§2, p. 4) on `m` arrivals whose keys, in arrival order, are
`x 0, …, x (m-1)` in a linear order. It skips the first `⌊m / e⌋` arrivals, then selects the
first arrival `t` (index `t ≥ ⌊m/e⌋`) whose key is strictly larger than the key of every earlier
arrival, the skipped ones included. It returns the index of the selected arrival, or `none`. -/
noncomputable def classicalSecretary {α : Type*} [LinearOrder α] (m : ℕ) (x : Fin m → α) :
    Option (Fin m) :=
  (List.finRange m).find? fun t =>
    decide (Nat.floor ((m : ℝ) / Real.exp 1) ≤ t.val ∧ ∀ s : Fin m, s < t → x s < x t)

end SecretaryWD.DiscUpper


