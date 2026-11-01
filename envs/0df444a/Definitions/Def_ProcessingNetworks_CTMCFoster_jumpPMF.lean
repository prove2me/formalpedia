-- Prove2me | Definitions.Def_ProcessingNetworks_CTMCFoster_jumpPMF
-- name    : ProcessingNetworks_CTMCFoster_jumpPMF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:45.220108+00:00
-- url     : https://prove2.me/theorems/e06a1827-221a-4b7b-8791-de79c866f79a
-- title:
--   The jump matrix $G$ of a generator (D.3) as a transition kernel
-- statement:
--   Let $\Lambda=(\Lambda_{ij})$ be a generator matrix on a countable set $\mathscr S$: its off-diagonal entries are non-negative, each row sums to zero, and the exit rates $\lambda(i)=-\Lambda_{ii}$ are strictly positive. The **jump matrix** $G$ of $\Lambda$ is
--
--   $$
--   G_{ij}=\begin{cases}\Lambda_{ij}/\lambda(i), & j\ne i,\\ 0, & j=i.\end{cases}
--   $$
--
--   Each row of $G$ is a probability vector, so $G$ is the transition matrix of a discrete-time chain, the jump chain of the continuous-time chain with generator $\Lambda$. This item packages $G$ as a map from states to probability mass functions, the form taken by the recurrence and stationarity predicates of the series.
--
--   **Formalization Note** The entries are those of the platform function `jumpP`, and the generator conditions are the platform predicate `IsGeneratorC` (Definition D.1 with (D.2)); the row-sum property is proved in the auxiliary lemma `jumpP_hasSum_ofReal`.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix D, §D.1, eq. (D.3), p.287 (PDF 303)

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain

namespace ProcessingNetworks.CTMCFoster

open MatrixAnalytic.ProductForm
open scoped ENNReal

/-- The off-diagonal part of a row of a generator with (D.2), divided by the exit rate, sums to
one. Auxiliary fact behind `jumpPMF`. -/
theorem jumpP_hasSum_ofReal {S : Type*} [Countable S] [DecidableEq S] {Λ : S → S → ℝ}
    (hΛ : IsGeneratorC Λ) (i : S) :
    HasSum (fun j => ENNReal.ofReal (jumpP Λ i j)) 1 := by
  have hrate : 0 < holdRate Λ i := neg_pos.mpr (hΛ.2.1 i)
  have hnn : ∀ j, 0 ≤ jumpP Λ i j := by
    intro j
    unfold jumpP
    split_ifs with h
    · exact le_rfl
    · exact div_nonneg (hΛ.1 i j (Ne.symm h)) hrate.le
  have hrow : HasSum (fun j => Λ i j + (if j = i then holdRate Λ i else 0)) (0 + holdRate Λ i) :=
    (hΛ.2.2 i).add (hasSum_ite_eq i (holdRate Λ i))
  have hdiv : HasSum (fun j => jumpP Λ i j) 1 := by
    have h := hrow.div_const (holdRate Λ i)
    rw [zero_add, div_self hrate.ne'] at h
    have heq : (fun j => jumpP Λ i j) =
        fun j => (Λ i j + (if j = i then holdRate Λ i else 0)) / holdRate Λ i := by
      funext j
      unfold jumpP
      by_cases hj : j = i
      · subst hj
        simp only [if_true]
        unfold holdRate
        rw [add_neg_cancel, zero_div]
      · simp only [hj, if_false, add_zero]
    rw [heq]
    exact h
  have hsum : ∑' j, ENNReal.ofReal (jumpP Λ i j) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hdiv.summable, hdiv.tsum_eq, ENNReal.ofReal_one]
  exact hsum ▸ ENNReal.summable.hasSum

/-- The jump matrix `G` of (D.3) as a transition kernel: `G i j = Λ i j / λ(i)` for `j ≠ i` and
`G i i = 0`. That each row is a probability vector follows from Definition D.1 and (D.2).

Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix D,
§D.1, eq. (D.3), p.287 (PDF 303).

**Formalization Note** The entries are those of the platform definition `jumpP`; this declaration
only packages them as `S → PMF S`, the form taken by the published predicates of
`ProcessingNetworks.Stability`. -/
noncomputable def jumpPMF {S : Type*} [Countable S] [DecidableEq S] {Λ : S → S → ℝ}
    (hΛ : IsGeneratorC Λ) (i : S) : PMF S :=
  ⟨fun j => ENNReal.ofReal (jumpP Λ i j), jumpP_hasSum_ofReal hΛ i⟩

end ProcessingNetworks.CTMCFoster


