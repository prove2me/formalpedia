-- Prove2me | Definitions.Def_ProcessingNetworks_CTMCFoster_uniformizedPMF
-- name    : ProcessingNetworks_CTMCFoster_uniformizedPMF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:47.484299+00:00
-- url     : https://prove2.me/theorems/e734cfa4-cb71-41e6-bb12-b34f710ad2d9
-- title:
--   The uniformized transition matrix $P$ of (D.30)
-- statement:
--   Let $\Lambda$ be a generator matrix on a countable set $\mathscr S$ with exit rates $\lambda(i)=-\Lambda_{ii}>0$, and let $\eta\ge\sup_{i}\lambda(i)$. The matrix
--
--   $$
--   P_{ij}=\begin{cases}\Lambda_{ij}/\eta, & i\ne j,\\ 1-\lambda(i)/\eta, & i=j,\end{cases}
--   $$
--
--   is stochastic. It is the transition matrix of the discrete-time chain $Z$ in the uniformization representation $X(t)=Z_{N(t)}$ of the continuous-time chain, with $N$ an independent Poisson process of rate $\eta$. Unlike the jump matrix, $P$ may have positive diagonal entries.
--
--   **Formalization Note** The hypothesis $\eta\ge\sup_i\lambda(i)$ is that $\eta$ bounds every $\lambda(i)$; positivity of $\eta$ then follows from $\lambda(i)>0$ at the state whose row is being formed. Stochasticity is the auxiliary lemma `uniformized_hasSum_ofReal`.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix D, §D.7, eq. (D.30), p.296 (PDF 312), and the sentence opening p.297 (PDF 313)

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain

namespace ProcessingNetworks.CTMCFoster

open MatrixAnalytic.ProductForm
open scoped ENNReal

/-- The entries of (D.30) form a probability vector in each row. Auxiliary fact behind
`uniformizedPMF`. -/
theorem uniformized_hasSum_ofReal {S : Type*} [Countable S] [DecidableEq S] {Λ : S → S → ℝ}
    (hΛ : IsGeneratorC Λ) {η : ℝ} (hle : ∀ i, holdRate Λ i ≤ η) (i : S) :
    HasSum (fun j => ENNReal.ofReal (if j = i then 1 - holdRate Λ i / η else Λ i j / η)) 1 := by
  have hrate : 0 < holdRate Λ i := neg_pos.mpr (hΛ.2.1 i)
  have hη : 0 < η := hrate.trans_le (hle i)
  have hnn : ∀ j, 0 ≤ (if j = i then 1 - holdRate Λ i / η else Λ i j / η) := by
    intro j
    split_ifs with h
    · exact sub_nonneg.mpr ((div_le_one hη).mpr (hle i))
    · exact div_nonneg (hΛ.1 i j (Ne.symm h)) hη.le
  have hrow : HasSum (fun j => Λ i j / η + (if j = i then 1 else 0)) (0 / η + 1) :=
    ((hΛ.2.2 i).div_const η).add (hasSum_ite_eq i (1 : ℝ))
  rw [zero_div, zero_add] at hrow
  have hsum' : HasSum (fun j => if j = i then 1 - holdRate Λ i / η else Λ i j / η) 1 := by
    convert hrow using 2 with j
    by_cases hj : j = i
    · subst hj
      simp only [if_true]
      unfold holdRate
      rw [neg_div]
      ring
    · simp only [hj, if_false, add_zero]
  have hsum : ∑' j, ENNReal.ofReal (if j = i then 1 - holdRate Λ i / η else Λ i j / η) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum'.summable, hsum'.tsum_eq, ENNReal.ofReal_one]
  exact hsum ▸ ENNReal.summable.hasSum

/-- The stochastic matrix `P` of the uniformization representation (D.30), for `η ≥ sup_i λ(i)`:
`P i j = Λ i j / η` for `i ≠ j` and `P i i = 1 - λ(i) / η`. The statement "`P` is a stochastic
matrix on `S`" of p.297 is the fact `uniformized_hasSum_ofReal`.

Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix D,
§D.7, eq. (D.30), p.296 (PDF 312).

**Formalization Note** `η ≥ sup_i λ(i)` is the hypothesis that `η` bounds every `λ(i)`. Positivity
of `η` needs no hypothesis: each row of `P` is taken at a state `i`, and `0 < λ(i) ≤ η`. -/
noncomputable def uniformizedPMF {S : Type*} [Countable S] [DecidableEq S] {Λ : S → S → ℝ}
    (hΛ : IsGeneratorC Λ) {η : ℝ} (hle : ∀ i, holdRate Λ i ≤ η) (i : S) : PMF S :=
  ⟨fun j => ENNReal.ofReal (if j = i then 1 - holdRate Λ i / η else Λ i j / η),
    uniformized_hasSum_ofReal hΛ hle i⟩

end ProcessingNetworks.CTMCFoster


