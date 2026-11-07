-- Prove2me | Definitions.Def_RobustFcstAgg_gaussInst
-- name    : RobustFcstAgg_gaussInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:06.922999+00:00
-- url     : https://prove2.me/theorems/8799aa0c-db9f-4f5f-9c85-13a94d6e682f
-- title:
--   Gaussian instance $\mathcal D_\lambda$
-- statement:
--   Let $\Delta=\{\lambda\ge0:\sum_{\emptyset\ne T}\lambda_T=1\}$ be the set of probability vectors over nonempty subsets of $[n]$. For $\lambda\in\Delta$, the **Gaussian instance** $\mathcal D_\lambda$ is the instance under which the independent signals satisfy $X_T\sim N(0,\lambda_T)$ for each $\emptyset\ne T\subseteq[n]$.
--
--   A coordinate $\lambda_T=0$ gives a point mass at $0$, so the Gaussian vector may be singular. These instances are the hard ones in the lower bound.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 4.3.1, p.14

import Mathlib
import Definitions.Def_RobustFcstAgg_InfoStruct
open MeasureTheory
open ProbabilityTheory

namespace RobustFcstAgg

/-- **Gaussian instance `D_λ`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 4.3.1, p.14: "Let `Δ := {λ ≥ 0 : Σ_{∅≠T} λ_T = 1}` ... `X_T ∼ N(0, λ_T)` for each
`∅ ≠ T ⊆ [n]`".

**Formalization Note.** `Δ` is `stdSimplex ℝ (Subs n)`. A coordinate `λ_T = 0` gives the Dirac at `0`
(`gaussianReal 0 0`), so the Gaussian vector may be singular. -/
noncomputable def gaussInst {n : ℕ} (lam : stdSimplex ℝ (Subs n)) : InfoStruct n where
  law := fun T => gaussianReal 0 (lam.1 T).toNNReal
  isProb := fun _ => inferInstance
  memLp := fun _ => memLp_id_gaussianReal 2
  mean_zero := fun _ => integral_id_gaussianReal
  nondeg := by
    obtain ⟨hnn, hsum⟩ := lam.2
    obtain ⟨T, hT⟩ : ∃ T, 0 < lam.1 T := by
      by_contra h
      push Not at h
      have : ∑ T, lam.1 T ≤ 0 := Finset.sum_nonpos fun T _ => h T
      linarith
    refine ⟨T, ?_⟩
    have h1 : ∫ x, x ^ 2 ∂gaussianReal 0 (lam.1 T).toNNReal = (lam.1 T).toNNReal := by
      have hv := variance_fun_id_gaussianReal (μ := 0) (v := (lam.1 T).toNNReal)
      rw [variance_of_integral_eq_zero (by fun_prop) (by simp)] at hv
      simpa using hv
    rw [h1, Real.coe_toNNReal _ (hnn T)]
    exact hT

end RobustFcstAgg


