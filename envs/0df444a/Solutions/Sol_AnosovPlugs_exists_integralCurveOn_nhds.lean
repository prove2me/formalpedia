-- Prove2me | solution 1 for AnosovPlugs.exists_integralCurveOn_nhds
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T19:13:18.675341+00:00
-- url     : https://prove2.me/submissions/0c58a11c-dcc3-4567-8b5c-c58572236b93

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_exists_localFlow_of_isInteriorPoint
import Theorems.Thm_AnosovPlugs_exists_integralCurveOn_nhds_of_localFlow

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X) (γ : ℝ → M) (t : ℝ)
    (hγ : IsMIntegralCurveOn γ X (uIcc 0 t)) (hint : ∀ s ∈ uIcc 0 t, I3.IsInteriorPoint (γ s)) :
    ∀ᶠ y in 𝓝 (γ 0), ∃ γ' : ℝ → M, γ' 0 = y ∧ IsMIntegralCurveOn γ' X (uIcc 0 t) ∧
      ∀ s ∈ uIcc 0 t, I3.IsInteriorPoint (γ' s) := by
  exact exists_integralCurveOn_nhds_of_localFlow X
    (fun x₀ hx₀ => exists_localFlow_of_isInteriorPoint X hX x₀ hx₀) γ t hγ hint
