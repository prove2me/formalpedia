-- Prove2me | solution 1 for AnosovPlugs.exists_comparable_metric
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T19:13:18.5365+00:00
-- url     : https://prove2.me/submissions/6aec9150-51b1-4836-bb5b-98796045d1c1

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_exists_riemannianMetric3
import Theorems.Thm_AnosovPlugs_comparable_of_metrics

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [T2Space M] [CompactSpace M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    [T2Space N] [CompactSpace N]
    (i : M → N) (hi : ContMDiff I3 I3 1 i) (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (g : RiemannianMetric3 M) :
    ∃ g' : RiemannianMetric3 N, ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (x : M) (v : TangentSpace I3 x),
        c₁ * g.norm x v ≤ g'.norm (i x) (mfderiv I3 I3 i x v) ∧
        g'.norm (i x) (mfderiv I3 I3 i x v) ≤ c₂ * g.norm x v := by
  obtain ⟨g'⟩ := exists_riemannianMetric3 (N := N)
  exact ⟨g', comparable_of_metrics i hi hinj g g'⟩
