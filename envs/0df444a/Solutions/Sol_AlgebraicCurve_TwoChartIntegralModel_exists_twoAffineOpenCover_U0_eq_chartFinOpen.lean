-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_twoAffineOpenCover_U0_eq_chartFinOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d17c3ddc-faf9-5022-99d6-05c8b4696e63

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_twoAffineOpenCover_U0_eq_chartFinOpen

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_twoAffineOpenCover_U0_eq_chartFinOpen.AlgebraicCurve.TwoChartIntegralModel"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel TwoChartIntegralModel.isAffineOpen_chartFinOpen TwoChartIntegralModel.isAffineOpen_chartInfOpen TwoChartIntegralModel.twoChartCover"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "XFin XInf XMid fFin fInf ιFin ιInf glue_condition chartFinOpen chartInfOpen isAffineOpen_chartFinOpen isAffineOpen_chartInfOpen twoChartCover"
namespace CoverAux
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem ιFin_eq_ιInf_iff (x₀ : XFin R F j) (xi : XInf R F j) :
    (ιFin R F j).base x₀ = (ιInf R F j).base xi ↔
      ∃ w : XMid R F j, (fFin R F j).base w = x₀ ∧ (fInf R F j).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin R F j) (fInf R F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · rcases fi with _ | _
      rcases fj with _ | _
      exact ⟨w, h₁, h₂⟩
    · rcases fj with _ | _
    · rcases fi with _ | _
  · rintro ⟨w, rfl, rfl⟩
    change (fFin R F j ≫ ιFin R F j).base w = (fInf R F j ≫ ιInf R F j).base w
    rw [glue_condition]

theorem chartFinOpen_inf_chartInfOpen :
    chartFinOpen R F j ⊓ chartInfOpen R F j = (fFin R F j ≫ ιFin R F j).opensRange := by
  apply TopologicalSpace.Opens.ext
  rw [TopologicalSpace.Opens.coe_inf, chartFinOpen, chartInfOpen, Scheme.Hom.coe_opensRange,
    Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange]
  ext x
  constructor
  · rintro ⟨⟨x₀, rfl⟩, ⟨xi, hxi⟩⟩
    obtain ⟨w, hw, -⟩ := (ιFin_eq_ιInf_iff R F j x₀ xi).mp hxi.symm
    refine ⟨w, ?_⟩
    rw [Scheme.Hom.comp_apply]
    change (ιFin R F j).base ((fFin R F j).base w) = (ιFin R F j).base x₀
    rw [hw]
  · rintro ⟨w, rfl⟩
    refine ⟨⟨(fFin R F j).base w, ?_⟩, ⟨(fInf R F j).base w, ?_⟩⟩
    · rw [Scheme.Hom.comp_apply]
    · change (ιInf R F j) ((fInf R F j) w) = (fFin R F j ≫ ιFin R F j) w
      rw [glue_condition, Scheme.Hom.comp_apply]

end AlgebraicCurve.TwoChartIntegralModel.CoverAux

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    ∃ 𝒱 : (AlgebraicCurve.TwoChartIntegralModel R F j).TwoAffineOpenCover,
      𝒱.U0 = chartFinOpen R F j ∧ 𝒱.U1 = chartInfOpen R F j :=
  ⟨{ U0 := chartFinOpen R F j
     U1 := chartInfOpen R F j
     isAffineOpen_U0 := AlgebraicCurve.TwoChartIntegralModel.isAffineOpen_chartFinOpen R F j
     isAffineOpen_U1 := AlgebraicCurve.TwoChartIntegralModel.isAffineOpen_chartInfOpen R F j
     sup_eq_top := AlgebraicCurve.TwoChartIntegralModel.twoChartCover R F j
     isAffineOpen_inf := by
       rw [AlgebraicCurve.TwoChartIntegralModel.CoverAux.chartFinOpen_inf_chartInfOpen]
       exact isAffineOpen_opensRange _ }, rfl, rfl⟩

end S_AlgebraicCurve_TwoChartIntegralModel_exists_twoAffineOpenCover_U0_eq_chartFinOpen
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_twoAffineOpenCover_U0_eq_chartFinOpen (solution)
