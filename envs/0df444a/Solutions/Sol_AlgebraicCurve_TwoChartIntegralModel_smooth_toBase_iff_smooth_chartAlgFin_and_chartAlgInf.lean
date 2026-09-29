-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.smooth_toBase_iff_smooth_chartAlgFin_and_chartAlgInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/200094ad-3bb7-5909-8f36-aee1dc87bfdb

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_smooth_toBase_iff_smooth_chartAlgFin_and_chartAlgInf

set_option autoImplicit false

noncomputable section

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_smooth_toBase_iff_smooth_chartAlgFin_and_chartAlgInf.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel.chartAlgFin TwoChartIntegralModel.chartAlgInf TwoChartIntegralModel TwoChartIntegralModel.isOpenImmersion_ιFin TwoChartIntegralModel.isOpenImmersion_ιInf TwoChartIntegralModel.toBase"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlgFin chartAlgInf XFin XInf ιFin ιInf isOpenImmersion_ιFin isOpenImmersion_ιInf toBase ιFin_toBase ιInf_toBase mem_range_ιFin_or_mem_range_ιInf"
namespace SmoothChartsAux
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

def openCover₂ : (AlgebraicCurve.TwoChartIntegralModel R F j).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b => bif b then XFin R F j else XInf R F j)
    (fun b => match b with
      | true => ιFin R F j
      | false => ιInf R F j)
    (by
      intro x
      rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, y, hy⟩)
    (by
      rintro (_ | _)
      · exact TwoChartIntegralModel.isOpenImmersion_ιInf R F j
      · exact TwoChartIntegralModel.isOpenImmersion_ιFin R F j)

theorem smooth_spec_algebraMap_iff (A : Type u) [CommRing A] [Algebra R A] :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔ Algebra.Smooth R A := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom, RingHom.smooth_algebraMap]

end AlgebraicCurve.TwoChartIntegralModel.SmoothChartsAux

open _root_.AlgebraicCurve.TwoChartIntegralModel _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_smooth_toBase_iff_smooth_chartAlgFin_and_chartAlgInf.AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve.TwoChartIntegralModel.SmoothChartsAux in
theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    Smooth (TwoChartIntegralModel.toBase R F j) ↔
      Algebra.Smooth R ↥(TwoChartIntegralModel.chartAlgFin R F j) ∧
        Algebra.Smooth R ↥(TwoChartIntegralModel.chartAlgInf R F j) := by
  constructor
  · intro h
    have h1 : Smooth (ιFin R F j ≫ toBase R F j) := inferInstance
    have h2 : Smooth (ιInf R F j ≫ toBase R F j) := inferInstance
    rw [ιFin_toBase, smooth_spec_algebraMap_iff] at h1
    rw [ιInf_toBase, smooth_spec_algebraMap_iff] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (openCover₂ R F j) ?_
    rintro (_ | _)
    · change Smooth (ιInf R F j ≫ toBase R F j)
      rw [ιInf_toBase, smooth_spec_algebraMap_iff]
      exact h2
    · change Smooth (ιFin R F j ≫ toBase R F j)
      rw [ιFin_toBase, smooth_spec_algebraMap_iff]
      exact h1

end

end S_AlgebraicCurve_TwoChartIntegralModel_smooth_toBase_iff_smooth_chartAlgFin_and_chartAlgInf
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_smooth_toBase_iff_smooth_chartAlgFin_and_chartAlgInf (solution)
