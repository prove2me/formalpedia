-- Prove2me | solution 1 for Algebra.FormallySmooth.isReduced_quotient_map_of_isMaximal_of_finitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1bef7212-5879-5b2a-8957-00509cd428f8

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallySmooth_isReduced_quotient_map_of_isMaximal_of_finitePresentation

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem solution
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FormallySmooth A B] [Algebra.FinitePresentation A B]
    (I : Ideal A) (hI : I.IsMaximal) :
    IsReduced (B ⧸ Ideal.map (algebraMap A B) I) := by
  haveI : I.IsMaximal := hI
  letI instK : Field (A ⧸ I) := Ideal.Quotient.field I
  have hs : Algebra.Smooth (A ⧸ I) (TensorProduct A (A ⧸ I) B) :=
    ⟨inferInstance, inferInstance⟩
  have hφ : (CommRingCat.ofHom (algebraMap (A ⧸ I) (TensorProduct A (A ⧸ I) B))).hom.Smooth := by
    rw [CommRingCat.hom_ofHom, RingHom.smooth_algebraMap]
    exact hs
  have hS : AlgebraicGeometry.Smooth
      (Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) (TensorProduct A (A ⧸ I) B)))) :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)).mpr hφ
  have hred : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (TensorProduct A (A ⧸ I) B))) :=
    AlgebraicGeometry.isReduced_of_smooth_of_field (K := A ⧸ I)
      (Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) (TensorProduct A (A ⧸ I) B))))
  have hC : _root_.IsReduced (TensorProduct A (A ⧸ I) B) :=
    (AlgebraicGeometry.affine_isReduced_iff (CommRingCat.of (TensorProduct A (A ⧸ I) B))).mp hred
  exact isReduced_of_injective (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I)
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).injective

end S_Algebra_FormallySmooth_isReduced_quotient_map_of_isMaximal_of_finitePresentation
end P2MW
export P2MW.S_Algebra_FormallySmooth_isReduced_quotient_map_of_isMaximal_of_finitePresentation (solution)
