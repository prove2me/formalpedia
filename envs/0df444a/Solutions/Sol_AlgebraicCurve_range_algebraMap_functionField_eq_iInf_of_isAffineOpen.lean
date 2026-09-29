-- Prove2me | solution 1 for AlgebraicCurve.range_algebraMap_functionField_eq_iInf_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/af10b7bf-3623-52c3-b8ed-018d65aa1f12

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (algebraMap Γ(C, U) C.functionField).range =
      ⨅ (v : AlgebraicCurve.Place K C.functionField)
        (_ : ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
          (algebraMap (C.presheaf.stalk x) C.functionField).range =
            v.toValuationSubring.toSubring),
        v.toValuationSubring.toSubring := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  rw [hU.range_algebraMap_functionField_eq_iInf]
  apply le_antisymm
  ·
    refine le_iInf₂ fun v hv => ?_
    obtain ⟨x, hxU, -, hrange⟩ := hv
    rw [← hrange]
    exact iInf₂_le x hxU
  ·
    refine le_iInf₂ fun x hxU => ?_
    by_cases hη : x = genericPoint C
    ·
      subst hη
      intro f _
      refine ⟨f, ?_⟩
      change (C.presheaf.stalkSpecializes (specializes_refl _)).hom f = f
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    · have hxcl : IsClosed ({x} : Set C) := isClosed_singleton_of_ne_genericPoint c x hη
      obtain ⟨v, hv⟩ := exists_place_range_stalk_eq c x hxcl
      rw [hv]
      exact iInf₂_le v ⟨x, hxU, hxcl, hv⟩

end S_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen
end P2MW
export P2MW.S_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen (solution)
