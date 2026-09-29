-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5698b1ec-703e-54c1-9870-3264cbf70669

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace FFIsoL0c

theorem isIso_stalkSpecializes_of_eq {X : TopCat.{u}} (P : TopCat.Presheaf CommRingCat.{u} X)
    {x y : X} (e : x = y) (h : x ⤳ y) : IsIso (P.stalkSpecializes h) := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

theorem eq_genericPoint_of_isField {C : Scheme.{u}} [IsIntegral C] (x : C)
    (hfield : IsField (C.presheaf.stalk x)) : x = genericPoint C := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := C) (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  letI := C.presheaf.algebra_section_stalk (⟨_, hxU⟩ : U)
  haveI := hU.isLocalization_stalk ⟨_, hxU⟩
  have hbot : (hU.primeIdealOf ⟨_, hxU⟩).asIdeal = ⊥ := by
    rw [← Ideal.map_eq_bot_iff_of_injective (IsLocalization.injective (C.presheaf.stalk x)
      (hU.primeIdealOf ⟨_, hxU⟩).asIdeal.primeCompl_le_nonZeroDivisors),
      IsLocalization.AtPrime.map_eq_maximalIdeal (hU.primeIdealOf ⟨_, hxU⟩).asIdeal,
      ← IsLocalRing.isField_iff_maximalIdeal_eq]
    exact hfield
  have h1 : hU.primeIdealOf ⟨_, hxU⟩ = hU.primeIdealOf ⟨genericPoint C,
      ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using (inferInstance : Nonempty U))⟩ := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    ext1
    exact hbot
  have h2 := congr(hU.fromSpec $h1)
  rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h2

end FFIsoL0c

open FFIsoL0c in

theorem solution
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C]
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase)
    (hbir : IsIso (ν.stalkMap (genericPoint M.C))) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ν.base (genericPoint M.C) = genericPoint C ∧ Nonempty (F ≃ₐ[k] C.functionField) := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  have hx : ν.base (genericPoint M.C) = genericPoint C := by
    apply eq_genericPoint_of_isField
    exact MulEquiv.isField (Field.toIsField M.C.functionField)
      (asIso (ν.stalkMap (genericPoint M.C))).commRingCatIsoToRingEquiv.toMulEquiv
  refine ⟨hx, ⟨?_⟩⟩
  have hsp : genericPoint C ⤳ ν.base (genericPoint M.C) := (genericPoint_spec C).specializes trivial
  haveI := isIso_stalkSpecializes_of_eq C.presheaf hx.symm hsp
  let e : F ≃+* C.functionField :=
    M.ffEquiv.trans (((asIso (ν.stalkMap (genericPoint M.C))).symm ≪≫
      asIso (C.presheaf.stalkSpecializes hsp)).commRingCatIsoToRingEquiv)
  refine AlgEquiv.ofRingEquiv (f := e) fun a => ?_
  show C.presheaf.stalkSpecializes hsp (inv (ν.stalkMap (genericPoint M.C))
    (M.ffEquiv (algebraMap k F a))) = baseToFunctionField c a
  rw [M.ffEquiv_algebraMap]
  have h1 : baseToFunctionField M.toBase a = ν.stalkMap (genericPoint M.C)
      (C.presheaf.germ ⊤ (ν.base (genericPoint M.C)) trivial
        (c.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a))) := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    show (M.C.presheaf.germ ⊤ (genericPoint M.C) trivial)
      (M.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)) = _
    rw [← hν, Scheme.Hom.comp_appTop]
    rfl
  rw [h1, IsIso.hom_inv_id_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]
  rfl

#print axioms solution

end S_AlgebraicCurve_CurveModel_apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap (solution)
