-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.finite_integralClosure_sections_of_isIso_stalkMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/014f8b3f-a649-516e-b5be-383724f94b6f

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_CurveModel_apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
import Theorems.Thm_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen
import Theorems.Thm_AlgebraicCurve_CurveModel_isFinite_of_isIso_stalkMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_finite_integralClosure_sections_of_isIso_stalkMap

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve

noncomputable section

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C] [IsProper c]
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase)
    (hbir : IsIso (ν.stalkMap (genericPoint M.C)))
    (U : C.Opens) (hUaff : IsAffineOpen U) [Nonempty U] :
    Module.Finite Γ(C, U) ↥(integralClosure Γ(C, U) C.functionField) := by
  haveI : IsFinite ν := AlgebraicCurve.CurveModel.isFinite_of_isIso_stalkMap k c M ν hν hbir

  obtain ⟨hgen, -⟩ :=
    AlgebraicCurve.CurveModel.apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
      k c M ν hν hbir
  have hηV : genericPoint M.C ∈ ν ⁻¹ᵁ U := by
    show ν.base (genericPoint M.C) ∈ U
    rw [hgen]
    exact ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  haveI hne : Nonempty (ν ⁻¹ᵁ U) := ⟨⟨genericPoint M.C, hηV⟩⟩
  letI algV : Algebra Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField := (M.C.germToFunctionField (ν ⁻¹ᵁ U)).hom.toAlgebra
  have hVaff : IsAffineOpen (ν ⁻¹ᵁ U) := hUaff.preimage ν

  let φ : Γ(C, U) →+* Γ(M.C, ν ⁻¹ᵁ U) := (ν.app U).hom
  letI algφ : Algebra Γ(C, U) Γ(M.C, ν ⁻¹ᵁ U) := φ.toAlgebra
  haveI hfin : Module.Finite Γ(C, U) Γ(M.C, ν ⁻¹ᵁ U) := IsFinite.finite_app ν U hUaff

  let θ : C.functionField ≃+* M.C.functionField :=
    ((C.presheaf.stalkCongr (.of_eq hgen.symm)) ≪≫ asIso (ν.stalkMap (genericPoint M.C))).commRingCatIsoToRingEquiv
  have hθ : ∀ s : Γ(C, U),
      θ (algebraMap Γ(C, U) C.functionField s) = algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField (φ s) := by
    intro s
    change ν.stalkMap (genericPoint M.C)
        (C.presheaf.stalkSpecializes (Inseparable.of_eq hgen.symm).ge
          (C.presheaf.germ U (genericPoint C)
            (((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)) s)) =
      M.C.presheaf.germ (ν ⁻¹ᵁ U) (genericPoint M.C) hηV (φ s)
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]
  have hcomp : (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField).comp φ =
      θ.toRingHom.comp (algebraMap Γ(C, U) C.functionField) :=
    RingHom.ext fun s => (hθ s).symm

  let ψ : Γ(M.C, ν ⁻¹ᵁ U) →ₐ[Γ(C, U)] C.functionField :=
    { toRingHom := θ.symm.toRingHom.comp (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField)
      commutes' := fun s => by
        change θ.symm (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField (φ s)) = _
        rw [← hθ, RingEquiv.symm_apply_apply] }

  have h1 : ∀ b, IsIntegral Γ(C, U) (ψ b) := fun b => (Algebra.IsIntegral.isIntegral b).map ψ

  have h2 : ∀ x : C.functionField, IsIntegral Γ(C, U) x → x ∈ ψ.range := by
    intro x hx
    have hx' : IsIntegral Γ(M.C, ν ⁻¹ᵁ U) (θ x) := hx.map_of_comp_eq φ θ.toRingHom hcomp
    have hmem : θ x ∈ (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField).range := by
      letI := (AlgebraicCurve.baseToFunctionField M.toBase).toAlgebra
      have hrange := AlgebraicCurve.range_algebraMap_functionField_eq_iInf_of_isAffineOpen
        M.toBase (ν ⁻¹ᵁ U) hVaff
      rw [hrange]
      simp only [Subring.mem_iInf]
      intro v hv
      have hle : (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField).range ≤ v.toValuationSubring.toSubring := by
        rw [hrange]; exact iInf₂_le v hv

      let ρ : Γ(M.C, ν ⁻¹ᵁ U) →+* ↥v.toValuationSubring :=
        (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField).codRestrict v.toValuationSubring.toSubring
          fun b => hle ⟨b, rfl⟩
      have hρ : (algebraMap ↥v.toValuationSubring M.C.functionField).comp ρ =
          (RingHom.id M.C.functionField).comp (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField) :=
        RingHom.ext fun _ => rfl
      have hxv : IsIntegral ↥v.toValuationSubring (θ x) := hx'.map_of_comp_eq ρ (RingHom.id M.C.functionField) hρ
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := M.C.functionField)).mp hxv
      rw [← hy]
      exact y.2
    obtain ⟨b, hb⟩ := hmem
    refine ⟨b, ?_⟩
    change θ.symm (algebraMap Γ(M.C, ν ⁻¹ᵁ U) M.C.functionField b) = x
    rw [hb, RingEquiv.symm_apply_apply]

  have heq : Subalgebra.toSubmodule (integralClosure Γ(C, U) C.functionField) = LinearMap.range ψ.toLinearMap := by
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := h2 x hx
      exact ⟨b, hb⟩
    · rintro ⟨b, rfl⟩
      exact h1 b
  have hfr : Module.Finite Γ(C, U) ↥(LinearMap.range ψ.toLinearMap) := Module.Finite.range ψ.toLinearMap
  rw [← heq] at hfr
  exact hfr

end

#print axioms solution

end S_AlgebraicCurve_CurveModel_finite_integralClosure_sections_of_isIso_stalkMap
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_finite_integralClosure_sections_of_isIso_stalkMap (solution)
