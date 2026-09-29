-- Prove2me | solution 1 for AlgebraicGeometry.exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/eeefdd8d-9396-5f22-acd9-90fb2c62d336

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem solution
    {X Y Z : Scheme.{u}} (a : X ⟶ Z) (b : Y ⟶ Z) [IsAffineHom a] [IsAffineHom b]
    (U : Z.Opens) (hU : IsAffineOpen U)
    (hle₂ : (pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U) ≤ (pullback.snd a b) ⁻¹ᵁ (b ⁻¹ᵁ U)) :
    letI : Algebra Γ(Z, U) Γ(X, a ⁻¹ᵁ U) := (a.app U).hom.toAlgebra
    letI : Algebra Γ(Z, U) Γ(Y, b ⁻¹ᵁ U) := (b.app U).hom.toAlgebra
    IsAffineOpen ((pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U)) ∧
    ∃ τ : Γ(pullback a b, (pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U)) ≃+* Γ(X, a ⁻¹ᵁ U) ⊗[Γ(Z, U)] Γ(Y, b ⁻¹ᵁ U),
      (∀ s : Γ(X, a ⁻¹ᵁ U), τ (((pullback.fst a b).app (a ⁻¹ᵁ U)).hom s) = s ⊗ₜ 1) ∧
      (∀ s' : Γ(Y, b ⁻¹ᵁ U),
        τ (((pullback.snd a b).appLE (b ⁻¹ᵁ U) ((pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U)) hle₂).hom s') = 1 ⊗ₜ s')
  := by
  letI iA : Algebra Γ(Z, U) Γ(X, a ⁻¹ᵁ U) := (a.app U).hom.toAlgebra
  letI iB : Algebra Γ(Z, U) Γ(Y, b ⁻¹ᵁ U) := (b.app U).hom.toAlgebra
  have hUX : IsAffineOpen (a ⁻¹ᵁ U) := hU.preimage a
  have hUT : IsAffineOpen (b ⁻¹ᵁ U) := hU.preimage b
  haveI : IsAffineHom (pullback.fst a b) := MorphismProperty.pullback_fst _ _ inferInstance
  have hW : IsAffineOpen ((pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U)) := hUX.preimage _
  refine ⟨hW, ?_⟩
  have hsq := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback a b) (US := U) (UT := b ⁻¹ᵁ U)
    (UX := a ⁻¹ᵁ U) le_rfl le_rfl (UY := (pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U)) (inf_eq_left.mpr hle₂).symm
  haveI : IsAffine (a ⁻¹ᵁ U) := hUX
  haveI : IsAffine (b ⁻¹ᵁ U) := hUT
  haveI : IsAffine U := hU
  have hpo := isPushout_appTop_of_isPullback hsq
  have key : ∀ {S T : Scheme.{u}} (φ : S ⟶ T) (O : T.Opens) (V : S.Opens) (e : V ≤ φ ⁻¹ᵁ O),
      (φ.resLE O V e).appTop ≫ V.topIso.hom = O.topIso.hom ≫ φ.appLE O V e := by
    intro S T φ O V e
    change (φ.resLE O V e).app ⊤ ≫ V.topIso.hom = _
    rw [Scheme.Hom.resLE_app_top]
    ext x
    change V.topIso.hom.hom (V.topIso.inv.hom ((φ.appLE O V e).hom (O.topIso.hom.hom x))) =
      (φ.appLE O V e).hom (O.topIso.hom.hom x)
    exact CategoryTheory.Iso.inv_hom_id_apply V.topIso _
  have hpo2 : IsPushout (a.app U) (b.app U) ((pullback.fst a b).app (a ⁻¹ᵁ U))
      ((pullback.snd a b).appLE (b ⁻¹ᵁ U) ((pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U)) hle₂) := by
    refine hpo.of_iso (U.topIso) ((a ⁻¹ᵁ U).topIso) ((b ⁻¹ᵁ U).topIso) (((pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U)).topIso)
      ?_ ?_ ?_ ?_
    · rw [key, Scheme.Hom.app_eq_appLE]
    · rw [key, Scheme.Hom.app_eq_appLE]
    · rw [key, Scheme.Hom.app_eq_appLE]
    · rw [key]
  have h3 : IsPushout (a.app U) (b.app U)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Γ(X, a ⁻¹ᵁ U) →+* Γ(X, a ⁻¹ᵁ U) ⊗[Γ(Z, U)] Γ(Y, b ⁻¹ᵁ U)))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Γ(Y, b ⁻¹ᵁ U) →ₐ[Γ(Z, U)] Γ(X, a ⁻¹ᵁ U) ⊗[Γ(Z, U)] Γ(Y, b ⁻¹ᵁ U)).toRingHom) :=
    CommRingCat.isPushout_tensorProduct Γ(Z, U) Γ(X, a ⁻¹ᵁ U) Γ(Y, b ⁻¹ᵁ U)
  let e := IsPushout.isoIsPushout _ _ hpo2 h3
  refine ⟨e.commRingCatIsoToRingEquiv, ?_, ?_⟩
  · intro s
    change (((pullback.fst a b).app (a ⁻¹ᵁ U)) ≫ e.hom).hom s = s ⊗ₜ 1
    rw [IsPushout.inl_isoIsPushout_hom]
    rfl
  · intro s'
    change (((pullback.snd a b).appLE (b ⁻¹ᵁ U) ((pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U)) hle₂) ≫ e.hom).hom s' = 1 ⊗ₜ s'
    rw [IsPushout.inr_isoIsPushout_hom]
    rfl

end S_AlgebraicGeometry_exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen (solution)
