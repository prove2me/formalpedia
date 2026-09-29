-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_iso_tensor_pullback_negMor_pullback_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/a47d22ca-0f8e-5be8-9f0c-8288db52b033

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_iso_tensor_pullback_negMor_pullback_of_comp_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace T1Sol

theorem baseChange_compat {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S']
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f) :
    ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S'))
      (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
      ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S S')))).mul t' P Q).1 ≫
          pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
        (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
          ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
            by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
            by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1 := by
  intro T t' P Q
  rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
  rfl

theorem negComm {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {T₁ T₂ : Type} [CommRing T₁] [CommRing T₂] (s₁ : S →+* T₁) (s₂ : S →+* T₂) (τ : T₁ →+* T₂)
    (hτ : τ.comp s₁ = s₂)
    (ρ : pullback f (Spec.map (CommRingCat.ofHom s₂)) ⟶ pullback f (Spec.map (CommRingCat.ofHom s₁)))
    (hρ₁ : ρ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom s₁)) = pullback.fst f (Spec.map (CommRingCat.ofHom s₂)))
    (hρ₂ : ρ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom s₁)) =
      pullback.snd f (Spec.map (CommRingCat.ofHom s₂)) ≫ Spec.map (CommRingCat.ofHom τ)) :
    ρ ≫ negMor (pullback.snd f (Spec.map (CommRingCat.ofHom s₁))) (L.baseChange (Spec.map (CommRingCat.ofHom s₁))) =
      negMor (pullback.snd f (Spec.map (CommRingCat.ofHom s₂))) (L.baseChange (Spec.map (CommRingCat.ofHom s₂))) ≫ ρ := by
  letI : Algebra S T₁ := s₁.toAlgebra
  letI : Algebra S T₂ := s₂.toAlgebra
  exact GoodReductionJacobian.RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible L T₁ T₂ τ hτ
    (L.baseChange _) (L.baseChange _) (baseChange_compat L) (baseChange_compat L) ρ hρ₁ hρ₂

noncomputable def transportIso {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {T₁ T₂ : Type} [CommRing T₁] [CommRing T₂] (s₁ : S →+* T₁) (s₂ : S →+* T₂) (τ : T₁ →+* T₂)
    (hτ : τ.comp s₁ = s₂)
    (ρ : pullback f (Spec.map (CommRingCat.ofHom s₂)) ⟶ pullback f (Spec.map (CommRingCat.ofHom s₁)))
    (hρ₁ : ρ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom s₁)) = pullback.fst f (Spec.map (CommRingCat.ofHom s₂)))
    (hρ₂ : ρ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom s₁)) =
      pullback.snd f (Spec.map (CommRingCat.ofHom s₂)) ≫ Spec.map (CommRingCat.ofHom τ))
    (𝓜 : (pullback f (Spec.map (CommRingCat.ofHom s₁))).Modules) :
    (Scheme.Modules.pullback ρ).obj
        (𝓜 ⊗ (Scheme.Modules.pullback
          (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom s₁))) (L.baseChange (Spec.map (CommRingCat.ofHom s₁))))).obj 𝓜) ≅
      (Scheme.Modules.pullback ρ).obj 𝓜 ⊗ (Scheme.Modules.pullback
        (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom s₂))) (L.baseChange (Spec.map (CommRingCat.ofHom s₂))))).obj
          ((Scheme.Modules.pullback ρ).obj 𝓜) :=
  Scheme.Modules.pullbackTensorObjIso ρ _ _ ≪≫
    whiskerLeftIso _
      ((Scheme.Modules.pullbackComp ρ (negMor _ (L.baseChange _))).app 𝓜 ≪≫
        (Scheme.Modules.pullbackCongr (negComm f L s₁ s₂ τ hτ ρ hρ₁ hρ₂)).app 𝓜 ≪≫
        ((Scheme.Modules.pullbackComp (negMor _ (L.baseChange _)) ρ).app 𝓜).symm)

end T1Sol

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {T₁ T₂ : Type} [CommRing T₁] [CommRing T₂] (s₁ : S →+* T₁) (s₂ : S →+* T₂) (τ : T₁ →+* T₂)
    (hτ : τ.comp s₁ = s₂)
    (ρ : pullback f (Spec.map (CommRingCat.ofHom s₂)) ⟶ pullback f (Spec.map (CommRingCat.ofHom s₁)))
    (hρ₁ : ρ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom s₁)) = pullback.fst f (Spec.map (CommRingCat.ofHom s₂)))
    (hρ₂ : ρ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom s₁)) =
      pullback.snd f (Spec.map (CommRingCat.ofHom s₂)) ≫ Spec.map (CommRingCat.ofHom τ))
    (𝓛 : A.Modules) (𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom s₁))).Modules)
    (e : Nonempty ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom s₁)))).obj 𝓛 ≅
      𝓛₀ ⊗ (Scheme.Modules.pullback
        (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom s₁))) (L.baseChange (Spec.map (CommRingCat.ofHom s₁))))).obj 𝓛₀)) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom s₂)))).obj 𝓛 ≅
      (Scheme.Modules.pullback ρ).obj 𝓛₀ ⊗ (Scheme.Modules.pullback
        (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom s₂))) (L.baseChange (Spec.map (CommRingCat.ofHom s₂))))).obj
          ((Scheme.Modules.pullback ρ).obj 𝓛₀)) := by
  obtain ⟨e₀⟩ := e
  exact ⟨((Scheme.Modules.pullbackCongr hρ₁).app 𝓛).symm ≪≫
    ((Scheme.Modules.pullbackComp ρ (pullback.fst f _)).app 𝓛).symm ≪≫
    (Scheme.Modules.pullback ρ).mapIso e₀ ≪≫
    T1Sol.transportIso f L s₁ s₂ τ hτ ρ hρ₁ hρ₂ 𝓛₀⟩

end S_AlgebraicGeometry_Polarisation_nonempty_iso_tensor_pullback_negMor_pullback_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_iso_tensor_pullback_negMor_pullback_of_comp_eq (solution)
