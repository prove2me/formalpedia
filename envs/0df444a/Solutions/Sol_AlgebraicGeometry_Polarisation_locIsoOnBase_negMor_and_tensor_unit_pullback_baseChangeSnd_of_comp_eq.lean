-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.locIsoOnBase_negMor_and_tensor_unit_pullback_baseChangeSnd_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/76e73670-a110-55cd-98a6-8e2c48c2f7a4

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_negMor_and_tensor_unit_pullback_baseChangeSnd_of_comp_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace AdmAscent

theorem mul_coe_congr {S : Type} [CommRing S] {A T : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    {P₁ Q₁ : SchemeHomOver t₁ f} {P₂ Q₂ : SchemeHomOver t₂ f} (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

def pbComp {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) ≅ (Scheme.Modules.pullback (a ≫ b)).obj M :=
  (Scheme.Modules.pullbackComp a b).app M

theorem locIsoOnBase_congr {S : Type} [CommRing S] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S))
    {M₁ N₁ M₂ N₂ : X.Modules} (e₁ : M₁ ≅ N₁) (e₂ : M₂ ≅ N₂) (h : LocIsoOnBase g M₁ M₂) :
    LocIsoOnBase g N₁ N₂ := by
  intro s
  obtain ⟨U, hs, ⟨i⟩⟩ := h s
  exact ⟨U, hs, ⟨(Scheme.Modules.pullback _).mapIso e₁.symm ≪≫ i ≪≫ (Scheme.Modules.pullback _).mapIso e₂⟩⟩

theorem over_comp {B Y X : Scheme.{0}} {t : Y ⟶ B} {f : X ⟶ B} (x : SchemeHomOver t f) : x.1 ≫ f = t := x.2

theorem over_comp_assoc {B Y X Z : Scheme.{0}} {t : Y ⟶ B} {f : X ⟶ B} (x : SchemeHomOver t f) (h : B ⟶ Z) :
    x.1 ≫ f ≫ h = t ≫ h := by
  rw [← Category.assoc, x.2]

section

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
  (B B' : Type) [CommRing B] [CommRing B'] [Algebra S B] [Algebra S B']
  (φ : B →+* B') (hφ : φ.comp (algebraMap S B) = algebraMap S B')

def ψ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B))) :=
  ⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩

include hφ in
theorem spec_φ_comp : Spec.map (CommRingCat.ofHom φ) ≫ (Spec.map (CommRingCat.ofHom (algebraMap S B))) = (Spec.map (CommRingCat.ofHom (algebraMap S B'))) := (ψ B B' φ hφ).2

theorem g_fst : RelPicard.baseChangeSnd f (ψ B B' φ hφ) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B'))) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem g_snd : RelPicard.baseChangeSnd f (ψ B B' φ hφ) ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))) =
    pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))) ≫ Spec.map (CommRingCat.ofHom φ) :=
  pullback.lift_snd _ _ _

theorem compat (B : Type) [CommRing B] [Algebra S B] (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of B))
    (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))) :
    ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))).mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))) =
      (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1 :=
  congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul (Spec.map (CommRingCat.ofHom (algebraMap S B))) L t' P Q)

theorem g_negMor : RelPicard.baseChangeSnd f (ψ B B' φ hφ) ≫ negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))) =
    negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))) ≫ RelPicard.baseChangeSnd f (ψ B B' φ hφ) :=
  RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible L B B' φ hφ _ _ (compat f L B) (compat f L B') _
    (g_fst f B B' φ hφ) (g_snd f B B' φ hφ)

theorem main (N : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules)
    (h : LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        ((Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj N) N ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (N ⊗ N) (𝟙_ ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules))) :
    LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
        ((Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))))).obj ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f (ψ B B' φ hφ))).obj N))
        ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f (ψ B B' φ hφ))).obj N) ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
        (((Scheme.Modules.pullback (RelPicard.baseChangeSnd f (ψ B B' φ hφ))).obj N) ⊗ ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f (ψ B B' φ hφ))).obj N)) (𝟙_ ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B')))).Modules)) := by
  obtain ⟨h1, h2⟩ := h
  have h1' := LocIsoOnBase.pullback_of_comp_eq (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) (RelPicard.baseChangeSnd f (ψ B B' φ hφ)) (Spec.map (CommRingCat.ofHom φ)) (g_snd f B B' φ hφ) h1
  have h2' := LocIsoOnBase.pullback_of_comp_eq (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) (RelPicard.baseChangeSnd f (ψ B B' φ hφ)) (Spec.map (CommRingCat.ofHom φ)) (g_snd f B B' φ hφ) h2
  refine ⟨locIsoOnBase_congr _ ?_ (Iso.refl _) h1', locIsoOnBase_congr _ (Scheme.Modules.pullbackTensorObjIso _ _ _)
    (Scheme.Modules.pullbackTensorUnitObjIso _) h2'⟩
  exact pbComp _ _ N ≪≫ (Scheme.Modules.pullbackCongr (g_negMor f L B B' φ hφ)).app N ≪≫ (pbComp _ _ N).symm

end

end AdmAscent

end

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (B B' : Type) [CommRing B] [CommRing B'] [Algebra S B] [Algebra S B']
    (φ : B →+* B') (hφ : φ.comp (algebraMap S B) = algebraMap S B')
    (N : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules) (hN : Scheme.Modules.IsInvertible N)
    (h : LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        ((Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
          (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj N) N ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        (N ⊗ N) (𝟙_ ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules))) :
    LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
        ((Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
          (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))))).obj ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj N)) ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj N) ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
        (((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj N) ⊗ ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj N)) (𝟙_ ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B')))).Modules)) :=
  AdmAscent.main f L B B' φ hφ N h

end S_AlgebraicGeometry_Polarisation_locIsoOnBase_negMor_and_tensor_unit_pullback_baseChangeSnd_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_negMor_and_tensor_unit_pullback_baseChangeSnd_of_comp_eq (solution)
