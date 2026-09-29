-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_pullback_baseChangeSnd_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/12b46d86-9525-53e1-9f5b-2cc328a1237c

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Polarisation_IsSymmetric_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_tensor_pullback_negMor_iso_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_pullback_baseChangeSnd_of_comp_eq
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace SymRootAscent

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

theorem hmul_g {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B')) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))) :
    ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))).mul t' P Q).1 ≫ (RelPicard.baseChangeSnd f (ψ B B' φ hφ)) =
      ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))).mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ (RelPicard.baseChangeSnd f (ψ B B' φ hφ)), by rw [Category.assoc, g_snd f B B' φ hφ, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ (RelPicard.baseChangeSnd f (ψ B B' φ hφ)), by rw [Category.assoc, g_snd f B B' φ hφ, ← Category.assoc, Q.2]⟩).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, g_fst, compat f L B', compat f L B]
    apply mul_coe_congr L
    · rw [Category.assoc, spec_φ_comp B B' φ hφ]
    · change P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B'))) = (P.1 ≫ (RelPicard.baseChangeSnd f (ψ B B' φ hφ))) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B)))
      rw [Category.assoc, g_fst]
    · change Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B'))) = (Q.1 ≫ (RelPicard.baseChangeSnd f (ψ B B' φ hφ))) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B)))
      rw [Category.assoc, g_fst]
  · simp only [Category.assoc, g_snd, over_comp_assoc, over_comp]

theorem main (𝓛 : A.Modules) (M : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (h : IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))) M ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))))).obj 𝓛)
        (M ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M)) :
    IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))) ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f (ψ B B' φ hφ))).obj M) ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))).obj 𝓛)
        (((Scheme.Modules.pullback (RelPicard.baseChangeSnd f (ψ B B' φ hφ))).obj M) ⊗
          (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))))).obj
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f (ψ B B' φ hφ))).obj M)) := by
  have hg : IsPullback (RelPicard.baseChangeSnd f (ψ B B' φ hφ)) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (Spec.map (CommRingCat.ofHom φ)) :=
    RelPicard.isPullback_baseChangeSnd f (ψ B B' φ hφ)
  obtain ⟨hS, hR⟩ := h
  refine ⟨IsSymmetric.pullback_of_isPullback φ hg (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
      (fun t' P Q => hmul_g f L B B' φ hφ t' P Q) M hS, ?_⟩
  obtain ⟨e₂⟩ := nonempty_pullback_tensor_pullback_negMor_iso_of_comp_eq f L (algebraMap S B) (algebraMap S B') φ hφ (RelPicard.baseChangeSnd f (ψ B B' φ hφ))
    (g_fst f B B' φ hφ) (g_snd f B B' φ hφ) M
  exact locIsoOnBase_congr _ (pbComp _ _ 𝓛 ≪≫ (Scheme.Modules.pullbackCongr (g_fst f B B' φ hφ)).app 𝓛) e₂
    (LocIsoOnBase.pullback_of_comp_eq (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) (RelPicard.baseChangeSnd f (ψ B B' φ hφ)) (Spec.map (CommRingCat.ofHom φ)) (g_snd f B B' φ hφ) hR)

end

end SymRootAscent

end

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (B B' : Type) [CommRing B] [CommRing B'] [Algebra S B] [Algebra S B']
    (φ : B →+* B') (hφ : φ.comp (algebraMap S B) = algebraMap S B')
    (M : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (h : IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))) M ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))))).obj 𝓛)
        (M ⊗ (Scheme.Modules.pullback
          (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
            (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M)) :
    IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
        (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))) ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M) ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))).obj 𝓛)
        (((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M) ⊗ (Scheme.Modules.pullback
          (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
            (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))))).obj ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M)) :=
  SymRootAscent.main f L B B' φ hφ 𝓛 M hM h

end S_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_pullback_baseChangeSnd_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_pullback_baseChangeSnd_of_comp_eq (solution)
