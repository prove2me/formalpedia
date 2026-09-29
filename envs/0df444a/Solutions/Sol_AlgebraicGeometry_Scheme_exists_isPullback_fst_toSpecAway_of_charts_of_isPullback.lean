-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_isPullback_fst_toSpecAway_of_charts_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/dbd6ff54-4ae8-5aa6-be1b-d7b72c0d54bc

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isPullback_fst_toSpecAway_of_charts_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem solution
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (ι : ∀ i, A' i ⟶ Y)
    [∀ i, IsOpenImmersion (ι i)]
    (hsq : ∀ i, CategoryTheory.IsPullback (ι i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (i j : Fin k) :
    ∃ (ρ₁ : B i →ₐ[S] Localization.Away (r i * r j))
      (fP : Limits.pullback (ι i) (ι j) ⟶ Spec (CommRingCat.of (Localization.Away (r i * r j)))),
      (letI := ρ₁.toRingHom.toAlgebra
       IsLocalization.Away (algebraMap S (B i) (r j)) (Localization.Away (r i * r j))) ∧
      CategoryTheory.IsPullback (Limits.pullback.fst (ι i) (ι j)) fP (f' i) (Spec.map (CommRingCat.ofHom ρ₁.toRingHom)) ∧
      fP ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i * r j)))) =
        Limits.pullback.fst (ι i) (ι j) ≫ ι i ≫ f := by
  classical
  set L := Localization.Away (r i * r j) with hL

  let L₁ := Localization.Away (algebraMap S (B i) (r j))
  let L₂ := Localization.Away (algebraMap S (B j) (r i))
  haveI : IsLocalization.Away (r i * r j) L₁ := inferInstance
  haveI : IsLocalization.Away (r i * r j) L₂ := inferInstance
  let e₁ : L₁ ≃ₐ[S] Localization.Away (r i * r j) := IsLocalization.algEquiv (Submonoid.powers (r i * r j)) L₁ _
  let e₂ : L₂ ≃ₐ[S] Localization.Away (r i * r j) := IsLocalization.algEquiv (Submonoid.powers (r i * r j)) L₂ _
  let ρ₁ : B i →ₐ[S] Localization.Away (r i * r j) := e₁.toAlgHom.comp (IsScalarTower.toAlgHom S (B i) L₁)
  let ρ₂ : B j →ₐ[S] Localization.Away (r i * r j) := e₂.toAlgHom.comp (IsScalarTower.toAlgHom S (B j) L₂)

  letI algI : Algebra (B i) (Localization.Away (r i * r j)) := ρ₁.toRingHom.toAlgebra
  letI algJ : Algebra (B j) (Localization.Away (r i * r j)) := ρ₂.toRingHom.toAlgebra
  have hawayI : IsLocalization.Away (algebraMap S (B i) (r j)) (Localization.Away (r i * r j)) := by
    let h₁ : L₁ ≃ₐ[B i] Localization.Away (r i * r j) := AlgEquiv.ofRingEquiv (f := e₁.toRingEquiv) (fun x => rfl)
    exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap S (B i) (r j))) h₁
  have hawayJ : IsLocalization.Away (algebraMap S (B j) (r i)) (Localization.Away (r i * r j)) := by
    let h₂ : L₂ ≃ₐ[B j] Localization.Away (r i * r j) := AlgEquiv.ofRingEquiv (f := e₂.toRingEquiv) (fun x => rfl)
    exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap S (B j) (r i))) h₂

  have hpo : IsPushout (CommRingCat.ofHom (algebraMap S (B j))) (CommRingCat.ofHom (algebraMap S (B i)))
      (CommRingCat.ofHom (algebraMap (B j) (Localization.Away (r i * r j)))) (CommRingCat.ofHom ρ₁.toRingHom) := by
    haveI := hawayJ
    refine CommRingCat.isPushout_of_isLocalization (algebraMap S (B j)) ρ₁.toRingHom ?_ (Submonoid.powers (r i))
    exact RingHom.ext fun s => (ρ₁.commutes s).trans (ρ₂.commutes s).symm
  have hbot : IsPullback (Spec.map (CommRingCat.ofHom ρ₁.toRingHom)) (Spec.map (CommRingCat.ofHom ρ₂.toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))) (Spec.map (CommRingCat.ofHom (algebraMap S (B j)))) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip

  have hR1 : IsPullback (pullback.fst (ι i) (ι j)) (pullback.snd (ι i) (ι j) ≫ f' j) (ι i ≫ f)
      (Spec.map (CommRingCat.ofHom (algebraMap S (B j)))) :=
    (IsPullback.of_hasPullback (ι i) (ι j)).paste_vert (hsq j)

  have hw : (pullback.fst (ι i) (ι j) ≫ f' i) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B i))) =
      (pullback.snd (ι i) (ι j) ≫ f' j) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B j))) := by
    rw [Category.assoc, Category.assoc, ← (hsq i).w, ← (hsq j).w, ← Category.assoc, ← Category.assoc, pullback.condition]
  let fP := hbot.lift _ _ hw
  have hfP₁ : fP ≫ Spec.map (CommRingCat.ofHom ρ₁.toRingHom) = pullback.fst (ι i) (ι j) ≫ f' i := hbot.lift_fst _ _ hw
  have hfP₂ : fP ≫ Spec.map (CommRingCat.ofHom ρ₂.toRingHom) = pullback.snd (ι i) (ι j) ≫ f' j := hbot.lift_snd _ _ hw
  have hs : IsPullback (pullback.fst (ι i) (ι j)) (fP ≫ Spec.map (CommRingCat.ofHom ρ₂.toRingHom))
      (f' i ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B i)))) (Spec.map (CommRingCat.ofHom (algebraMap S (B j)))) := by
    rw [hfP₂, ← (hsq i).w]; exact hR1
  refine ⟨ρ₁, fP, hawayI, IsPullback.of_bot hs hfP₁.symm hbot, ?_⟩
  have halg : algebraMap S (Localization.Away (r i * r j)) = ρ₁.toRingHom.comp (algebraMap S (B i)) :=
    RingHom.ext fun s => (ρ₁.commutes s).symm
  rw [halg, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc, hfP₁, Category.assoc, ← (hsq i).w]

end S_AlgebraicGeometry_Scheme_exists_isPullback_fst_toSpecAway_of_charts_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_isPullback_fst_toSpecAway_of_charts_of_isPullback (solution)
