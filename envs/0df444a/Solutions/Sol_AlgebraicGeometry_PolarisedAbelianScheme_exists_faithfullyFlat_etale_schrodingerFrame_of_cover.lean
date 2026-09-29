-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_faithfullyFlat_etale_schrodingerFrame_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4d6f7045-654e-5aa4-8d0f-131104fc5d82

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_monoidHom_pt_comp_eq_act_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover.AlgebraicGeometry.Polarisation TopologicalSpace Opposite"

open scoped BigOperators

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.Hom.app_smul Surjective Scheme.Hom.iSup_preimage_eq_top Scheme.Modules.pushforward Scheme.Modules.pullback Scheme.Hom Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Modules.restrictFunctor Scheme.Modules.Hom.id_app Scheme.Modules.restrictAdjunction IsOpenImmersion Scheme.Hom.comp_appTop Flat Scheme.Hom.opensRange_of_isIso Scheme.Modules.pullbackCongr Spec.map_id Etale Scheme.Modules.pullbackPushforwardAdjunction Scheme.Hom.opensRange_comp_of_isIso Scheme.Modules Scheme.Hom.opensRange_pullbackFst Scheme.Hom.preimage_bot Scheme.Modules.pullbackComp Scheme.ΓSpecIso Polarisation.ThetaPt PolarisedAbelianScheme Scheme.Modules.pullbackLocalSection Scheme.Modules.pullbackLocalSection_def Scheme.Modules.pullbackLocalSection_add Scheme.Modules.pullbackLocalSection_sum Scheme.Modules.pullbackLocalSection_smul Polarisation.ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one"
namespace Polarisation
p2m_export "AlgebraicGeometry.Polarisation" "ThetaPt.ofUnit ThetaPt.ofScalar ThetaPt baseScalar SchrodingerFrame ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback"
namespace ThetaPtGlue
p2m_open "AlgebraicGeometry.Polarisation AlgebraicGeometry"

section Cover

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
  {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
  {m : ℕ} (ε : Fin m → R)
  (b : ∀ j, pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) ⟶ pullback f t)
  (hb₁ : ∀ j, b j ≫ pullback.fst f t =
    pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t))
  (hb₂ : ∀ j, b j ≫ pullback.snd f t =
    pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))))

include hb₁ hb₂ in

theorem piece_eq (j : Fin m) :
    b j = (pullbackLeftPullbackSndIso f t (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))))).inv ≫
      pullback.fst (pullback.snd f t) (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j))))) := by
  apply pullback.hom_ext
  · rw [hb₁, Category.assoc, pullbackLeftPullbackSndIso_inv_fst]
  · rw [hb₂, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd]

include hb₁ hb₂ in
theorem isOpenImmersion_piece (j : Fin m) : IsOpenImmersion (b j) := by
  rw [piece_eq f t ε b hb₁ hb₂ j]
  infer_instance

theorem opensRange_specMap_away (r : R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).opensRange =
      PrimeSpectrum.basicOpen r :=
  Opens.ext (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r)

include hb₁ hb₂ in
theorem opensRange_piece [∀ j, IsOpenImmersion (b j)] (j : Fin m) :
    (b j).opensRange = pullback.snd f t ⁻¹ᵁ (PrimeSpectrum.basicOpen (ε j) : (Spec (CommRingCat.of R)).Opens) := by
  have key : ∀ (g : _ ⟶ pullback f t) [IsOpenImmersion g], g = b j → (b j).opensRange = g.opensRange := by
    rintro g _ rfl; rfl
  rw [key _ (piece_eq f t ε b hb₁ hb₂ j).symm, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Hom.opensRange_pullbackFst, opensRange_specMap_away]

include hb₁ hb₂ in
theorem iSup_opensRange_piece_eq_top [∀ j, IsOpenImmersion (b j)] (hsum : ∑ j, ε j = 1) :
    ⨆ j, (b j).opensRange = ⊤ := by
  simp_rw [opensRange_piece f t ε b hb₁ hb₂]
  apply Scheme.Hom.iSup_preimage_eq_top
  have key : (⨆ i, PrimeSpectrum.basicOpen (ε i) : Opens (PrimeSpectrum R)) = ⊤ := by
    rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff, Ideal.eq_top_iff_one, ← hsum]
    exact Ideal.sum_mem _ fun j _ => Ideal.subset_span ⟨j, rfl⟩
  exact key

include hb₁ hb₂ in
theorem opensRange_piece_inf_eq_bot [∀ j, IsOpenImmersion (b j)] (horth : ∀ j l, j ≠ l → ε j * ε l = 0)
    (j l : Fin m) (hjl : j ≠ l) : (b j).opensRange ⊓ (b l).opensRange = ⊥ := by
  rw [opensRange_piece f t ε b hb₁ hb₂ j, opensRange_piece f t ε b hb₁ hb₂ l, ← Scheme.Hom.preimage_inf]
  have key : (PrimeSpectrum.basicOpen (ε j) ⊓ PrimeSpectrum.basicOpen (ε l) : Opens (PrimeSpectrum R)) = ⊥ := by
    rw [← PrimeSpectrum.basicOpen_mul, horth j l hjl, PrimeSpectrum.basicOpen_zero]
  exact (congrArg (fun V : (Spec (CommRingCat.of R)).Opens => pullback.snd f t ⁻¹ᵁ V) key).trans
    (Scheme.Hom.preimage_bot _)

end Cover

theorem pullbackLocalSection_eq_restrict {X Y : Scheme.{0}} (g : Y ⟶ X) [IsOpenImmersion g] (M : X.Modules)
    (w : Γ(M, ⊤)) :
    Scheme.Modules.pullbackLocalSection (U := ⊤) g w =
      (((Scheme.Modules.pushforward g).map
          (((Scheme.Modules.restrictAdjunction g).leftAdjointUniq
            (Scheme.Modules.pullbackPushforwardAdjunction g)).hom.app M)).app ⊤)
        ((((Scheme.Modules.restrictAdjunction g).unit.app M).app ⊤) w) := by
  rw [Scheme.Modules.pullbackLocalSection_def, ← Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction g) (Scheme.Modules.pullbackPushforwardAdjunction g) M]
  rfl

theorem eq_of_forall_pullbackLocalSection_eq
    {X : Scheme.{0}} (M : X.Modules) {ι : Type} {Y : ι → Scheme.{0}} (b : ∀ j, Y j ⟶ X)
    [∀ j, IsOpenImmersion (b j)] (hcov : ⨆ j, (b j).opensRange = ⊤)
    (u v : Γ(M, ⊤))
    (h : ∀ j, Scheme.Modules.pullbackLocalSection (b j) u = Scheme.Modules.pullbackLocalSection (b j) v) :
    u = v := by

  have h2 : ∀ j, M.presheaf.map (homOfLE ((b j).image_preimage_le ⊤)).op u =
      M.presheaf.map (homOfLE ((b j).image_preimage_le ⊤)).op v := by
    intro j
    have hu := pullbackLocalSection_eq_restrict (b j) M u
    have hv := pullbackLocalSection_eq_restrict (b j) M v
    rw [h j] at hu
    have hinj : Function.Injective
        (((Scheme.Modules.pushforward (b j)).map
          (((Scheme.Modules.restrictAdjunction (b j)).leftAdjointUniq
            (Scheme.Modules.pullbackPushforwardAdjunction (b j))).hom.app M)).app ⊤) := by
      intro a a' haa
      have := congrArg (inv ((((Scheme.Modules.pushforward (b j)).map
          (((Scheme.Modules.restrictAdjunction (b j)).leftAdjointUniq
            (Scheme.Modules.pullbackPushforwardAdjunction (b j))).hom.app M)).app ⊤))) haa
      simpa only [← CategoryTheory.comp_apply, IsIso.hom_inv_id, CategoryTheory.id_apply] using this
    exact hinj (hu.symm.trans hv)

  have hU : ∀ j, (b j) ''ᵁ ((b j) ⁻¹ᵁ ⊤) = (b j).opensRange := fun j => (b j).image_top_eq_opensRange
  have hcover : (⊤ : X.Opens) ≤ ⨆ j, (b j) ''ᵁ ((b j) ⁻¹ᵁ ⊤) := by
    rw [show (fun j => (b j) ''ᵁ ((b j) ⁻¹ᵁ ⊤)) = fun j => (b j).opensRange from funext hU, hcov]
  let F : TopCat.Sheaf Ab X.carrier := (SheafOfModules.toSheaf _).obj M
  exact TopCat.Sheaf.eq_of_locally_eq' F (fun j => (b j) ''ᵁ ((b j) ⁻¹ᵁ ⊤)) ⊤
    (fun j => homOfLE ((b j).image_preimage_le ⊤)) hcover u v h2

end AlgebraicGeometry.Polarisation.ThetaPtGlue

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.Hom.app_smul Surjective Scheme.Hom.iSup_preimage_eq_top Scheme.Modules.pushforward Scheme.Modules.pullback Scheme.Hom Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Modules.restrictFunctor Scheme.Modules.Hom.id_app Scheme.Modules.restrictAdjunction IsOpenImmersion Scheme.Hom.comp_appTop Flat Scheme.Hom.opensRange_of_isIso Scheme.Modules.pullbackCongr Spec.map_id Etale Scheme.Modules.pullbackPushforwardAdjunction Scheme.Hom.opensRange_comp_of_isIso Scheme.Modules Scheme.Hom.opensRange_pullbackFst Scheme.Hom.preimage_bot Scheme.Modules.pullbackComp Scheme.ΓSpecIso Polarisation.ThetaPt PolarisedAbelianScheme Scheme.Modules.pullbackLocalSection Scheme.Modules.pullbackLocalSection_def Scheme.Modules.pullbackLocalSection_add Scheme.Modules.pullbackLocalSection_sum Scheme.Modules.pullbackLocalSection_smul Polarisation.ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one"
namespace Polarisation
p2m_export "AlgebraicGeometry.Polarisation" "ThetaPt.ofUnit ThetaPt.ofScalar ThetaPt baseScalar SchrodingerFrame ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback"
namespace EtaleAbsorb
p2m_open "AlgebraicGeometry.Polarisation AlgebraicGeometry"

open AlgebraicGeometry.Polarisation.ThetaPtGlue

section Generic

variable {X : Scheme.{0}} (M : X.Modules)

def chartMap {Y : Scheme.{0}} (b : Y ⟶ X) {N : Y.Modules} (c : (Scheme.Modules.pullback b).obj M ≅ N) (s : Γ(M, ⊤)) :
    Γ(N, ⊤) :=
  c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection (U := ⊤) b s : Γ((Scheme.Modules.pullback b).obj M, ⊤))

theorem chartMap_def {Y : Scheme.{0}} (b : Y ⟶ X) {N : Y.Modules} (c : (Scheme.Modules.pullback b).obj M ≅ N)
    (s : Γ(M, ⊤)) :
    chartMap M b c s =
      c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection (U := ⊤) b s : Γ((Scheme.Modules.pullback b).obj M, ⊤)) := rfl

theorem chartMap_add {Y : Scheme.{0}} (b : Y ⟶ X) {N : Y.Modules} (c : (Scheme.Modules.pullback b).obj M ≅ N)
    (s s' : Γ(M, ⊤)) : chartMap M b c (s + s') = chartMap M b c s + chartMap M b c s' := by
  rw [chartMap_def, Scheme.Modules.pullbackLocalSection_add]
  exact (c.hom.app ⊤).hom.map_add _ _

theorem chartMap_sum {Y : Scheme.{0}} (b : Y ⟶ X) {N : Y.Modules} (c : (Scheme.Modules.pullback b).obj M ≅ N)
    {ι : Type} (T : Finset ι) (s : ι → Γ(M, ⊤)) :
    chartMap M b c (∑ i ∈ T, s i) = ∑ i ∈ T, chartMap M b c (s i) := by
  rw [chartMap_def, Scheme.Modules.pullbackLocalSection_sum]
  exact map_sum (c.hom.app ⊤).hom _ _

theorem chartMap_smul {Y : Scheme.{0}} (b : Y ⟶ X) {N : Y.Modules} (c : (Scheme.Modules.pullback b).obj M ≅ N)
    (g : Γ(X, ⊤)) (s : Γ(M, ⊤)) : chartMap M b c (g • s) = b.appTop g • chartMap M b c s := by
  rw [chartMap_def, chartMap_def]
  have h1 : Scheme.Modules.pullbackLocalSection (U := ⊤) b (g • s) =
      HSMul.hSMul (α := Γ(Y, ⊤)) (β := Γ((Scheme.Modules.pullback b).obj M, ⊤)) (b.appTop g)
        (Scheme.Modules.pullbackLocalSection (U := ⊤) b s) :=
    Scheme.Modules.pullbackLocalSection_smul b g s
  rw [h1, Scheme.Modules.Hom.app_smul]

variable {ι : Type} {Y : ι → Scheme.{0}} (b : ∀ j, Y j ⟶ X) [∀ j, IsOpenImmersion (b j)]
  {N : ∀ j, (Y j).Modules} (c : ∀ j, (Scheme.Modules.pullback (b j)).obj M ≅ N j)

theorem iso_hom_app_inv_app_apply {M' N' : X.Modules} (e : M' ≅ N') (U : X.Opens) (x : Γ(N', U)) :
    e.hom.app U (e.inv.app U x) = x := by
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl

theorem eq_of_forall_chartMap_eq (hcov : ⨆ j, (b j).opensRange = ⊤) (s s' : Γ(M, ⊤))
    (h : ∀ j, chartMap M (b j) (c j) s = chartMap M (b j) (c j) s') : s = s' := by
  apply eq_of_forall_pullbackLocalSection_eq M b hcov
  intro j
  have hinj : Function.Injective ((c j).hom.app ⊤) := by
    intro a a' haa
    have := congrArg ((c j).inv.app ⊤) haa
    simpa only [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
      Scheme.Modules.Hom.id_app, CategoryTheory.id_apply] using this
  exact hinj (h j)

theorem eq_of_eq_bot (V : X.Opens) (hV : V = ⊥) (a a' : Γ(M, V)) : a = a' := by
  let F : TopCat.Sheaf Ab X.carrier := (SheafOfModules.toSheaf _).obj M
  exact TopCat.Sheaf.eq_of_locally_eq' F (fun i : Empty => (⊥ : X.Opens)) V (fun i => i.elim) (hV.le.trans bot_le)
    a a' (fun i => i.elim)

theorem exists_forall_chartMap_eq (hcov : ⨆ j, (b j).opensRange = ⊤)
    (hdisj : ∀ j l, j ≠ l → (b j).opensRange ⊓ (b l).opensRange = ⊥) (v : ∀ j, Γ(N j, ⊤)) :
    ∃ s : Γ(M, ⊤), ∀ j, chartMap M (b j) (c j) s = v j := by

  obtain ⟨e, he⟩ : ∃ e : ∀ j, (Scheme.Modules.pushforward (b j)).obj ((Scheme.Modules.restrictFunctor (b j)).obj M) ≅
      (Scheme.Modules.pushforward (b j)).obj ((Scheme.Modules.pullback (b j)).obj M),
      ∀ j, (e j).hom = (Scheme.Modules.pushforward (b j)).map
        (((Scheme.Modules.restrictAdjunction (b j)).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction (b j))).hom.app M) :=
    ⟨fun j => (Scheme.Modules.pushforward (b j)).mapIso
      (((Scheme.Modules.restrictAdjunction (b j)).leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction (b j))).app M), fun j => rfl⟩
  have hU : ∀ j, (b j) ''ᵁ ((b j) ⁻¹ᵁ ⊤) = (b j).opensRange := fun j => (b j).image_top_eq_opensRange
  have hcover : (⊤ : X.Opens) ≤ ⨆ j, (b j) ''ᵁ ((b j) ⁻¹ᵁ ⊤) := by
    rw [show (fun j => (b j) ''ᵁ ((b j) ⁻¹ᵁ ⊤)) = fun j => (b j).opensRange from funext hU, hcov]
  let F : TopCat.Sheaf Ab X.carrier := (SheafOfModules.toSheaf _).obj M

  have hcompat : TopCat.Presheaf.IsCompatible F.1 (fun j => (b j) ''ᵁ ((b j) ⁻¹ᵁ ⊤))
      (fun j => ((e j).inv.app ⊤ ((c j).inv.app ⊤ (v j)) : Γ(M, (b j) ''ᵁ ((b j) ⁻¹ᵁ ⊤)))) := by
    intro j l
    by_cases hjl : j = l
    · subst hjl; rfl
    · apply eq_of_eq_bot M
      change (b j) ''ᵁ ((b j) ⁻¹ᵁ ⊤) ⊓ (b l) ''ᵁ ((b l) ⁻¹ᵁ ⊤) = ⊥
      rw [hU, hU, hdisj j l hjl]
  obtain ⟨s, hs⟩ := (TopCat.Sheaf.existsUnique_gluing' F (fun j => (b j) ''ᵁ ((b j) ⁻¹ᵁ ⊤)) ⊤
    (fun j => homOfLE ((b j).image_preimage_le ⊤)) hcover
    (fun j => ((e j).inv.app ⊤ ((c j).inv.app ⊤ (v j)) : Γ(M, (b j) ''ᵁ ((b j) ⁻¹ᵁ ⊤)))) hcompat).exists
  refine ⟨s, fun j => ?_⟩
  rw [chartMap_def, pullbackLocalSection_eq_restrict, ← he]
  change (c j).hom.app ⊤ ((e j).hom.app ⊤ (F.1.map (homOfLE ((b j).image_preimage_le ⊤)).op s)) = v j
  rw [hs j]
  change (c j).hom.app ⊤ ((e j).hom.app ⊤ ((e j).inv.app ⊤ ((c j).inv.app ⊤ (v j)))) = v j
  rw [iso_hom_app_inv_app_apply (e j), iso_hom_app_inv_app_apply (c j)]

def compCongrIso {X' Y' Z' : Scheme.{0}} (p : X' ⟶ Y') (q : Y' ⟶ Z') (r : X' ⟶ Z') (h : p ≫ q = r) (M' : Z'.Modules) :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj M') ≅ (Scheme.Modules.pullback r).obj M' :=
  (Scheme.Modules.pullbackComp p q).app M' ≪≫ (Scheme.Modules.pullbackCongr h).app M'

end Generic

section Chart

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
  {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) {m : ℕ} (ε : Fin m → R)

def chart (j : Fin m) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) ⟶ pullback f t :=
  pullback.lift (pullback.fst f _)
    (pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))))
    (by rw [Category.assoc]; exact pullback.condition)

theorem chart_fst (j : Fin m) : chart f t ε j ≫ pullback.fst f t = pullback.fst f _ := pullback.lift_fst _ _ _

theorem chart_snd (j : Fin m) :
    chart f t ε j ≫ pullback.snd f t =
      pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) :=
  pullback.lift_snd _ _ _

end Chart

theorem appTop_baseScalar {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    {R R' : Type} [CommRing R] [CommRing R']
    (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (t' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S))
    (φ : R →+* R') (b : pullback f t' ⟶ pullback f t)
    (hb₂ : b ≫ pullback.snd f t = pullback.snd f t' ≫ Spec.map (CommRingCat.ofHom φ)) (x : R) :
    b.appTop (baseScalar f t x) = baseScalar f t' (φ x) := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pullback.snd f t).appTop ≫ b.appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ (pullback.snd f t').appTop := by
    rw [← Scheme.Hom.comp_appTop, hb₂, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc]
  have := congrArg (fun k => k.hom x) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this

theorem algebraMap_away_apply_eq_one {R : Type} [CommRing R] (e : R) (he : IsIdempotentElem e) :
    algebraMap R (Localization.Away e) e = 1 := by
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away e) e
  have hu2 : u * u = u := by rw [Units.ext_iff] at *; push_cast; rw [hu, ← map_mul, he.eq]
  have : u = 1 := by simpa using hu2
  rw [← hu, this, Units.val_one]

theorem algebraMap_pi_away_bijective {R : Type} [CommRing R] {m : ℕ} (ε : Fin m → R)
    (hε : ∀ j, IsIdempotentElem (ε j)) (hsum : ∑ j, ε j = 1) (horth : ∀ j l, j ≠ l → ε j * ε l = 0) :
    Function.Bijective (fun x : R => fun j => algebraMap R (Localization.Away (ε j)) x) := by
  classical
  have hmul : ∀ j (x x' : R), algebraMap R (Localization.Away (ε j)) x = algebraMap R (Localization.Away (ε j)) x' →
      ε j * x = ε j * x' := by
    intro j x x' h
    obtain ⟨⟨c, hc⟩, hcx⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (ε j)) _).mp h
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hc
    have : ε j * (ε j ^ n * x) = ε j * (ε j ^ n * x') := by rw [hcx]
    rcases n with _ | n
    · simpa using this
    · simpa only [(hε j).pow_succ_eq, ← mul_assoc, (hε j).eq] using this
  constructor
  · intro x x' h
    have hj : ∀ j, ε j * x = ε j * x' := fun j => hmul j x x' (congrFun h j)
    calc x = (∑ j, ε j) * x := by rw [hsum, one_mul]
      _ = ∑ j, ε j * x' := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => hj j
      _ = x' := by rw [← Finset.sum_mul, hsum, one_mul]
  · intro y
    choose x hx using fun j => IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem (ε j) (hε j)
      (S := Localization.Away (ε j)) (y j)
    refine ⟨∑ l, ε l * x l, funext fun j => ?_⟩
    change algebraMap R (Localization.Away (ε j)) (∑ l, ε l * x l) = y j
    rw [map_sum, Finset.sum_eq_single j]
    · rw [map_mul, algebraMap_away_apply_eq_one _ (hε j), one_mul, hx]
    · intro l _ hlj
      rw [map_mul, ← one_mul (algebraMap R _ (ε l)), ← algebraMap_away_apply_eq_one _ (hε j), ← map_mul,
        horth j l (Ne.symm hlj), map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ j) h

section ChartIso

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (𝓛 : A.Modules)
  {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) {m : ℕ} (ε : Fin m → R)

def chartIsoFam (j : Fin m) :
    (Scheme.Modules.pullback (chart f t ε j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅ ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t))).obj 𝓛) :=
  compCongrIso (chart f t ε j) (pullback.fst f t) (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t)) (chart_fst f t ε j) 𝓛

end ChartIso

theorem nonempty_schrodingerFrame_of_isIdempotentElem_of_sum_eq_one
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules) {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)]
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    {m : ℕ} (ε : Fin m → R) (hε : ∀ j, IsIdempotentElem (ε j)) (hsum : ∑ j, ε j = 1)
    (horth : ∀ j l, j ≠ l → ε j * ε l = 0)
    (F : ∀ j, SchrodingerFrame f L 𝓛 (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) δ) :
    Nonempty (SchrodingerFrame f L 𝓛 t δ) := by
  classical
  obtain ⟨B, hB₁, hB₂, ⟨C⟩⟩ : ∃ B : ∀ j, pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) ⟶ pullback f t,
      (∀ j, B j ≫ pullback.fst f t = pullback.fst f _) ∧
      (∀ j, B j ≫ pullback.snd f t =
        pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j))))) ∧
      Nonempty (∀ j, (Scheme.Modules.pullback (B j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
        (Scheme.Modules.pullback (pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t))).obj 𝓛) :=
    ⟨chart f t ε, chart_fst f t ε, chart_snd f t ε, ⟨chartIsoFam f 𝓛 t ε⟩⟩

  haveI hOI : ∀ j, IsOpenImmersion (B j) := fun j =>
    isOpenImmersion_piece f t ε (B) (hB₁) (hB₂) j
  have hcov : ⨆ j, (B j).opensRange = ⊤ :=
    iSup_opensRange_piece_eq_top f t ε (B) (hB₁) (hB₂) hsum
  have hdisj := opensRange_piece_inf_eq_bot f t ε (B) (hB₁) (hB₂) horth

  have ρ_smul : ∀ j (x : R) (s : Γ(((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤)),
      chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) (baseScalar f t x • s) =
        baseScalar f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) (algebraMap R (Localization.Away (ε j)) x) • chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) s := by
    intro j x s
    rw [chartMap_smul, appTop_baseScalar f t _ (algebraMap R (Localization.Away (ε j))) (B j) (hB₂ j)]
  have ρ_sum : ∀ j (s : ((i : Fin g) → ZMod (δ i)) → Γ(((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤)),
      chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) (∑ h, s h) = ∑ h, chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) (s h) :=
    fun j s => chartMap_sum ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) Finset.univ s
  have ρ_inj : ∀ s s' : Γ(((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤),
      (∀ j, chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) s = chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) s') → s = s' :=
    eq_of_forall_chartMap_eq ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B) (C) hcov
  have ρ_surj : ∀ v : (∀ j, Γ(((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t))).obj 𝓛), ⊤)), ∃ s : Γ(((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤), ∀ j, chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) s = v j :=
    exists_forall_chartMap_eq ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B) (C) hcov hdisj
  have alg := algebraMap_pi_away_bijective ε hε hsum horth
  have hχ : ∀ (χ : AddChar ((i : Fin g) → ZMod (δ i)) R) j h,
      ((algebraMap R (Localization.Away (ε j))).toMonoidHom.compAddChar χ) h = algebraMap R (Localization.Away (ε j)) (χ h) := fun χ j h => rfl

  obtain ⟨σ, hσ⟩ : ∃ σ : ((i : Fin g) → ZMod (δ i)) → Γ(((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤), ∀ h j, chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) (σ h) = (F j).σ h :=
    ⟨fun h => (ρ_surj fun j => (F j).σ h).choose, fun h j => (ρ_surj fun j => (F j).σ h).choose_spec j⟩

  have hglue := fun θ' : ∀ j, ThetaPt f L 𝓛 (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) =>
    AlgebraicGeometry.Polarisation.ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one
      f L 𝓛 t ε hε hsum horth (B) (hB₁) (hB₂) (C) θ'
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : ((i : Fin g) → ZMod (δ i)) → ThetaPt f L 𝓛 t, ∀ h (s s' : Γ(((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤)),
      (∀ j, ((F j).lift h).act ((C j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (B j) s)) =
        (C j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (B j) s')) → (Θ h).act s = s' :=
    ⟨fun h => (hglue fun j => (F j).lift h).choose, fun h => (hglue fun j => (F j).lift h).choose_spec.2.2⟩
  obtain ⟨η, hη⟩ : ∃ η : AddChar ((i : Fin g) → ZMod (δ i)) R → ThetaPt f L 𝓛 t, ∀ χ (s s' : Γ(((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤)),
      (∀ j, ((F j).dualLift ((algebraMap R (Localization.Away (ε j))).toMonoidHom.compAddChar χ)).act
          ((C j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (B j) s)) =
        (C j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (B j) s')) → (η χ).act s = s' :=
    ⟨fun χ => (hglue fun j => (F j).dualLift ((algebraMap R (Localization.Away (ε j))).toMonoidHom.compAddChar χ)).choose,
      fun χ => (hglue fun j => (F j).dualLift ((algebraMap R (Localization.Away (ε j))).toMonoidHom.compAddChar χ)).choose_spec.2.2⟩

  have ρΦ : ∀ j (cf : ((i : Fin g) → ZMod (δ i)) → R),
      chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) (∑ h, baseScalar f t (cf h) • σ h) =
        ∑ h, baseScalar f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) (algebraMap R (Localization.Away (ε j)) (cf h)) • (F j).σ h := by
    intro j cf
    rw [ρ_sum]
    exact Finset.sum_congr rfl fun h _ => by rw [ρ_smul, hσ]
  refine ⟨{ σ := σ, basis := ?_, lift := Θ, dualLift := η, lift_act := ?_, dualLift_act := ?_ }⟩
  ·
    constructor
    · intro c₁ c₂ h12
      have h12' : ∑ h, baseScalar f t (c₁ h) • σ h = ∑ h, baseScalar f t (c₂ h) • σ h := h12
      funext h
      apply alg.1
      funext j
      have hj := congrArg (chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j)) h12'
      rw [ρΦ, ρΦ] at hj
      exact congrFun ((F j).basis.1 hj) h
    · intro s
      have hcj := fun j => (F j).basis.2 (chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) s)
      obtain ⟨cf, hcf⟩ : ∃ cf : ((i : Fin g) → ZMod (δ i)) → R, ∀ h j, algebraMap R (Localization.Away (ε j)) (cf h) = (hcj j).choose h :=
        ⟨fun h => (alg.2 fun j => (hcj j).choose h).choose,
          fun h j => congrFun (alg.2 fun j => (hcj j).choose h).choose_spec j⟩
      refine ⟨cf, ρ_inj _ _ fun j => ?_⟩
      rw [ρΦ]
      refine Eq.trans ?_ (hcj j).choose_spec
      exact Finset.sum_congr rfl fun h _ => by rw [hcf]
  ·
    intro h h'
    apply hΘ
    intro j
    rw [← chartMap_def ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) (σ h'), ← chartMap_def ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) (σ (h + h')), hσ, hσ,
      (F j).lift_act]
  ·
    intro χ h
    apply hη
    intro j
    rw [← chartMap_def ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) (σ h), ← chartMap_def ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (B j) (C j) (baseScalar f t (χ h) • σ h),
      hσ, (F j).dualLift_act, ρ_smul, hσ, hχ]

theorem faithfullyFlat_and_etale_pi_away
    {S : Type} [CommRing S] (S₁ : Type) [CommRing S₁] [Algebra S S₁] [Module.FaithfullyFlat S S₁] [Algebra.Etale S S₁]
    {m : ℕ} (r : Fin m → S₁) (hr : Ideal.span (Set.range r) = ⊤) :
    Module.FaithfullyFlat S (Π j, Localization.Away (r j)) ∧ Algebra.Etale S (Π j, Localization.Away (r j)) := by
  classical

  haveI hE₁ : ∀ j, Algebra.Etale S₁ (Localization.Away (r j)) := fun j =>
    Algebra.Etale.of_isLocalizationAway (r j)
  haveI hE : ∀ j, Algebra.Etale S (Localization.Away (r j)) := fun j => inferInstance
  have hEpi : Algebra.Etale S (Π j, Localization.Away (r j)) := inferInstance
  have hEpi₁ : Algebra.Etale S₁ (Π j, Localization.Away (r j)) := inferInstance

  haveI : Module.Flat S₁ (Π j, Localization.Away (r j)) := inferInstance

  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap S₁ (Π j, Localization.Away (r j)))) := by
    intro 𝔭
    have hj : ∃ j, r j ∉ 𝔭.asIdeal := by
      by_contra h
      push Not at h
      have hle : Ideal.span (Set.range r) ≤ 𝔭.asIdeal := Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact h j)
      rw [hr, top_le_iff] at hle
      exact 𝔭.isPrime.ne_top hle
    obtain ⟨j, hj⟩ := hj
    have hmem : 𝔭 ∈ Set.range (PrimeSpectrum.comap (algebraMap S₁ (Localization.Away (r j)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (r j)) (r j)]
      exact hj
    obtain ⟨q, hq⟩ := hmem
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun j => Localization.Away (r j)) j) q, ?_⟩
    have hcomp : (Pi.evalRingHom (fun j => Localization.Away (r j)) j).comp
        (algebraMap S₁ (Π j, Localization.Away (r j))) = algebraMap S₁ (Localization.Away (r j)) := by
      ext s; rfl
    rw [← hq, ← hcomp, PrimeSpectrum.comap_comp]
    rfl
  have hFF₁ : Module.FaithfullyFlat S₁ (Π j, Localization.Away (r j)) :=
    Module.FaithfullyFlat.of_comap_surjective hsurj
  exact ⟨Module.FaithfullyFlat.trans S S₁ (Π j, Localization.Away (r j)), hEpi⟩

theorem isLocalizationAway_single_eval {m : ℕ} (A : Fin m → Type) [∀ i, CommRing (A i)] (j : Fin m) :
    letI := (Pi.evalRingHom A j).toAlgebra
    IsLocalization.Away (Pi.single (M := A) j 1) (A j) := by
  classical
  letI := (Pi.evalRingHom A j).toAlgebra
  refine IsLocalization.away_of_isIdempotentElem_of_mul ?_ ?_ ?_
  · show Pi.single (M := A) j 1 * Pi.single j 1 = Pi.single j 1
    rw [← Pi.single_mul, mul_one]
  · intro x y
    change x j = y j ↔ Pi.single (M := A) j 1 * x = Pi.single j 1 * y
    constructor
    · intro h
      funext i
      by_cases hij : i = j
      · subst hij; simp [h]
      · simp [Pi.single_apply, hij]
    · intro h
      have := congrFun h j
      simpa using this
  · exact Function.surjective_eval j

theorem exists_ringEquiv_away_comp_eq
    {S : Type} [CommRing S] (S₁ : Type) [CommRing S₁] [Algebra S S₁] {m : ℕ} (r : Fin m → S₁) (j : Fin m) :
    ∃ ψ : Localization.Away (r j) ≃+*
        Localization.Away (Pi.single (M := fun i => Localization.Away (r i)) j 1),
      ψ.toRingHom.comp ((algebraMap S₁ (Localization.Away (r j))).comp (algebraMap S S₁)) =
        (algebraMap (Π i, Localization.Away (r i))
            (Localization.Away (Pi.single (M := fun i => Localization.Away (r i)) j 1))).comp
          (algebraMap S (Π i, Localization.Away (r i))) := by
  classical
  letI alg : Algebra (Π i, Localization.Away (r i)) (Localization.Away (r j)) :=
    (Pi.evalRingHom (fun i => Localization.Away (r i)) j).toAlgebra
  haveI : IsLocalization.Away (Pi.single (M := fun i => Localization.Away (r i)) j 1) (Localization.Away (r j)) :=
    isLocalizationAway_single_eval (fun i => Localization.Away (r i)) j
  let ψ : Localization.Away (r j) ≃ₐ[Π i, Localization.Away (r i)]
      Localization.Away (Pi.single (M := fun i => Localization.Away (r i)) j 1) :=
    IsLocalization.algEquiv (Submonoid.powers (Pi.single (M := fun i => Localization.Away (r i)) j 1)) _ _
  refine ⟨ψ.toRingEquiv, ?_⟩
  ext s
  have h1 : (algebraMap S₁ (Localization.Away (r j))) (algebraMap S S₁ s) =
      algebraMap (Π i, Localization.Away (r i)) (Localization.Away (r j))
        (algebraMap S (Π i, Localization.Away (r i)) s) := by
    change _ = (algebraMap S (Π i, Localization.Away (r i)) s) j
    rw [Pi.algebraMap_apply]
    exact (IsScalarTower.algebraMap_apply S S₁ (Localization.Away (r j)) s).symm
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [h1]
  exact ψ.commutes _

section Idempotents

variable {m : ℕ} (A : Fin m → Type) [∀ j, CommRing (A j)]

theorem isIdempotentElem_single (j : Fin m) : IsIdempotentElem (Pi.single (M := A) j 1) := by
  classical
  exact (CompleteOrthogonalIdempotents.single A).idem j

theorem sum_single_eq_one : ∑ j, (Pi.single (M := A) j 1) = 1 := by
  classical
  exact (CompleteOrthogonalIdempotents.single A).complete

theorem single_mul_single_eq_zero (j l : Fin m) (hjl : j ≠ l) :
    Pi.single (M := A) j 1 * Pi.single (M := A) l 1 = 0 := by
  classical
  exact (CompleteOrthogonalIdempotents.single A).ortho hjl

end Idempotents

end AlgebraicGeometry.Polarisation.EtaleAbsorb

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.Hom.app_smul Surjective Scheme.Hom.iSup_preimage_eq_top Scheme.Modules.pushforward Scheme.Modules.pullback Scheme.Hom Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Modules.restrictFunctor Scheme.Modules.Hom.id_app Scheme.Modules.restrictAdjunction IsOpenImmersion Scheme.Hom.comp_appTop Flat Scheme.Hom.opensRange_of_isIso Scheme.Modules.pullbackCongr Spec.map_id Etale Scheme.Modules.pullbackPushforwardAdjunction Scheme.Hom.opensRange_comp_of_isIso Scheme.Modules Scheme.Hom.opensRange_pullbackFst Scheme.Hom.preimage_bot Scheme.Modules.pullbackComp Scheme.ΓSpecIso Polarisation.ThetaPt PolarisedAbelianScheme Scheme.Modules.pullbackLocalSection Scheme.Modules.pullbackLocalSection_def Scheme.Modules.pullbackLocalSection_add Scheme.Modules.pullbackLocalSection_sum Scheme.Modules.pullbackLocalSection_smul Polarisation.ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one"
namespace Polarisation
p2m_export "AlgebraicGeometry.Polarisation" "ThetaPt.ofUnit ThetaPt.ofScalar ThetaPt baseScalar SchrodingerFrame ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback"
namespace TA
p2m_open "AlgebraicGeometry.Polarisation AlgebraicGeometry"

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
  (𝓛 : A.Modules) {R R' : Type} [CommRing R] [CommRing R']
  (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (t' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S))
  (ψ : R →+* R') (hr : Spec.map (CommRingCat.ofHom ψ) ≫ t = t')

def b : pullback f t' ⟶ pullback f t :=
  pullback.lift (pullback.fst f t' ≫ 𝟙 A) (pullback.snd f t' ≫ Spec.map (CommRingCat.ofHom ψ)) (by
    rw [Category.assoc, Category.id_comp, pullback.condition, Category.assoc, hr])

theorem b_fst : b f t t' ψ hr ≫ pullback.fst f t = pullback.fst f t' ≫ 𝟙 A := pullback.lift_fst _ _ _

theorem b_fst' : b f t t' ψ hr ≫ pullback.fst f t = pullback.fst f t' := by rw [b_fst, Category.comp_id]

theorem b_snd : b f t t' ψ hr ≫ pullback.snd f t = pullback.snd f t' ≫ Spec.map (CommRingCat.ofHom ψ) :=
  pullback.lift_snd _ _ _

def c : (Scheme.Modules.pullback (b f t t' ψ hr)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
    (Scheme.Modules.pullback (pullback.fst f t')).obj 𝓛 :=
  (Scheme.Modules.pullbackComp (b f t t' ψ hr) _).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr (b_fst' f t t' ψ hr)).app 𝓛

theorem isPullback_id : IsPullback (𝟙 A) f f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
  rw [CommRingCat.ofHom_id, Spec.map_id]
  exact IsPullback.id_horiz f

theorem mul_congr_base {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (x y : SchemeHomOver t₁ f) :
    (L.mul t₁ x y).1 = (L.mul t₂ ⟨x.1, h ▸ x.2⟩ ⟨y.1, h ▸ y.2⟩).1 := by
  subst h; rfl

theorem hmul_id {T : Scheme.{0}} (t'' : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t'' f) :
    (L.mul t'' x y).1 ≫ 𝟙 A =
      (L.mul (t'' ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)))
        ⟨x.1 ≫ 𝟙 A, by rw [Category.assoc, (isPullback_id f).w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ 𝟙 A, by rw [Category.assoc, (isPullback_id f).w, ← Category.assoc, y.2]⟩).1 := by
  have ht : t'' = t'' ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  rw [Category.comp_id, mul_congr_base f L ht x y]
  congr 2 <;> exact Subtype.ext (Category.comp_id _).symm

include hr in
theorem hr' : Spec.map (CommRingCat.ofHom ψ) ≫ t = t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)) := by
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, hr]

theorem exists_monoidHom_transport :
    ∃ β : ThetaPt f L 𝓛 t →* ThetaPt f L 𝓛 t',
      (∀ θ, (β θ).pt.1 = Spec.map (CommRingCat.ofHom ψ) ≫ θ.pt.1) ∧
      (∀ θ (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)),
        (β θ).act ((c f 𝓛 t t' ψ hr).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b f t t' ψ hr) s :
            Γ((Scheme.Modules.pullback (b f t t' ψ hr)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) =
          (c f 𝓛 t t' ψ hr).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b f t t' ψ hr) (θ.act s) :
            Γ((Scheme.Modules.pullback (b f t t' ψ hr)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) ∧
      (∀ v : Rˣ, β (ThetaPt.ofScalar v) = ThetaPt.ofScalar (Units.map (ψ : R →* R') v)) ∧
      (∀ w : Γ(pullback f t, ⊤)ˣ,
        β (ThetaPt.ofUnit w) = ThetaPt.ofUnit (Units.map ((b f t t' ψ hr).appTop.hom : _ →* _) w)) := by
  obtain ⟨β, h1, h2, h3, h4⟩ := ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback (RingHom.id S) L L (𝟙 A)
    (isPullback_id f) (fun t'' x y => hmul_id f L t'' x y) 𝓛 𝓛 t t' ψ (hr' t t' ψ hr)
    (b f t t' ψ hr) (b_fst f t t' ψ hr) (b_snd f t t' ψ hr) (c f 𝓛 t t' ψ hr)
  refine ⟨β, fun θ => ?_, h2, h3, h4⟩
  have := h1 θ
  rwa [Category.comp_id] at this

theorem hr_algebraMap (R R' : Type) [CommRing R] [CommRing R'] [Algebra S R] [Algebra S R'] [Algebra R R']
    [IsScalarTower S R R'] :
    Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ Spec.map (CommRingCat.ofHom (algebraMap S R)) =
      Spec.map (CommRingCat.ofHom (algebraMap S R')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

end AlgebraicGeometry.Polarisation.TA

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.Hom.app_smul Surjective Scheme.Hom.iSup_preimage_eq_top Scheme.Modules.pushforward Scheme.Modules.pullback Scheme.Hom Scheme.Hom.preimage_inf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Modules.restrictFunctor Scheme.Modules.Hom.id_app Scheme.Modules.restrictAdjunction IsOpenImmersion Scheme.Hom.comp_appTop Flat Scheme.Hom.opensRange_of_isIso Scheme.Modules.pullbackCongr Spec.map_id Etale Scheme.Modules.pullbackPushforwardAdjunction Scheme.Hom.opensRange_comp_of_isIso Scheme.Modules Scheme.Hom.opensRange_pullbackFst Scheme.Hom.preimage_bot Scheme.Modules.pullbackComp Scheme.ΓSpecIso Polarisation.ThetaPt PolarisedAbelianScheme Scheme.Modules.pullbackLocalSection Scheme.Modules.pullbackLocalSection_def Scheme.Modules.pullbackLocalSection_add Scheme.Modules.pullbackLocalSection_sum Scheme.Modules.pullbackLocalSection_smul Polarisation.ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one"
namespace Polarisation
p2m_export "AlgebraicGeometry.Polarisation" "ThetaPt.ofUnit ThetaPt.ofScalar ThetaPt baseScalar SchrodingerFrame ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback"
namespace EtaleAbsorb
p2m_open "AlgebraicGeometry.Polarisation AlgebraicGeometry"

section Single

variable {X : Scheme.{0}} (M : X.Modules) {Y : Scheme.{0}} (b : Y ⟶ X) [IsOpenImmersion b] {N : Y.Modules}
  (c : (Scheme.Modules.pullback b).obj M ≅ N)

include c in
theorem iSup_opensRange_const (hb : b.opensRange = ⊤) : ⨆ _ : Unit, b.opensRange = ⊤ := by
  rw [iSup_const]; exact hb

theorem eq_of_chartMap_eq (hb : b.opensRange = ⊤) (s s' : Γ(M, ⊤)) (h : chartMap M b c s = chartMap M b c s') :
    s = s' :=
  eq_of_forall_chartMap_eq M (fun _ : Unit => b) (N := fun _ => N) (fun _ => c) (iSup_opensRange_const M b c hb) s s'
    (fun _ => h)

theorem exists_chartMap_eq (hb : b.opensRange = ⊤) (v : Γ(N, ⊤)) : ∃ s : Γ(M, ⊤), chartMap M b c s = v := by
  obtain ⟨s, hs⟩ := exists_forall_chartMap_eq M (fun _ : Unit => b) (N := fun _ => N) (fun _ => c)
    (iSup_opensRange_const M b c hb) (fun i j hij => absurd (Subsingleton.elim i j) hij) (fun _ => v)
  exact ⟨s, hs ()⟩

end Single

section TransportIso

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
  {R R' : Type} [CommRing R] [CommRing R'] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (ψ : R ≃+* R')

theorem specMap_symm_comp :
    Spec.map (CommRingCat.ofHom ψ.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) =
      𝟙 (Spec (CommRingCat.of R)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingEquiv.symm_toRingHom_comp_toRingHom, CommRingCat.ofHom_id,
    Spec.map_id]

theorem specMap_comp_symm :
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Spec.map (CommRingCat.ofHom ψ.symm.toRingHom) =
      𝟙 (Spec (CommRingCat.of R')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingEquiv.toRingHom_comp_symm_toRingHom, CommRingCat.ofHom_id,
    Spec.map_id]

def binv : pullback f t ⟶ pullback f (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) :=
  pullback.lift (pullback.fst f t) (pullback.snd f t ≫ Spec.map (CommRingCat.ofHom ψ.symm.toRingHom)) (by
    rw [Category.assoc, ← Category.assoc (Spec.map (CommRingCat.ofHom ψ.symm.toRingHom)), specMap_symm_comp,
      Category.id_comp]
    exact pullback.condition)

theorem binv_fst : binv f t ψ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) = pullback.fst f t := pullback.lift_fst _ _ _

theorem binv_snd : binv f t ψ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) =
    pullback.snd f t ≫ Spec.map (CommRingCat.ofHom ψ.symm.toRingHom) := pullback.lift_snd _ _ _

scoped instance isIso_b : IsIso (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) := by
  refine ⟨⟨binv f t ψ, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, binv_fst, TA.b_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, binv_snd, ← Category.assoc, TA.b_snd, Category.assoc, specMap_comp_symm, Category.comp_id,
        Category.id_comp]
  · apply pullback.hom_ext
    · rw [Category.assoc, TA.b_fst, Category.comp_id, binv_fst, Category.id_comp]
    · rw [Category.assoc, TA.b_snd, ← Category.assoc, binv_snd, Category.assoc, specMap_symm_comp, Category.comp_id,
        Category.id_comp]

end TransportIso

theorem nonempty_schrodingerFrame_of_ringEquiv
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules) {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)]
    {R R' : Type} [CommRing R] [CommRing R']
    (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (t' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S))
    (ψ : R ≃+* R') (hψ : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t = t')
    (F : SchrodingerFrame f L 𝓛 t δ) : Nonempty (SchrodingerFrame f L 𝓛 t' δ) := by
  classical
  subst hψ
  have hcov : (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl).opensRange = ⊤ := Scheme.Hom.opensRange_of_isIso _
  obtain ⟨β, -, hβ, -, -⟩ := TA.exists_monoidHom_transport f L 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl

  have ρ_inj := eq_of_chartMap_eq ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) hcov
  have ρ_surj := exists_chartMap_eq ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) hcov
  have ρ_smul : ∀ (x : R) (s : Γ(((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤)),
      chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (baseScalar f t x • s) =
        baseScalar f (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) (ψ.toRingHom x) • chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) s := by
    intro x s
    rw [chartMap_smul, appTop_baseScalar f t _ ψ.toRingHom (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.b_snd f t _ ψ.toRingHom rfl)]
  have ρ_sum : ∀ s : ((i : Fin g) → ZMod (δ i)) → Γ(((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤),
      chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (∑ h, s h) = ∑ h, chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (s h) :=
    fun s => chartMap_sum ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) Finset.univ s
  have hψψ : ∀ y : R', ψ.toRingHom (ψ.symm y) = y := fun y => ψ.apply_symm_apply y
  have hχ : ∀ (χ' : AddChar ((i : Fin g) → ZMod (δ i)) R') h,
      ψ.toRingHom ((ψ.symm.toRingHom.toMonoidHom.compAddChar χ') h) = χ' h := fun χ' h => ψ.apply_symm_apply (χ' h)

  have ρΦ : ∀ cf : ((i : Fin g) → ZMod (δ i)) → R,
      chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (∑ h, baseScalar f t (cf h) • F.σ h) =
        ∑ h, baseScalar f (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) (ψ.toRingHom (cf h)) • chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (F.σ h) := by
    intro cf
    rw [ρ_sum]
    exact Finset.sum_congr rfl fun h _ => by rw [ρ_smul]
  refine ⟨{ σ := fun h => chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (F.σ h)
            basis := ?_
            lift := fun h => β (F.lift h)
            dualLift := fun χ' => β (F.dualLift (ψ.symm.toRingHom.toMonoidHom.compAddChar χ'))
            lift_act := ?_
            dualLift_act := ?_ }⟩
  ·
    constructor
    · intro c₁ c₂ h12
      have h12' : ∑ h, baseScalar f (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) (c₁ h) • chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (F.σ h) =
          ∑ h, baseScalar f (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) (c₂ h) • chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (F.σ h) := h12
      have e : ∀ c' : ((i : Fin g) → ZMod (δ i)) → R', ∑ h, baseScalar f (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) (c' h) • chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (F.σ h) =
          chartMap ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (∑ h, baseScalar f t (ψ.symm (c' h)) • F.σ h) := by
        intro c'
        rw [ρΦ]
        exact Finset.sum_congr rfl fun h _ => by rw [hψψ]
      rw [e, e] at h12'
      have h3 := F.basis.1 (ρ_inj _ _ h12')
      funext h
      have h4 : ψ.symm (c₁ h) = ψ.symm (c₂ h) := congrFun h3 h
      simpa using congrArg ψ h4
    · intro s'
      obtain ⟨s, hs⟩ := ρ_surj s'
      obtain ⟨cf, hcf⟩ := F.basis.2 s
      refine ⟨fun h => ψ.toRingHom (cf h), ?_⟩
      have hcf' : ∑ h, baseScalar f t (cf h) • F.σ h = s := hcf
      rw [← hs, ← hcf', ρΦ]
  ·
    intro h h'
    rw [chartMap_def, chartMap_def, hβ, F.lift_act]
  ·
    intro χ' h
    rw [chartMap_def, hβ, F.dualLift_act,
      ← chartMap_def ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl)
        (baseScalar f t ((ψ.symm.toRingHom.toMonoidHom.compAddChar χ') h) • F.σ h),
      ← chartMap_def ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) (TA.b f t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (TA.c f 𝓛 t (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ t) ψ.toRingHom rfl) (F.σ h), ρ_smul, hχ]

end AlgebraicGeometry.Polarisation.EtaleAbsorb
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover.AlgebraicGeometry P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover.AlgebraicGeometry.Polarisation P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover.AlgebraicGeometry.Polarisation.EtaleAbsorb"
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover.AlgebraicGeometry P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover.AlgebraicGeometry.Polarisation"
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover.AlgebraicGeometry"

open AlgebraicGeometry.Polarisation.EtaleAbsorb

theorem solution
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)]
    {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    (S₁ : Type) [CommRing S₁] [Algebra S S₁] [Module.FaithfullyFlat S S₁] [Algebra.Etale S S₁]
    (m : ℕ) (r : Fin m → S₁) (hr : Ideal.span (Set.range r) = ⊤)
    (F : ∀ j : Fin m, SchrodingerFrame u.f u.L u.pol (Spec.map (CommRingCat.ofHom ((algebraMap S₁ (Localization.Away (r j))).comp (algebraMap S S₁)))) δ) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧ Algebra.Etale S S' ∧
      Nonempty (SchrodingerFrame u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap S S'))) δ) := by
  classical
  obtain ⟨hff, het⟩ := faithfullyFlat_and_etale_pi_away (S := S) S₁ r hr
  refine ⟨(Π j, Localization.Away (r j)), inferInstance, inferInstance, hff, het, ?_⟩

  let e : Fin m → (Π j, Localization.Away (r j)) := fun j => Pi.single j 1

  have F' : ∀ j, Nonempty (SchrodingerFrame u.f u.L u.pol
      (Spec.map (CommRingCat.ofHom (algebraMap (Π j, Localization.Away (r j)) (Localization.Away (e j)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (Π j, Localization.Away (r j))))) δ) := by
    intro j
    obtain ⟨ψ, hψ⟩ := exists_ringEquiv_away_comp_eq (S := S) S₁ r j
    refine nonempty_schrodingerFrame_of_ringEquiv u.f u.L u.pol δ _ _ ψ ?_ (F j)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) hψ

  exact nonempty_schrodingerFrame_of_isIdempotentElem_of_sum_eq_one u.f u.L u.pol δ _ e
    (isIdempotentElem_single _) (sum_single_eq_one _) (single_mul_single_eq_zero _) fun j => (F' j).some

end
end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_schrodingerFrame_of_cover (solution)
