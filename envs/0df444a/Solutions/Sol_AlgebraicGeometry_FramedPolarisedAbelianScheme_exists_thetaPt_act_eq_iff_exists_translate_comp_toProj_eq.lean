-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_thetaPt_act_eq_iff_exists_translate_comp_toProj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d8dbea71-3e05-517b-b994-9604e3a38d4c

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_iso_forall_app_eq_of_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_thetaPt_act_eq_iff_exists_translate_comp_toProj_eq
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

open Opposite

universe u

namespace PPofIso

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M M' : X.Modules} {N : ℕ}

theorem app_map (φ : M ⟶ M') {V V' : X.Opens} (hle : V' ≤ V) (x : Γ(M, V)) :
    M'.presheaf.map (homOfLE hle).op (φ.app V x) = φ.app V' (M.presheaf.map (homOfLE hle).op x) := by
  have := φ.mapPresheaf.naturality (homOfLE hle).op
  have e := congrArg (fun f => f x) this
  simpa using e.symm

theorem app_bijective (φ : M ≅ M') (V : X.Opens) : Function.Bijective (φ.hom.app V) := by
  have h1 : ∀ x, φ.inv.app V (φ.hom.app V x) = x := fun x => by
    have e := congrArg (fun g : M ⟶ M => g.app V x) φ.hom_inv_id
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at e
    exact e
  have h2 : ∀ y, φ.hom.app V (φ.inv.app V y) = y := fun y => by
    have e := congrArg (fun g : M' ⟶ M' => g.app V y) φ.inv_hom_id
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at e
    exact e
  exact ⟨fun a b hab => by rw [← h1 a, ← h1 b, hab], fun y => ⟨_, h2 y⟩⟩

noncomputable def ofIso (𝔓 : Scheme.Modules.ProjPresentation M f N) (φ : M ≅ M') :
    Scheme.Modules.ProjPresentation M' f N where
  σ i := φ.hom.app ⊤ (𝔓.σ i)
  toProj := 𝔓.toProj
  toProj_π := 𝔓.toProj_π
  frame i V hV := by
    have key : (fun g : Γ(X, V) => g • (M'.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (φ.hom.app ⊤ (𝔓.σ i)) : Γ(M', V))) =
        (φ.hom.app V) ∘ (fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (𝔓.σ i) : Γ(M, V))) := by
      funext g
      simp only [Function.comp_apply, app_map, Scheme.Modules.Hom.app_smul]
    rw [key]
    exact (app_bijective φ V).comp (𝔓.frame i V hV)
  app_ratio_smul i j := by
    rw [app_map, app_map, ← Scheme.Modules.Hom.app_smul, 𝔓.app_ratio_smul i j]

theorem exists_of_iso (𝔓 : Scheme.Modules.ProjPresentation M f N) (φ : M ≅ M') :
    ∃ 𝔔 : Scheme.Modules.ProjPresentation M' f N, (∀ i, 𝔔.σ i = φ.hom.app ⊤ (𝔓.σ i)) ∧ 𝔔.toProj = 𝔓.toProj :=
  ⟨ofIso 𝔓 φ, fun _ => rfl, rfl⟩

end PPofIso

namespace F2Sol

theorem toProj_eq_of_sigma_eq {S : Type u} [CommRing S] {A : Scheme.{u}} {f g : A ⟶ Spec (CommRingCat.of S)} (hfg : g = f)
    {L : A.Modules} {N : ℕ} (P1 : Scheme.Modules.ProjPresentation L g N) (P2 : Scheme.Modules.ProjPresentation L f N)
    (h : ∀ i, P1.σ i = P2.σ i) : P1.toProj = P2.toProj := by
  subst hfg
  exact AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq_univ P1 P2 h

theorem exists_iso_of_toProj_eq {S : Type u} [CommRing S] {A : Scheme.{u}} {f g : A ⟶ Spec (CommRingCat.of S)} (hfg : g = f)
    {L L' : A.Modules} {N : ℕ} (P1 : Scheme.Modules.ProjPresentation L g N) (P2 : Scheme.Modules.ProjPresentation L' f N)
    (h : P1.toProj = P2.toProj) : ∃ φ : L ≅ L', ∀ i : Fin (N + 1), φ.hom.app ⊤ (P1.σ i) = P2.σ i := by
  subst hfg
  exact AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_iso_forall_app_eq_of_toProj_eq P1 P2 h

theorem main
    {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (P' : Scheme.Modules.ProjPresentation X.pol X.f N) :
    (∃ θ : ThetaPt X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))), ∀ i : Fin (N + 1),
        θ.act (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i) :
            Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol, ⊤)) =
          (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (P'.σ i) :
            Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
              (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤))) ↔
    (∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) X.f,
        Polarisation.translate X.f X.L (𝟙 (Spec (CommRingCat.of S))) x ≫ pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫
            X.frame.toProj =
          pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫ P'.toProj) := by
  classical

  obtain ⟨PT, hPTσ, hPTπ⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq
    (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) X.frame
  obtain ⟨Q, hQσ, hQπ⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq
    (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) P'

  have hbase : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) X.f,
      Polarisation.translate X.f X.L (𝟙 _) x ≫ (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫ X.f) =
        pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫ X.f := fun x => by
    rw [pullback.condition, ← Category.assoc, Polarisation.translate_snd]
  constructor
  · rintro ⟨θ, hθ⟩
    obtain ⟨Pτ, hPτσ, hPτπ⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq
      (Polarisation.translate X.f X.L (𝟙 _) θ.pt) PT
    obtain ⟨Pψ, hPψσ, hPψπ⟩ := PPofIso.exists_of_iso Pτ θ.iso
    have hσ : ∀ i, Pψ.σ i = Q.σ i := fun i => by
      rw [hPψσ, hPτσ, hPTσ, hQσ]
      exact hθ i
    have e := toProj_eq_of_sigma_eq (hbase θ.pt) Pψ Q hσ
    rw [hPψπ, hPτπ, hPTπ, hQπ] at e
    exact ⟨θ.pt, e⟩
  · rintro ⟨x, hx⟩
    obtain ⟨Pτ, hPτσ, hPτπ⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq
      (Polarisation.translate X.f X.L (𝟙 _) x) PT
    have hπ : Pτ.toProj = Q.toProj := by rw [hPτπ, hPTπ, hQπ]; exact hx
    obtain ⟨ψ, hψ⟩ := exists_iso_of_toProj_eq (hbase x) Pτ Q hπ
    refine ⟨⟨x, ψ⟩, fun i => ?_⟩
    show ψ.hom.app _ (Scheme.Modules.pullbackLocalSection (Polarisation.translate X.f X.L (𝟙 _) x)
      (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i))) = _
    have := hψ i
    rw [hPτσ, hPTσ, hQσ] at this
    exact this

end F2Sol

theorem solution
    {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (P' : Scheme.Modules.ProjPresentation X.pol X.f N) :
    (∃ θ : ThetaPt X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))), ∀ i : Fin (N + 1),
        θ.act (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i) :
            Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol, ⊤)) =
          (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (P'.σ i) :
            Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
              (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤))) ↔
    (∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) X.f,
        Polarisation.translate X.f X.L (𝟙 (Spec (CommRingCat.of S))) x ≫ pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫
            X.frame.toProj =
          pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫ P'.toProj) :=
  F2Sol.main X P'

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_thetaPt_act_eq_iff_exists_translate_comp_toProj_eq
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_thetaPt_act_eq_iff_exists_translate_comp_toProj_eq (solution)
