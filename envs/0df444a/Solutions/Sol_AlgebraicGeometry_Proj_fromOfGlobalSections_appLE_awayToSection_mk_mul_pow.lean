-- Prove2me | solution 1 for AlgebraicGeometry.Proj.fromOfGlobalSections_appLE_awayToSection_mk_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/a6be9e41-2061-52ac-9ee2-45ee22fe35e9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Proj_fromOfGlobalSections_appLE_awayToSection_mk_mul_pow

universe u v

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace K10E1

theorem eq_of_toSpecΓ_comp_eq {X : Scheme.{u}} (U : X.Opens) {B : CommRingCat.{u}}
    (φ₁ φ₂ : B ⟶ Γ(X, U)) (h : U.toSpecΓ ≫ Spec.map φ₁ = U.toSpecΓ ≫ Spec.map φ₂) : φ₁ = φ₂ := by
  have h1 := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop] at h1
  have h2 : (Spec.map φ₁).appTop ≫ (Scheme.ΓSpecIso Γ(X, U)).hom =
      (Spec.map φ₂).appTop ≫ (Scheme.ΓSpecIso Γ(X, U)).hom := by
    have := congrArg (fun q => q ≫ U.topIso.hom) h1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using this
  rw [Scheme.ΓSpecIso_naturality, Scheme.ΓSpecIso_naturality] at h2
  exact (cancel_epi _).1 h2

end K10E1

open K10E1 in
theorem solution
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X : Scheme.{u}} (g : A →+* Γ(X, ⊤)) (hg : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g = ⊤)
    {n : ℕ} (hn : 0 < n) {r : A} (hr : r ∈ 𝒜 n) (k : ℕ) (s : A) (hs : s ∈ 𝒜 (k • n)) :
    (Proj.fromOfGlobalSections 𝒜 g hg).appLE (Proj.basicOpen 𝒜 r) (X.basicOpen (g r))
        (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 g hg hn hr).ge
        (Proj.awayToSection 𝒜 r (Away.mk 𝒜 hr k s hs)) *
      X.presheaf.map (homOfLE (X.basicOpen_le (g r))).op (g r) ^ k =
    X.presheaf.map (homOfLE (X.basicOpen_le (g r))).op (g s) := by
  classical
  set D : X.Opens := X.basicOpen (g r) with hD

  set ρ : Γ(X, ⊤) →+* Γ(X, D) := (X.presheaf.map (homOfLE (X.basicOpen_le (g r))).op).hom with hρ
  have hu : IsUnit (ρ (g r)) := by
    rw [hρ]
    exact RingedSpace.isUnit_res_basicOpen _ (g r)

  set β : Localization.Away (g r) →+* Γ(X, D) := IsLocalization.Away.lift (g r) hu with hβ
  have hgr : Submonoid.powers r ≤ (Submonoid.powers (g r)).comap g := by
    rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]
  set ψ : Away 𝒜 r →+* Localization.Away (g r) :=
    (IsLocalization.map (M := Submonoid.powers r) (T := Submonoid.powers (g r))
      (Localization.Away (g r)) g hgr).comp (algebraMap (Away 𝒜 r) (Localization.Away r)) with hψ

  have key : Proj.awayToSection 𝒜 r ≫ (Proj.fromOfGlobalSections 𝒜 g hg).appLE (Proj.basicOpen 𝒜 r) D
        (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 g hg hn hr).ge =
      CommRingCat.ofHom (β.comp ψ) := by
    apply eq_of_toSpecΓ_comp_eq

    rw [Spec.map_comp, ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE,
      Proj.fromOfGlobalSections_resLE 𝒜 g hg hn hr, Category.assoc]
    change Proj.toBasicOpenOfGlobalSections 𝒜 g rfl hn hr ≫ Proj.basicOpenToSpec 𝒜 r = _
    rw [← Proj.basicOpenIsoSpec_hom 𝒜 r hr hn]
    simp only [Proj.toBasicOpenOfGlobalSections, Category.assoc, Iso.inv_hom_id, Category.comp_id]

    have Q : D.toSpecΓ ≫ Spec.map (CommRingCat.ofHom β) =
        (X.isoOfEq (X.toSpecΓ_preimage_basicOpen (g r))).inv ≫
          X.toSpecΓ ∣_ PrimeSpectrum.basicOpen (g r) ≫ (basicOpenIsoSpecAway (g r)).hom := by
      rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away (g r)))))]
      simp only [Category.assoc, basicOpenIsoSpecAway, IsOpenImmersion.isoOfRangeEq_hom_fac,
        morphismRestrict_ι, Scheme.isoOfEq_inv_ι_assoc]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hβ, IsLocalization.Away.lift_comp]
      exact Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top D
    conv_rhs => rw [hψ, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [reassoc_of% Q]

  have hmem : g (r ^ k) ∈ Submonoid.powers (g r) := by
    rw [map_pow]; exact pow_mem (Submonoid.mem_powers _) k
  have key' := congrArg (fun φ : CommRingCat.of (Away 𝒜 r) ⟶ Γ(X, D) => φ (Away.mk 𝒜 hr k s hs)) key
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at key'
  have hψv : ψ (Away.mk 𝒜 hr k s hs) =
      IsLocalization.mk' (Localization.Away (g r)) (g s) ⟨g (r ^ k), hmem⟩ := by
    rw [hψ, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk,
      Localization.mk_eq_mk', IsLocalization.map_mk']
  rw [key', hψv]
  change β _ * ρ (g r) ^ k = ρ (g s)
  have e2 : β (IsLocalization.mk' (Localization.Away (g r)) (g s) ⟨g (r ^ k), hmem⟩) * ρ (g (r ^ k)) =
      ρ (g s) := by
    have e1 := IsLocalization.mk'_spec (Localization.Away (g r)) (g s) ⟨g (r ^ k), hmem⟩
    have := congrArg β e1
    rwa [map_mul, hβ, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at this
  have e3 : ρ (g (r ^ k)) = ρ (g r) ^ k := by rw [map_pow, map_pow]
  rw [e3] at e2
  exact e2

end S_AlgebraicGeometry_Proj_fromOfGlobalSections_appLE_awayToSection_mk_mul_pow
end P2MW
export P2MW.S_AlgebraicGeometry_Proj_fromOfGlobalSections_appLE_awayToSection_mk_mul_pow (solution)
