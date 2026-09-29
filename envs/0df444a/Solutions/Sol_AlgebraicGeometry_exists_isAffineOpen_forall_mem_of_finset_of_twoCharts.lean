-- Prove2me | solution 1 for AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_finset_of_twoCharts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8691d792-fc22-5f5c-9f82-5e65b356dfb8

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_finset_of_twoCharts

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_finset_of_twoCharts.AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι IsAffineOpen.isoSpec_inv_toSpecΓ_assoc Spec.map_comp_assoc Proj.opensRange_awayι Scheme.Hom Scheme.Hom.preimage_inf SpecMap_preimage_basicOpen IsAffineOpen.fromSpec_top isAffineHom_of_forall_exists_isAffineOpen Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc IsAffineOpen.isoSpec_inv_ι isPullback_opens_inf IsAffineOpen.isoSpec_hom IsAffineOpen.SpecMap_appLE_fromSpec IsAffineOpen.fromSpec_preimage_self Spec Spec.map Proj.basicOpenToSpec Scheme Proj.awayι Scheme.Hom.preimage_opensRange Scheme.isoSpec_Spec_inv Proj Spec.map_injective Proj.awayι_preimage_basicOpen isAffineOpen_top Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc IsAffineOpen Scheme.Opens Scheme.Hom.appLE_map Scheme.Cover.hom_ext Proj.iSup_basicOpen_eq_top Proj.SpecMap_awayMap_awayι Scheme.Hom.comp_preimage IsAffineHom Proj.awayToSection Proj.basicOpenIsoSpec_hom toSpecΓ Scheme.Cover Scheme.ΓSpecIso ProjSpace.irrelevant_le_span_X ProjSpace.X_mem_one exists_isAffineOpen_forall_mem_of_isAffineHom_proj"
namespace TwoChartHomProj
p2m_open "AlgebraicGeometry"

open HomogeneousLocalization

section AwayDesc

variable {A B : Type*} [CommRing A] [CommRing B] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

noncomputable def awayDesc (χ : A →+* B) (x : A) (v : B) (hv : χ x * v = 1) :
    HomogeneousLocalization.Away 𝒜 x →+* B :=
  (Localization.awayLift χ x (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)).comp
    (algebraMap (HomogeneousLocalization.Away 𝒜 x) (Localization.Away x))

theorem awayDesc_mk (χ : A →+* B) (x : A) (v : B) (hv : χ x * v = 1) {d : ℕ} (hx : x ∈ 𝒜 d)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayDesc 𝒜 χ x v hv (Away.mk 𝒜 hx n a ha) = χ a * v ^ n := by
  simp only [awayDesc, RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  exact Localization.awayLift_mk χ x a v hv n

theorem awayDesc_fromZeroRingHom (χ : A →+* B) (x : A) (v : B) (hv : χ x * v = 1) (a : 𝒜 0) :
    awayDesc 𝒜 χ x v hv (fromZeroRingHom 𝒜 _ a) = χ a := by
  simp only [awayDesc, RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
    fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, val_mk]
  change Localization.awayLift χ x _ (Localization.mk (a : A) 1) = χ a
  rw [Localization.mk_one_eq_algebraMap]
  exact IsLocalization.lift_eq _ _

end AwayDesc

theorem eval₂_smul_of_isHomogeneous {R S : Type*} [CommSemiring R] [CommSemiring S] {τ : Type*}
    {φ : MvPolynomial τ R} {n : ℕ} (hφ : φ.IsHomogeneous n) (i : R →+* S) (u : S) (v : τ → S) :
    MvPolynomial.eval₂ i (u • v) φ = u ^ n * MvPolynomial.eval₂ i v φ := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← hφ.degree_eq_sum_deg_support hd]
  ring

section Charts

variable {R : Type u} [CommRing R] {B : Type u} [CommRing B]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) R

attribute [local instance] MvPolynomial.gradedAlgebra

theorem X_mem (j : Fin 2) : (MvPolynomial.X j : MvPolynomial (Fin 2) R) ∈ 𝒜 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R j)

theorem X_mul_X_mem : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) R) ∈ 𝒜 2 :=
  SetLike.mul_mem_graded (X_mem 0) (X_mem 1)

noncomputable def χ₀ (i : R →+* B) (f : B) : MvPolynomial (Fin 2) R →+* B := MvPolynomial.eval₂Hom i ![1, f]

noncomputable def χ₁ (i : R →+* B) (g : B) : MvPolynomial (Fin 2) R →+* B := MvPolynomial.eval₂Hom i ![g, 1]

@[scoped simp] theorem χ₀_X_zero (i : R →+* B) (f : B) : χ₀ i f (MvPolynomial.X 0) = 1 := by simp [χ₀]
@[scoped simp] theorem χ₀_X_one (i : R →+* B) (f : B) : χ₀ i f (MvPolynomial.X 1) = f := by simp [χ₀]
@[scoped simp] theorem χ₁_X_zero (i : R →+* B) (g : B) : χ₁ i g (MvPolynomial.X 0) = g := by simp [χ₁]
@[scoped simp] theorem χ₁_X_one (i : R →+* B) (g : B) : χ₁ i g (MvPolynomial.X 1) = 1 := by simp [χ₁]
@[scoped simp] theorem χ₀_C (i : R →+* B) (f : B) (r : R) : χ₀ i f (MvPolynomial.C r) = i r := by simp [χ₀]
@[scoped simp] theorem χ₁_C (i : R →+* B) (g : B) (r : R) : χ₁ i g (MvPolynomial.C r) = i r := by simp [χ₁]

theorem comp_χ₀ {B' : Type u} [CommRing B'] (ρ : B →+* B') (i : R →+* B) (f : B) :
    ρ.comp (χ₀ i f) = χ₀ (ρ.comp i) (ρ f) := by
  refine MvPolynomial.ringHom_ext (fun r => by simp) (fun j => ?_)
  fin_cases j <;> simp

theorem comp_χ₁ {B' : Type u} [CommRing B'] (ρ : B →+* B') (i : R →+* B) (g : B) :
    ρ.comp (χ₁ i g) = χ₁ (ρ.comp i) (ρ g) := by
  refine MvPolynomial.ringHom_ext (fun r => by simp) (fun j => ?_)
  fin_cases j <;> simp

theorem χ₁_eq_of_mem (i : R →+* B) (f g : B) (hfg : f * g = 1) {n : ℕ} {a : MvPolynomial (Fin 2) R}
    (ha : a ∈ 𝒜 n) : χ₁ i g a = g ^ n * χ₀ i f a := by
  have hv : (![g, 1] : Fin 2 → B) = g • ![1, f] := by
    funext j; fin_cases j <;> simp [mul_comm f g ▸ hfg]
  change MvPolynomial.eval₂ i ![g, 1] a = g ^ n * MvPolynomial.eval₂ i ![1, f] a
  rw [hv]
  exact eval₂_smul_of_isHomogeneous ((MvPolynomial.mem_homogeneousSubmodule n a).mp ha) i g _

noncomputable def ψ₀ (i : R →+* B) (f : B) : Away 𝒜 (MvPolynomial.X 0) →+* B :=
  awayDesc 𝒜 (χ₀ i f) (MvPolynomial.X 0) 1 (by simp)

noncomputable def ψ₁ (i : R →+* B) (g : B) : Away 𝒜 (MvPolynomial.X 1) →+* B :=
  awayDesc 𝒜 (χ₁ i g) (MvPolynomial.X 1) 1 (by simp)

noncomputable def θ (i : R →+* B) (f g : B) (hfg : f * g = 1) :
    Away 𝒜 (MvPolynomial.X 0 * MvPolynomial.X 1) →+* B :=
  awayDesc 𝒜 (χ₀ i f) (MvPolynomial.X 0 * MvPolynomial.X 1) g (by simpa using hfg)

theorem ψ₀_mk (i : R →+* B) (f : B) (n : ℕ) (a : MvPolynomial (Fin 2) R) (ha : a ∈ 𝒜 (n • 1)) :
    ψ₀ i f (Away.mk 𝒜 (X_mem 0) n a ha) = χ₀ i f a := by
  simp [ψ₀, awayDesc_mk]

theorem ψ₁_mk (i : R →+* B) (g : B) (n : ℕ) (a : MvPolynomial (Fin 2) R) (ha : a ∈ 𝒜 (n • 1)) :
    ψ₁ i g (Away.mk 𝒜 (X_mem 1) n a ha) = χ₁ i g a := by
  simp [ψ₁, awayDesc_mk]

theorem θ_mk (i : R →+* B) (f g : B) (hfg : f * g = 1) (n : ℕ) (a : MvPolynomial (Fin 2) R)
    (ha : a ∈ 𝒜 (n • 2)) :
    θ i f g hfg (Away.mk 𝒜 X_mul_X_mem n a ha) = χ₀ i f a * g ^ n :=
  awayDesc_mk ..

theorem comp_ψ₀ {B' : Type u} [CommRing B'] (ρ : B →+* B') (i : R →+* B) (f : B) :
    ρ.comp (ψ₀ i f) = ψ₀ (ρ.comp i) (ρ f) := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (X_mem 0) z
  simp [ψ₀_mk, ← comp_χ₀]

theorem comp_ψ₁ {B' : Type u} [CommRing B'] (ρ : B →+* B') (i : R →+* B) (g : B) :
    ρ.comp (ψ₁ i g) = ψ₁ (ρ.comp i) (ρ g) := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (X_mem 1) z
  simp [ψ₁_mk, ← comp_χ₁]

theorem ψ₀_fromZeroRingHom (i : R →+* B) (f : B) (r : R) (hr : MvPolynomial.C r ∈ 𝒜 0) :
    ψ₀ i f (fromZeroRingHom 𝒜 _ ⟨MvPolynomial.C r, hr⟩) = i r := by
  simp [ψ₀, awayDesc_fromZeroRingHom]

theorem ψ₁_fromZeroRingHom (i : R →+* B) (g : B) (r : R) (hr : MvPolynomial.C r ∈ 𝒜 0) :
    ψ₁ i g (fromZeroRingHom 𝒜 _ ⟨MvPolynomial.C r, hr⟩) = i r := by
  simp [ψ₁, awayDesc_fromZeroRingHom]

theorem θ_comp_awayMap₀ (i : R →+* B) (f g : B) (hfg : f * g = 1) :
    (θ i f g hfg).comp (awayMap 𝒜 (X_mem 1) (rfl : (MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) R) = _)) = ψ₀ i f := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (X_mem 0) z
  rw [RingHom.comp_apply, awayMap_mk, ψ₀_mk]
  erw [θ_mk]
  rw [map_mul, map_pow, χ₀_X_one, mul_assoc, ← mul_pow, hfg, one_pow, mul_one]

theorem θ_comp_awayMap₁ (i : R →+* B) (f g : B) (hfg : f * g = 1) :
    (θ i f g hfg).comp (awayMap 𝒜 (X_mem 0) (mul_comm _ _ : (MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) R) = _)) = ψ₁ i g := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (X_mem 1) z
  rw [RingHom.comp_apply, awayMap_mk, ψ₁_mk]
  erw [θ_mk]
  rw [map_mul, map_pow, χ₀_X_zero, one_pow, mul_one, χ₁_eq_of_mem i f g hfg (by simpa using ha),
    mul_comm]

end Charts

section Glue

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) R

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def iOf (W : C.Opens) : R →+* Γ(C, W) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appLE ⊤ W le_top).hom

theorem map_comp_iOf {W W' : C.Opens} (h : W' ≤ W) :
    (C.presheaf.map (homOfLE h).op).hom.comp (iOf c W) = iOf c W' := by
  rw [iOf, iOf, ← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE_map]

variable (U V : C.Opens) (f : Γ(C, U)) (g : Γ(C, V))

noncomputable def chart₀ : Spec Γ(C, U) ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (ψ₀ (iOf c U) f)) ≫ Proj.awayι 𝒜 (MvPolynomial.X 0) (X_mem 0) one_pos

noncomputable def chart₁ : Spec Γ(C, V) ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (ψ₁ (iOf c V) g)) ≫ Proj.awayι 𝒜 (MvPolynomial.X 1) (X_mem 1) one_pos

theorem specMap_comp_chart₀
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1) :
    Spec.map (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op) ≫ chart₀ c U f =
      Spec.map (CommRingCat.ofHom (θ (iOf c (U ⊓ V)) _ _ hfg)) ≫
        Proj.awayι 𝒜 (MvPolynomial.X 0 * MvPolynomial.X 1) X_mul_X_mem two_pos := by
  have key : CommRingCat.ofHom (ψ₀ (iOf c U) f) ≫ C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op =
      CommRingCat.ofHom (awayMap 𝒜 (X_mem 1) (rfl : (MvPolynomial.X 0 * MvPolynomial.X 1 :
        MvPolynomial (Fin 2) R) = _)) ≫ CommRingCat.ofHom (θ (iOf c (U ⊓ V)) _ _ hfg) := by
    ext1
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, comp_ψ₀, map_comp_iOf, CommRingCat.hom_comp,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, θ_comp_awayMap₀]
  rw [chart₀, ← Spec.map_comp_assoc, key, Spec.map_comp_assoc, Proj.SpecMap_awayMap_awayι]

theorem specMap_comp_chart₁
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1) :
    Spec.map (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op) ≫ chart₁ c V g =
      Spec.map (CommRingCat.ofHom (θ (iOf c (U ⊓ V)) _ _ hfg)) ≫
        Proj.awayι 𝒜 (MvPolynomial.X 0 * MvPolynomial.X 1) X_mul_X_mem two_pos := by
  have key : CommRingCat.ofHom (ψ₁ (iOf c V) g) ≫ C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op =
      CommRingCat.ofHom (awayMap 𝒜 (X_mem 0) (mul_comm _ _ : (MvPolynomial.X 0 * MvPolynomial.X 1 :
        MvPolynomial (Fin 2) R) = _)) ≫ CommRingCat.ofHom (θ (iOf c (U ⊓ V)) _ _ hfg) := by
    ext1
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, comp_ψ₁, map_comp_iOf, CommRingCat.hom_comp,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, θ_comp_awayMap₁]
  rw [chart₁, ← Spec.map_comp_assoc, key, Spec.map_comp_assoc, Proj.SpecMap_awayMap_awayι]

theorem exists_of_homOfLE_comp_eq {Y : Scheme.{u}} (hUV : U ⊔ V = ⊤) (φU : (U : Scheme.{u}) ⟶ Y)
    (φV : (V : Scheme.{u}) ⟶ Y) (h : C.homOfLE inf_le_left ≫ φU = C.homOfLE inf_le_right ≫ φV) :
    ∃ π : C ⟶ Y, U.ι ≫ π = φU ∧ V.ι ≫ π = φV := by
  let 𝒰 : C.OpenCover := C.openCoverOfIsOpenCover (fun b : Bool => cond b U V)
    (by rw [TopologicalSpace.IsOpenCover, iSup_bool_eq]; exact hUV)
  let φ : ∀ b, 𝒰.X b ⟶ Y := fun b => match b with
    | true => φU
    | false => φV
  have hUV' : pullback.fst U.ι V.ι ≫ φU = pullback.snd U.ι V.ι ≫ φV := by
    rw [← cancel_epi (isPullback_opens_inf U V).isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_snd_assoc]
    exact h
  have key : ∀ b b', pullback.fst (𝒰.f b) (𝒰.f b') ≫ φ b = pullback.snd _ _ ≫ φ b' := by
    rintro (_ | _) (_ | _)
    · change pullback.fst V.ι V.ι ≫ φV = pullback.snd V.ι V.ι ≫ φV
      rw [fst_eq_snd_of_mono_eq]
    · change pullback.fst V.ι U.ι ≫ φV = pullback.snd V.ι U.ι ≫ φU
      rw [← cancel_epi (pullbackSymmetry U.ι V.ι).hom, pullbackSymmetry_hom_comp_fst_assoc,
        pullbackSymmetry_hom_comp_snd_assoc]
      exact hUV'.symm
    · exact hUV'
    · change pullback.fst U.ι U.ι ≫ φU = pullback.snd U.ι U.ι ≫ φU
      rw [fst_eq_snd_of_mono_eq]
  exact ⟨𝒰.glueMorphisms φ key, 𝒰.ι_glueMorphisms φ key true, 𝒰.ι_glueMorphisms φ key false⟩

theorem exists_fromSpec_comp_eq (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1) :
    ∃ π : C ⟶ Proj 𝒜, hU.fromSpec ≫ π = chart₀ c U f ∧ hV.fromSpec ≫ π = chart₁ c V g := by
  obtain ⟨π, h₀, h₁⟩ := exists_of_homOfLE_comp_eq U V hUV (U.toSpecΓ ≫ chart₀ c U f) (V.toSpecΓ ≫ chart₁ c V g)
    (by rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, specMap_comp_chart₀ c U V f g hfg,
          ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, specMap_comp_chart₁ c U V f g hfg])
  refine ⟨π, ?_, ?_⟩
  · rw [← IsAffineOpen.isoSpec_inv_ι, Category.assoc, h₀, ← IsAffineOpen.isoSpec_hom hU,
      Iso.inv_hom_id_assoc]
  · rw [← IsAffineOpen.isoSpec_inv_ι, Category.assoc, h₁, ← IsAffineOpen.isoSpec_hom hV,
      Iso.inv_hom_id_assoc]

end Glue

section Consequences

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) R

attribute [local instance] MvPolynomial.gradedAlgebra

variable (U V : C.Opens) (f : Γ(C, U)) (g : Γ(C, V)) (hU : IsAffineOpen U) (hV : IsAffineOpen V)

theorem opens_ext_of_fromSpec (hUV : U ⊔ V = ⊤) {W₁ W₂ : C.Opens}
    (h₀ : hU.fromSpec ⁻¹ᵁ W₁ = hU.fromSpec ⁻¹ᵁ W₂) (h₁ : hV.fromSpec ⁻¹ᵁ W₁ = hV.fromSpec ⁻¹ᵁ W₂) :
    W₁ = W₂ := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  have hx : x ∈ U ⊔ V := by rw [hUV]; trivial
  rcases TopologicalSpace.Opens.mem_sup.mp hx with hxU | hxV
  · obtain ⟨y, rfl⟩ : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
    exact Iff.of_eq (congrArg (fun W : (Spec Γ(C, U)).Opens => y ∈ W) h₀)
  · obtain ⟨y, rfl⟩ : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hxV
    exact Iff.of_eq (congrArg (fun W : (Spec Γ(C, V)).Opens => y ∈ W) h₁)

theorem hom_ext_of_fromSpec (hUV : U ⊔ V = ⊤) {Y : Scheme.{u}} {p q : C ⟶ Y}
    (h₀ : hU.fromSpec ≫ p = hU.fromSpec ≫ q) (h₁ : hV.fromSpec ≫ p = hV.fromSpec ≫ q) : p = q := by
  let 𝒰 : C.OpenCover := C.openCoverOfIsOpenCover (fun b : Bool => cond b U V)
    (by rw [TopologicalSpace.IsOpenCover, iSup_bool_eq]; exact hUV)
  refine Scheme.Cover.hom_ext 𝒰 p q ?_
  rintro (_ | _)
  · change V.ι ≫ p = V.ι ≫ q
    rw [← cancel_epi hV.isoSpec.inv, ← Category.assoc, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι]
    exact h₁
  · change U.ι ≫ p = U.ι ≫ q
    rw [← cancel_epi hU.isoSpec.inv, ← Category.assoc, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι]
    exact h₀

theorem chart₀_preimage_basicOpen_X_zero :
    chart₀ c U f ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 0) = ⊤ := by
  rw [chart₀, Scheme.Hom.comp_preimage, ← Proj.opensRange_awayι 𝒜 _ (X_mem 0) one_pos,
    Scheme.Hom.preimage_opensRange]
  rfl

theorem chart₁_preimage_basicOpen_X_one :
    chart₁ c V g ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 1) = ⊤ := by
  rw [chart₁, Scheme.Hom.comp_preimage, ← Proj.opensRange_awayι 𝒜 _ (X_mem 1) one_pos,
    Scheme.Hom.preimage_opensRange]
  rfl

theorem chart₀_preimage_basicOpen_X_one :
    chart₀ c U f ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 1) = PrimeSpectrum.basicOpen f := by
  rw [chart₀, Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen 𝒜 (X_mem 0) one_pos (X_mem 1) one_pos,
    SpecMap_preimage_basicOpen]
  congr 1
  change ψ₀ (iOf c U) f (Away.mk 𝒜 (X_mem 0) 1 (MvPolynomial.X 1 ^ 1) _) = f
  rw [ψ₀_mk]
  simp

theorem chart₁_preimage_basicOpen_X_zero :
    chart₁ c V g ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 0) = PrimeSpectrum.basicOpen g := by
  rw [chart₁, Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen 𝒜 (X_mem 1) one_pos (X_mem 0) one_pos,
    SpecMap_preimage_basicOpen]
  congr 1
  change ψ₁ (iOf c V) g (Away.mk 𝒜 (X_mem 1) 1 (MvPolynomial.X 0 ^ 1) _) = g
  rw [ψ₁_mk]
  simp

variable {U V f g hU hV}

theorem preimage_basicOpen_X_zero (π : C ⟶ Proj 𝒜) (h₀ : hU.fromSpec ≫ π = chart₀ c U f)
    (h₁ : hV.fromSpec ≫ π = chart₁ c V g) (hUV : U ⊔ V = ⊤) (hg : U ⊓ V = C.basicOpen g) :
    π ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 0) = U := by
  refine opens_ext_of_fromSpec U V hU hV hUV ?_ ?_
  · rw [← Scheme.Hom.comp_preimage, h₀, chart₀_preimage_basicOpen_X_zero, IsAffineOpen.fromSpec_preimage_self]
  · rw [← Scheme.Hom.comp_preimage, h₁, chart₁_preimage_basicOpen_X_zero, ← hV.fromSpec_preimage_basicOpen,
      ← hg, Scheme.Hom.preimage_inf, hV.fromSpec_preimage_self, inf_top_eq]

theorem preimage_basicOpen_X_one (π : C ⟶ Proj 𝒜) (h₀ : hU.fromSpec ≫ π = chart₀ c U f)
    (h₁ : hV.fromSpec ≫ π = chart₁ c V g) (hUV : U ⊔ V = ⊤) (hf : U ⊓ V = C.basicOpen f) :
    π ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 1) = V := by
  refine opens_ext_of_fromSpec U V hU hV hUV ?_ ?_
  · rw [← Scheme.Hom.comp_preimage, h₀, chart₀_preimage_basicOpen_X_one, ← hU.fromSpec_preimage_basicOpen,
      ← hf, Scheme.Hom.preimage_inf, hU.fromSpec_preimage_self, top_inf_eq]
  · rw [← Scheme.Hom.comp_preimage, h₁, chart₁_preimage_basicOpen_X_one, IsAffineOpen.fromSpec_preimage_self]

theorem fromSpec_comp (W : C.Opens) (hW : IsAffineOpen W) :
    hW.fromSpec ≫ c = Spec.map (CommRingCat.ofHom (iOf c W)) := by
  rw [iOf, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top _) hW le_top]

theorem comp_eq (π : C ⟶ Proj 𝒜) (h₀ : hU.fromSpec ≫ π = chart₀ c U f)
    (h₁ : hV.fromSpec ≫ π = chart₁ c V g) (hUV : U ⊔ V = ⊤) (p : Proj 𝒜 ⟶ Spec (CommRingCat.of R))
    (e : R →+* (𝒜 0)) (he : ∀ r, (e r : MvPolynomial (Fin 2) R) = MvPolynomial.C r)
    (hp : ∀ j : Fin 2, Proj.awayι 𝒜 (MvPolynomial.X j) (X_mem j) one_pos ≫ p =
      Spec.map (CommRingCat.ofHom ((fromZeroRingHom 𝒜 _).comp e))) :
    π ≫ p = c := by
  have he' : ∀ r, e r = ⟨MvPolynomial.C r, he r ▸ (e r).2⟩ := fun r => Subtype.ext (he r)
  refine hom_ext_of_fromSpec U V hU hV hUV ?_ ?_
  · rw [reassoc_of% h₀, fromSpec_comp, chart₀, Category.assoc, hp 0, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, he', ψ₀_fromZeroRingHom]
  · rw [reassoc_of% h₁, fromSpec_comp, chart₁, Category.assoc, hp 1, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, he', ψ₁_fromZeroRingHom]

theorem awayToSection_comp_appLE_X_zero (π : C ⟶ Proj 𝒜) (h₀ : hU.fromSpec ≫ π = chart₀ c U f)
    (hle : U ≤ π ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 0)) :
    Proj.awayToSection 𝒜 (MvPolynomial.X 0) ≫ π.appLE (Proj.basicOpen 𝒜 (MvPolynomial.X 0)) U hle =
      CommRingCat.ofHom (ψ₀ (iOf c U) f) := by
  apply Spec.map_injective
  rw [← cancel_epi hU.isoSpec.hom, IsAffineOpen.isoSpec_hom, Spec.map_comp,
    Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  change π.resLE _ U hle ≫ Proj.basicOpenToSpec 𝒜 (MvPolynomial.X 0) = _
  rw [← Proj.basicOpenIsoSpec_hom 𝒜 _ (X_mem 0) one_pos, ← Iso.eq_comp_inv,
    ← cancel_mono (Proj.basicOpen 𝒜 (MvPolynomial.X 0)).ι, Category.assoc, Category.assoc,
    Proj.basicOpenIsoSpec_inv_ι, Scheme.Hom.resLE_comp_ι, ← cancel_epi hU.isoSpec.inv, ← Category.assoc,
    IsAffineOpen.isoSpec_inv_ι, h₀, IsAffineOpen.isoSpec_inv_toSpecΓ_assoc]
  rfl

theorem awayToSection_comp_appLE_X_one (π : C ⟶ Proj 𝒜) (h₁ : hV.fromSpec ≫ π = chart₁ c V g)
    (hle : V ≤ π ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 1)) :
    Proj.awayToSection 𝒜 (MvPolynomial.X 1) ≫ π.appLE (Proj.basicOpen 𝒜 (MvPolynomial.X 1)) V hle =
      CommRingCat.ofHom (ψ₁ (iOf c V) g) := by
  apply Spec.map_injective
  rw [← cancel_epi hV.isoSpec.hom, IsAffineOpen.isoSpec_hom, Spec.map_comp,
    Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  change π.resLE _ V hle ≫ Proj.basicOpenToSpec 𝒜 (MvPolynomial.X 1) = _
  rw [← Proj.basicOpenIsoSpec_hom 𝒜 _ (X_mem 1) one_pos, ← Iso.eq_comp_inv,
    ← cancel_mono (Proj.basicOpen 𝒜 (MvPolynomial.X 1)).ι, Category.assoc, Category.assoc,
    Proj.basicOpenIsoSpec_inv_ι, Scheme.Hom.resLE_comp_ι, ← cancel_epi hV.isoSpec.inv, ← Category.assoc,
    IsAffineOpen.isoSpec_inv_ι, h₁, IsAffineOpen.isoSpec_inv_toSpecΓ_assoc]
  rfl

theorem appLE_awayToSection_X_zero (π : C ⟶ Proj 𝒜) (h₀ : hU.fromSpec ≫ π = chart₀ c U f)
    (hle : U ≤ π ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 0))
    (h1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) R) ∈ 𝒜 (1 • 1)) :
    (π.appLE (Proj.basicOpen 𝒜 (MvPolynomial.X 0)) U hle).hom
      ((Proj.awayToSection 𝒜 (MvPolynomial.X 0)).hom (Away.mk 𝒜 (X_mem 0) 1 (MvPolynomial.X 1) h1)) = f := by
  rw [← CommRingCat.comp_apply, awayToSection_comp_appLE_X_zero c π h₀ hle]
  show ψ₀ (iOf c U) f _ = f
  rw [ψ₀_mk, χ₀_X_one]

theorem appLE_awayToSection_X_one (π : C ⟶ Proj 𝒜) (h₁ : hV.fromSpec ≫ π = chart₁ c V g)
    (hle : V ≤ π ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 1))
    (h0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) R) ∈ 𝒜 (1 • 1)) :
    (π.appLE (Proj.basicOpen 𝒜 (MvPolynomial.X 1)) V hle).hom
      ((Proj.awayToSection 𝒜 (MvPolynomial.X 1)).hom (Away.mk 𝒜 (X_mem 1) 1 (MvPolynomial.X 0) h0)) = g := by
  rw [← CommRingCat.comp_apply, awayToSection_comp_appLE_X_one c π h₁ hle]
  show ψ₁ (iOf c V) g _ = g
  rw [ψ₁_mk, χ₁_X_zero]

end Consequences

end AlgebraicGeometry.TwoChartHomProj
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_finset_of_twoCharts.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_finset_of_twoCharts.AlgebraicGeometry.TwoChartHomProj"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_finset_of_twoCharts.AlgebraicGeometry"

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (f : Γ(X, U)) (g : Γ(X, V))
    (hf : U ⊓ V = X.basicOpen f) (hg : U ⊓ V = X.basicOpen g)
    (hfg : (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (F : Finset X) : ∃ W : X.Opens, IsAffineOpen W ∧ ∀ x ∈ F, x ∈ W := by
  classical
  obtain ⟨π, h₀, h₁⟩ := AlgebraicGeometry.TwoChartHomProj.exists_fromSpec_comp_eq c U V f g hU hV hUV hfg
  have hU' := AlgebraicGeometry.TwoChartHomProj.preimage_basicOpen_X_zero c π h₀ h₁ hUV hg
  have hV' := AlgebraicGeometry.TwoChartHomProj.preimage_basicOpen_X_one c π h₀ h₁ hUV hf

  have hX : ∀ i : Fin 2, (MvPolynomial.X i : MvPolynomial (Fin 2) R) ∈
      MvPolynomial.homogeneousSubmodule (Fin 2) R 1 := fun i => ProjSpace.X_mem_one R 1 i
  have hcovP : (⨆ i : Fin 2, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R 1)
  haveI : IsAffineHom π := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun y => ?_
    have hy : y ∈ (⨆ i : Fin 2, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X i)) := by
      rw [hcovP]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    refine ⟨_, hi, Proj.isAffineOpen_basicOpen _ _ (hX i) one_pos, ?_⟩
    fin_cases i
    · simpa [hU'] using hU
    · simpa [hV'] using hV
  exact AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj
    (MvPolynomial.homogeneousSubmodule (Fin 2) R) π F

end S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_finset_of_twoCharts
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_finset_of_twoCharts (solution)
