-- Prove2me | solution 1 for AlgebraicGeometry.exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1e53ef6e-83b9-5435-a98d-1b45d95aa37e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq.AlgebraicGeometry TopologicalSpace Opposite"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Scheme.fromSpecStalk_closedPoint Spec.map_comp_assoc Scheme.Hom IsAffineOpen.isoSpec_inv_ι IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme IsAffineOpen.fromSpecStalk Spec.map_injective IsLocallyNoetherian.component_noetherian IsAffineOpen Scheme.Hom.appLE_map Scheme.Hom.comp_apply AffineScheme"
namespace InfinitesimalRigidity
p2m_open "AlgebraicGeometry"

theorem ringHom_ext_of_forall_quotient_pow {A B : Type*} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsLocalRing A] (φ ψ : B →+* A)
    (h : ∀ n : ℕ, (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n)).comp φ =
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n)).comp ψ) :
    φ = ψ := by
  ext b
  have hmem : φ b - ψ b ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal A ^ n := by
    refine Ideal.mem_iInf.mpr fun n => ?_
    rw [← Ideal.Quotient.eq, ← RingHom.comp_apply, h n, RingHom.comp_apply]
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top,
    Ideal.mem_bot] at hmem
  exact sub_eq_zero.mp hmem

theorem exists_not_mem_and_forall_mul_eq_zero {R A : Type*} [CommRing R] [CommRing A]
    [IsNoetherianRing R] [Algebra R A] (𝔭 : Ideal R) [𝔭.IsPrime] [IsLocalization.AtPrime A 𝔭]
    (I : Ideal R) (hI : ∀ i ∈ I, algebraMap R A i = 0) :
    ∃ m : R, m ∉ 𝔭 ∧ ∀ i ∈ I, m * i = 0 := by
  classical
  obtain ⟨t, ht⟩ := (isNoetherianRing_iff_ideal_fg R).mp ‹_› I
  have hgen : ∀ g ∈ t, ∃ m : R, m ∉ 𝔭 ∧ m * g = 0 := by
    intro g hg
    have hgI : g ∈ I := ht ▸ Ideal.subset_span hg
    obtain ⟨⟨m, hm⟩, hmg⟩ :=
      (IsLocalization.map_eq_zero_iff 𝔭.primeCompl A g).mp (hI g hgI)
    exact ⟨m, hm, hmg⟩
  choose! mf hmf using hgen
  refine ⟨∏ g ∈ t, mf g, ?_, ?_⟩
  ·
    intro hmem
    obtain ⟨g, hg, hg'⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact (hmf g hg).1 hg'
  · intro i hi
    rw [← ht] at hi
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hi
    · intro g hg
      obtain ⟨u, hu⟩ : mf g ∣ ∏ g' ∈ t, mf g' := Finset.dvd_prod_of_mem _ hg
      rw [hu, mul_comm (mf g) u, mul_assoc, (hmf g hg).2, mul_zero]
    · simp
    · intro a b _ _ ha hb
      rw [mul_add, ha, hb, add_zero]
    · intro r a _ ha
      rw [smul_eq_mul, mul_left_comm, ha, mul_zero]

theorem exists_mem_and_ι_comp_eq {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f g : X ⟶ Y)
    (x : X)
    (h : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ g) :
    ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g := by
  classical

  set A : CommRingCat.{u} := X.presheaf.stalk x with hA
  let 𝔪 : Ideal A := IsLocalRing.maximalIdeal A
  let q : ∀ n : ℕ, A ⟶ CommRingCat.of (A ⧸ 𝔪 ^ n) := fun n =>
    CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ n))
  have hq : ∀ n : ℕ, Spec.map (q n) ≫ X.fromSpecStalk x ≫ f =
      Spec.map (q n) ≫ X.fromSpecStalk x ≫ g := h

  have hfg : f x = g x := by
    haveI : Nontrivial (A ⧸ 𝔪 ^ 1) :=
      Ideal.Quotient.nontrivial_iff.mpr (by
        rw [pow_one]; exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
    obtain ⟨p⟩ : Nonempty (PrimeSpectrum (A ⧸ 𝔪 ^ 1)) := inferInstance
    have hp : (Spec.map (q 1)) p = IsLocalRing.closedPoint A := by
      apply PrimeSpectrum.ext
      apply ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le
        (PrimeSpectrum.isPrime _).ne_top ?_).symm
      intro a ha
      change a ∈ Ideal.comap (Ideal.Quotient.mk (𝔪 ^ 1)) p.asIdeal
      rw [Ideal.mem_comap]
      have : Ideal.Quotient.mk (𝔪 ^ 1) a = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [pow_one]; exact ha)
      rw [this]
      exact zero_mem _
    have key : ∀ (φ : X ⟶ Y), (Spec.map (q 1) ≫ X.fromSpecStalk x ≫ φ) p = φ x := by
      intro φ
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hp]
      erw [Scheme.fromSpecStalk_closedPoint]
    rw [← key f, ← key g, hq 1]

  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  have hxW : x ∈ f ⁻¹ᵁ V ⊓ g ⁻¹ᵁ V := ⟨hyV, show g x ∈ V from hfg ▸ hyV⟩
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU₀, hU₀W⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW (f ⁻¹ᵁ V ⊓ g ⁻¹ᵁ V).isOpen
  have ef : U₀ ≤ f ⁻¹ᵁ V := fun z hz => (hU₀W hz).1
  have eg : U₀ ≤ g ⁻¹ᵁ V := fun z hz => (hU₀W hz).2

  have hchart : ∀ (φ : X ⟶ Y) (e : U₀ ≤ φ ⁻¹ᵁ V) (n : ℕ),
      Spec.map (q n) ≫ X.fromSpecStalk x ≫ φ =
        Spec.map (φ.appLE V U₀ e ≫ X.presheaf.germ U₀ x hxU₀ ≫ q n) ≫ hV.fromSpec := by
    intro φ e n
    rw [← hU₀.fromSpecStalk_eq_fromSpecStalk hxU₀, IsAffineOpen.fromSpecStalk,
      Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec φ hV hU₀ e,
      Spec.map_comp_assoc, Spec.map_comp_assoc]
  have hring : ∀ n : ℕ,
      f.appLE V U₀ ef ≫ X.presheaf.germ U₀ x hxU₀ ≫ q n =
        g.appLE V U₀ eg ≫ X.presheaf.germ U₀ x hxU₀ ≫ q n := by
    intro n
    have := hq n
    rw [hchart f ef n, hchart g eg n, cancel_mono] at this
    exact Spec.map_injective this

  have hstalk : (f.appLE V U₀ ef ≫ X.presheaf.germ U₀ x hxU₀).hom =
      (g.appLE V U₀ eg ≫ X.presheaf.germ U₀ x hxU₀).hom := by
    apply ringHom_ext_of_forall_quotient_pow
    intro n
    have := congrArg (fun φ => CommRingCat.Hom.hom φ) (hring n)
    simp only [CommRingCat.hom_comp, Category.assoc, CommRingCat.hom_ofHom,
      RingHom.comp_assoc] at this
    exact this

  haveI : IsNoetherianRing Γ(X, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  letI := X.presheaf.algebra_section_stalk (⟨x, hxU₀⟩ : U₀)
  haveI := hU₀.isLocalization_stalk ⟨x, hxU₀⟩
  set φ : Γ(Y, V) →+* Γ(X, U₀) := (f.appLE V U₀ ef).hom with hφ
  set ψ : Γ(Y, V) →+* Γ(X, U₀) := (g.appLE V U₀ eg).hom with hψ
  let I : Ideal Γ(X, U₀) := Ideal.span (Set.range fun b => φ b - ψ b)
  have hI : ∀ i ∈ I, algebraMap Γ(X, U₀) A i = 0 := by
    intro i hi
    refine Submodule.span_induction ?_ (by simp) ?_ ?_ hi
    · rintro _ ⟨b, rfl⟩
      have := congrArg (fun χ => χ b) hstalk
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      change (X.presheaf.germ U₀ x hxU₀).hom (φ b - ψ b) = 0
      rw [map_sub, sub_eq_zero]
      exact this
    · intro a b _ _ ha hb
      rw [map_add, ha, hb, add_zero]
    · intro r a _ ha
      rw [smul_eq_mul, map_mul, ha, mul_zero]
  obtain ⟨m, hm𝔭, hmI⟩ := exists_not_mem_and_forall_mul_eq_zero
    (hU₀.primeIdealOf ⟨x, hxU₀⟩).asIdeal I hI

  have hxm : x ∈ X.basicOpen m := by
    rw [X.mem_basicOpen m x hxU₀]
    exact IsLocalization.map_units A (⟨m, hm𝔭⟩ : (hU₀.primeIdealOf ⟨x, hxU₀⟩).asIdeal.primeCompl)
  refine ⟨X.basicOpen m, hxm, ?_⟩

  have hDle : X.basicOpen m ≤ U₀ := X.basicOpen_le m
  have hres : f.appLE V U₀ ef ≫ X.presheaf.map (homOfLE hDle).op =
      g.appLE V U₀ eg ≫ X.presheaf.map (homOfLE hDle).op := by
    ext b
    change algebraMap Γ(X, U₀) Γ(X, X.basicOpen m) (φ b) =
      algebraMap Γ(X, U₀) Γ(X, X.basicOpen m) (ψ b)
    haveI := hU₀.isLocalization_basicOpen m
    rw [← sub_eq_zero, ← map_sub,
      IsLocalization.map_eq_zero_iff (Submonoid.powers m) Γ(X, X.basicOpen m)]
    exact ⟨⟨m, Submonoid.mem_powers m⟩, hmI _ (Ideal.subset_span ⟨b, rfl⟩)⟩
  have hD : IsAffineOpen (X.basicOpen m) := hU₀.basicOpen m
  have key : ∀ (χ : X ⟶ Y) (e : U₀ ≤ χ ⁻¹ᵁ V),
      (X.basicOpen m).ι ≫ χ =
        hD.isoSpec.hom ≫ Spec.map (χ.appLE V U₀ e ≫ X.presheaf.map (homOfLE hDle).op) ≫
          hV.fromSpec := by
    intro χ e
    rw [Scheme.Hom.appLE_map, IsAffineOpen.SpecMap_appLE_fromSpec χ hV hD (hDle.trans e),
      ← IsAffineOpen.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc]
  rw [key f ef, key g eg, hres]

end AlgebraicGeometry.InfinitesimalRigidity

theorem solution
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f g : X ⟶ Y) (x : X)
    (h : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ g) :
    ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g :=
  AlgebraicGeometry.InfinitesimalRigidity.exists_mem_and_ι_comp_eq f g x h

end S_AlgebraicGeometry_exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq (solution)
