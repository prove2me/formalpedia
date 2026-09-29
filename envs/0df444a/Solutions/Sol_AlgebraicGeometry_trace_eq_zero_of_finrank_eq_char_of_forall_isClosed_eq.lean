-- Prove2me | solution 1 for AlgebraicGeometry.trace_eq_zero_of_finrank_eq_char_of_forall_isClosed_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/22eaf254-224b-5eae-a884-b9e4d0b977dc

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_trace_eq_zero_of_finrank_eq_char_of_forall_isClosed_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace TraceZero3a67f5ea

theorem trace_eq_zero_of_isLocalRing {k B : Type*} [Field k] [CommRing B] [Algebra k B] [Module.Finite k B]
    [IsLocalRing B] (h1 : Algebra.trace k B 1 = 0)
    (hres : Function.Surjective (algebraMap k (B ⧸ IsLocalRing.maximalIdeal B))) :
    Algebra.trace k B = 0 := by
  ext b
  obtain ⟨c, hc⟩ := hres (Ideal.Quotient.mk _ b)
  have hmem : b - algebraMap k B c ∈ IsLocalRing.maximalIdeal B := by
    rw [← Ideal.Quotient.eq, ← hc, IsScalarTower.algebraMap_apply k B (B ⧸ IsLocalRing.maximalIdeal B),
      Ideal.Quotient.algebraMap_eq]
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  have hnil : IsNilpotent (b - algebraMap k B c) := by
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
    refine ⟨n, ?_⟩
    have h1 : (b - algebraMap k B c) ^ n ∈ (Ideal.jacobson (⊥ : Ideal B)) ^ n :=
      Ideal.pow_mem_pow (by rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) n
    rw [hn] at h1
    exact h1
  have htn : Algebra.trace k B (b - algebraMap k B c) = 0 := by
    rw [Algebra.trace_apply]
    exact (LinearMap.isNilpotent_trace_of_isNilpotent (hnil.map (Algebra.lmul k B))).eq_zero
  have htc : Algebra.trace k B (algebraMap k B c) = 0 := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
  calc Algebra.trace k B b = Algebra.trace k B (algebraMap k B c + (b - algebraMap k B c)) := by rw [add_sub_cancel]
    _ = 0 := by rw [map_add, htc, htn, add_zero]
    _ = (0 : B →ₗ[k] k) b := rfl

theorem mk_trace_eq {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B]
    (𝔪 : Ideal A) [𝔪.IsMaximal] (b : B) :
    Ideal.Quotient.mk 𝔪 (Algebra.trace A B b) = Algebra.trace (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) (Ideal.Quotient.mk _ b) := by
  classical
  let Rₚ := Localization.AtPrime 𝔪
  let Sₚ := Localization (Algebra.algebraMapSubmonoid B 𝔪.primeCompl)
  letI : Algebra Rₚ Sₚ := localizationAlgebra 𝔪.primeCompl B
  haveI : IsScalarTower A Rₚ Sₚ := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B 𝔪.primeCompl) Sₚ := inferInstance
  haveI : Module.Finite Rₚ Sₚ := .of_isLocalization A B 𝔪.primeCompl
  haveI : Module.Free Rₚ Sₚ :=
    Module.Free.of_basis ((Module.Free.chooseBasis A B).localizationLocalization Rₚ 𝔪.primeCompl Sₚ)
  have key := trace_quotient_eq_trace_localization_quotient B 𝔪 Rₚ Sₚ b
  apply (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔪 Rₚ).injective
  rw [key, RingEquiv.apply_symm_apply, IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk,
    IsScalarTower.algebraMap_eq B Sₚ, RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, Algebra.trace_quotient_mk,
    Algebra.trace_localization A 𝔪.primeCompl]

theorem eq_zero_of_forall_mk_eq_zero {A : Type*} [CommRing A] [IsJacobsonRing A] [IsReduced A] (t : A)
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → Ideal.Quotient.mk 𝔪 t = 0) : t = 0 := by
  have ht : t ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro J ⟨-, hJ⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mp (h J hJ)
  rw [IsJacobsonRing.out ‹IsJacobsonRing A› Ideal.isRadical_bot] at ht
  exact ht

theorem isLocalRing_quotient_map {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (𝔪 : Ideal A) [𝔪.IsMaximal]
    (huniq : ∀ N₁ N₂ : Ideal B, N₁.IsMaximal → N₂.IsMaximal →
      N₁.comap (algebraMap A B) = N₂.comap (algebraMap A B) → N₁ = N₂)
    [Nontrivial (B ⧸ 𝔪.map (algebraMap A B))] : IsLocalRing (B ⧸ 𝔪.map (algebraMap A B)) := by
  obtain ⟨M₀, hM₀⟩ := Ideal.exists_maximal (B ⧸ 𝔪.map (algebraMap A B))
  refine IsLocalRing.of_unique_max_ideal ⟨M₀, hM₀, fun M hM => ?_⟩

  have hc : ∀ M : Ideal (B ⧸ 𝔪.map (algebraMap A B)), M.IsMaximal →
      (M.comap (Ideal.Quotient.mk _)).IsMaximal ∧ (M.comap (Ideal.Quotient.mk _)).comap (algebraMap A B) = 𝔪 := by
    intro M hM
    have h1 : (M.comap (Ideal.Quotient.mk (𝔪.map (algebraMap A B)))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    refine ⟨h1, ?_⟩
    symm
    apply Ideal.IsMaximal.eq_of_le inferInstance
    · exact Ideal.IsPrime.ne_top (Ideal.IsMaximal.isPrime (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective) |>.comap _)
    · intro a ha
      rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)]
      exact M.zero_mem
  obtain ⟨hN, hNc⟩ := hc M hM
  obtain ⟨hN₀, hN₀c⟩ := hc M₀ hM₀
  have heq := huniq _ _ hN hN₀ (hNc.trans hN₀c.symm)
  rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective M,
    ← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective M₀, heq]

section Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f] (U : Y.Opens) (hU : IsAffineOpen U)

theorem isPullback_fromSpec :
    IsPullback (hU.preimage f).fromSpec (Spec.map (f.app U)) f hU.fromSpec := by
  have hnat : (hU.preimage f).isoSpec.inv ≫ (f ∣_ U) = Spec.map (f.app U) ≫ hU.isoSpec.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom]
    exact (Scheme.Opens.toSpecΓ_naturality f U).symm
  have sq1 : IsPullback (hU.preimage f).isoSpec.inv (Spec.map (f.app U)) (f ∣_ U) hU.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨hnat⟩
  have sq2 : IsPullback (f ⁻¹ᵁ U).ι (f ∣_ U) f U.ι := (isPullback_morphismRestrict f U).flip
  have := sq1.paste_horiz sq2
  rwa [IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.isoSpec_inv_ι] at this

include hU in

theorem maximal_eq_of_comap_eq [JacobsonSpace X]
    (hinj : ∀ x₁ x₂ : X, IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → f.base x₁ = f.base x₂ → x₁ = x₂)
    (N₁ N₂ : Ideal Γ(X, f ⁻¹ᵁ U)) (h₁ : N₁.IsMaximal) (h₂ : N₂.IsMaximal)
    (h : N₁.comap (f.app U).hom = N₂.comap (f.app U).hom) : N₁ = N₂ := by
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let z₁ : Spec Γ(X, V) := ⟨N₁, h₁.isPrime⟩
  let z₂ : Spec Γ(X, V) := ⟨N₂, h₂.isPrime⟩
  have hemb : Topology.IsOpenEmbedding hV.fromSpec.base := hV.fromSpec.isOpenEmbedding
  have hclosed : ∀ z : Spec Γ(X, V), IsClosed ({z} : Set (Spec Γ(X, V))) → IsClosed ({hV.fromSpec.base z} : Set X) := by
    intro z hz
    have hz' : z ∈ hV.fromSpec.base ⁻¹' closedPoints X := by rw [hemb.preimage_closedPoints]; exact hz
    exact hz'
  have hf : f.base (hV.fromSpec.base z₁) = f.base (hV.fromSpec.base z₂) := by
    have w := (isPullback_fromSpec f U hU).w
    have w' : ∀ z : Spec Γ(X, f ⁻¹ᵁ U), f.base (hV.fromSpec.base z) = hU.fromSpec.base ((Spec.map (f.app U)).base z) :=
      fun z => by simpa only [Scheme.Hom.comp_apply] using congrArg (fun g : Spec Γ(X, f ⁻¹ᵁ U) ⟶ Y => g.base z) w
    have e1 := w' z₁
    have e2 := w' z₂
    have hS : (Spec.map (f.app U)).base z₁ = (Spec.map (f.app U)).base z₂ := PrimeSpectrum.ext h
    rw [e1, e2, hS]
  have heq := hinj _ _ (hclosed z₁ ((PrimeSpectrum.isClosed_singleton_iff_isMaximal z₁).mpr h₁))
    (hclosed z₂ ((PrimeSpectrum.isClosed_singleton_iff_isMaximal z₂).mpr h₂)) hf
  have hz : z₁ = z₂ := hemb.injective heq
  exact congrArg (fun z : Spec Γ(X, V) => z.asIdeal) hz

theorem finrank_eq [LocallyOfFinitePresentation f] (z : Spec Γ(Y, U)) :
    letI := (f.app U).hom.toAlgebra
    ∀ [Module.Free Γ(Y, U) Γ(X, f ⁻¹ᵁ U)] [Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U)],
      Module.finrank Γ(Y, U) Γ(X, f ⁻¹ᵁ U) = f.finrank (hU.fromSpec.base z) := by
  intro _ _
  letI := (f.app U).hom.toAlgebra
  have h1 := Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_fromSpec f U hU) z
  have h2 := Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U) z
  rw [Module.rankAtStalk_eq_finrank_of_free] at h2
  have h3 : CommRingCat.ofHom (algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) = f.app U := CommRingCat.ofHom_hom _
  rw [h3, h1] at h2
  exact_mod_cast h2.symm

end Scheme

end TraceZero3a67f5ea

open TraceZero3a67f5ea in
theorem solution
    {κ : Type u} [Field κ] [IsAlgClosed κ] {p : ℕ} [Fact p.Prime] [CharP κ p]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (fY : Y ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType fY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (hrk : ∀ y, f.finrank y = p)
    (hinj : ∀ x₁ x₂ : X, IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → f.base x₁ = f.base x₂ → x₁ = x₂)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    ∀ [Module.Free Γ(Y, U) Γ(X, f ⁻¹ᵁ U)] [Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U)],
      Algebra.trace Γ(Y, U) Γ(X, f ⁻¹ᵁ U) = 0 := by
  intro _ _
  classical
  letI := (f.app U).hom.toAlgebra

  set A : Type u := Γ(Y, U) with hA
  set B : Type u := Γ(X, f ⁻¹ᵁ U) with hB

  rcases subsingleton_or_nontrivial A with hA0 | hA0
  · haveI : Subsingleton B := Module.subsingleton A B
    ext b; simp [Subsingleton.elim b 0]

  let ι₀ : κ →+* Γ(Spec (CommRingCat.of κ), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom
  have hι₀ : Function.Bijective ι₀ := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of κ)).inv
  let φ : κ →+* A := (fY.appLE ⊤ U le_top).hom.comp ι₀
  letI : Algebra κ A := φ.toAlgebra
  haveI : Algebra.FiniteType κ A := by
    have h1 : (fY.appLE ⊤ U le_top).hom.FiniteType := fY.finiteType_appLE (isAffineOpen_top _) hU le_top
    exact h1.comp (RingHom.FiniteType.of_surjective ι₀ hι₀.surjective)
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := κ) (B := A)
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (f ≫ fY)

  have hrank : Module.finrank A B = p := by
    obtain ⟨z⟩ := (inferInstance : Nonempty (Spec Γ(Y, U)))
    rw [finrank_eq f U hU z, hrk]

  ext b
  refine eq_zero_of_forall_mk_eq_zero _ fun 𝔪 h𝔪 => ?_
  haveI := h𝔪
  rw [mk_trace_eq 𝔪 b]

  letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  rcases subsingleton_or_nontrivial (B ⧸ 𝔪.map (algebraMap A B)) with hB0 | hB0
  · rw [Subsingleton.elim (Ideal.Quotient.mk (𝔪.map (algebraMap A B)) b) 0, map_zero]
  haveI : Module.Finite (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) := Module.Finite.of_restrictScalars_finite A _ _

  haveI : IsLocalRing (B ⧸ 𝔪.map (algebraMap A B)) :=
    isLocalRing_quotient_map 𝔪 (fun N₁ N₂ h₁ h₂ h => maximal_eq_of_comap_eq f U hU hinj N₁ N₂ h₁ h₂ h)

  haveI : Module.Finite κ (A ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing κ (A ⧸ 𝔪)
  have hbij : Function.Bijective (algebraMap κ (A ⧸ 𝔪)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsAlgClosed (A ⧸ 𝔪) := IsAlgClosed.of_ringEquiv κ (A ⧸ 𝔪) (RingEquiv.ofBijective _ hbij)
  haveI : CharP (A ⧸ 𝔪) p := charP_of_injective_ringHom hbij.1 p

  have hres : Function.Surjective (algebraMap (A ⧸ 𝔪)
      ((B ⧸ 𝔪.map (algebraMap A B)) ⧸ IsLocalRing.maximalIdeal (B ⧸ 𝔪.map (algebraMap A B)))) := by
    letI : Field ((B ⧸ 𝔪.map (algebraMap A B)) ⧸ IsLocalRing.maximalIdeal (B ⧸ 𝔪.map (algebraMap A B))) :=
      Ideal.Quotient.field _
    haveI : Module.Finite (A ⧸ 𝔪) ((B ⧸ 𝔪.map (algebraMap A B)) ⧸ IsLocalRing.maximalIdeal (B ⧸ 𝔪.map (algebraMap A B))) :=
      Module.Finite.of_surjective
        (Ideal.Quotient.mkₐ (A ⧸ 𝔪) (IsLocalRing.maximalIdeal (B ⧸ 𝔪.map (algebraMap A B)))).toLinearMap
        (Ideal.Quotient.mkₐ_surjective (A ⧸ 𝔪) (IsLocalRing.maximalIdeal (B ⧸ 𝔪.map (algebraMap A B))))
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := A ⧸ 𝔪)).2

  have h1 : Algebra.trace (A ⧸ 𝔪) (B ⧸ 𝔪.map (algebraMap A B)) 1 = 0 := by
    rw [← map_one (Ideal.Quotient.mk (𝔪.map (algebraMap A B))), ← mk_trace_eq 𝔪 (1 : B),
      ← map_one (algebraMap A B), Algebra.trace_algebraMap, hrank, nsmul_eq_mul, mul_one, map_natCast,
      CharP.cast_eq_zero]
  rw [trace_eq_zero_of_isLocalRing h1 hres, LinearMap.zero_apply]

end S_AlgebraicGeometry_trace_eq_zero_of_finrank_eq_char_of_forall_isClosed_eq
end P2MW
export P2MW.S_AlgebraicGeometry_trace_eq_zero_of_finrank_eq_char_of_forall_isClosed_eq (solution)
