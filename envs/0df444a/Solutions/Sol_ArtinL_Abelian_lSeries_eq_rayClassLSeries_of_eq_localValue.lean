-- Prove2me | solution 1 for ArtinL.Abelian.lSeries_eq_rayClassLSeries_of_eq_localValue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a5dca827-c9c8-564c-8c38-20382b0c8d43

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_NumberField_CompletedRayL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_lSeries_eq_rayClassLSeries_of_eq_localValue

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply Filter Topology Asymptotics
open scoped Classical nonZeroDivisors

namespace ArtinRayDict

variable (K : Type*) [Field K] [NumberField K]

theorem tendsto_sum_card_div :
    Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / n) atTop
      (𝓝 ((2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K * Units.regulator K *
        classNumber K) / (Units.torsionOrder K * Real.sqrt |discr K|))) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem summable_card_absNorm {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s := by
  set d : ℕ → ℝ := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) with hd
  have h1 := (tendsto_sum_card_div K).isBigO_one ℝ
  have h2 : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, d k) =ᶠ[atTop]
      fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n, d k) / n * n := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, d k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine h2.trans_isBigO ?_
    have h3 := h1.mul (isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop)
    refine h3.congr_right fun n ↦ ?_
    rw [Real.rpow_one, one_mul]
  have h4 := LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun n ↦ Nat.cast_nonneg _)
    zero_le_one (by simpa using hs)
  refine (LSeriesSummable_congr s fun {n} _ ↦ ?_).1 h4
  simp [hd]

def cnt (I : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk I).factors

variable {K}

theorem cnt_ne_zero_iff {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    cnt K I v ≠ 0 ↔ v.asIdeal ∣ I := by
  unfold cnt
  exact Associates.count_ne_zero_iff_dvd hI v.irreducible

theorem finite_setOf_cnt_ne_zero {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    {v : HeightOneSpectrum (𝓞 K) | cnt K I v ≠ 0}.Finite := by
  refine (Ideal.finite_factors hI).subset fun v hv ↦ ?_
  exact (cnt_ne_zero_iff hI v).1 hv

theorem hasFiniteMulSupport_pow_cnt {M : Type*} [Monoid M] {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (f : HeightOneSpectrum (𝓞 K) → M) :
    Function.HasFiniteMulSupport fun v ↦ f v ^ cnt K I v := by
  refine (finite_setOf_cnt_ne_zero hI).subset fun v hv ↦ ?_
  rw [Function.mem_mulSupport] at hv
  intro h
  exact hv (by simp only [h, pow_zero])

theorem count_coeIdeal {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = cnt K I v := by
  unfold cnt
  exact FractionalIdeal.count_coe K v (by rwa [Ne, Ideal.zero_eq_bot])

variable (K) in

def idealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K ⟨I, mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.zero_eq_bot])⟩

theorem idealUnit_val (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ((idealUnit K I hI : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = I :=
  FractionalIdeal.coe_mk0 K _

theorem idealUnit_mem_iff {𝔣 : Ideal (𝓞 K)} (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    idealUnit K I hI ∈ coprimeToModulus K 𝔣 ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 → cnt K I v = 0 := by
  rw [mem_coprimeToModulus_iff]
  refine forall_congr' fun v ↦ forall_congr' fun _ ↦ ?_
  rw [idealUnit_val, count_coeIdeal hI, Nat.cast_eq_zero]

variable (K) in

def primeCoprime (𝔣 : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) : ↥(coprimeToModulus K 𝔣) :=
  if hv : v.asIdeal ∣ 𝔣 then 1 else ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩

def toFrac (𝔣 : Ideal (𝓞 K)) : ↥(coprimeToModulus K 𝔣) →* FractionalIdeal (𝓞 K)⁰ K :=
  (Units.coeHom (FractionalIdeal (𝓞 K)⁰ K)).comp (coprimeToModulus K 𝔣).subtype

theorem toFrac_apply {𝔣 : Ideal (𝓞 K)} (y : ↥(coprimeToModulus K 𝔣)) :
    toFrac 𝔣 y = ((y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := rfl

theorem toFrac_injective (𝔣 : Ideal (𝓞 K)) : Function.Injective (toFrac (K := K) 𝔣) := by
  intro x y h
  rw [toFrac_apply, toFrac_apply] at h
  exact Subtype.ext (Units.ext h)

theorem eq_finprod_primeCoprime {𝔣 : Ideal (𝓞 K)} {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (y : ↥(coprimeToModulus K 𝔣))
    (hy : ((y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = I) :
    y = ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeCoprime K 𝔣 v ^ cnt K I v := by
  apply toFrac_injective 𝔣
  rw [toFrac_apply, hy, (toFrac 𝔣).map_finprod (hasFiniteMulSupport_pow_cnt hI _)]
  conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization_coe K hI]
  refine finprod_congr fun v ↦ ?_
  rw [zpow_natCast, map_pow]
  show _ = toFrac 𝔣 (primeCoprime K 𝔣 v) ^ cnt K I v
  by_cases hv : v.asIdeal ∣ 𝔣
  · have h0 : cnt K I v = 0 := by
      have := y.2 v hv
      rwa [hy, count_coeIdeal hI, Nat.cast_eq_zero] at this
    change _ ^ cnt K I v = _
    rw [h0, pow_zero, pow_zero]
  · rw [primeCoprime, dif_neg hv, toFrac_apply]
    show _ = ((primeUnit K v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ^ _
    rw [primeUnit_val]
    rfl

theorem apply_mk_eq_finprod {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (y : ↥(coprimeToModulus K 𝔣))
    (hy : ((y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = I) :
    χ (NarrowRayClassGroup.mk K 𝔣 y) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        χ (NarrowRayClassGroup.mk K 𝔣 (primeCoprime K 𝔣 v)) ^ cnt K I v := by
  rw [eq_finprod_primeCoprime hI y hy]
  rw [← MonoidHom.comp_apply,
    (χ.comp (NarrowRayClassGroup.mk K 𝔣)).map_finprod (hasFiniteMulSupport_pow_cnt hI _)]
  refine finprod_congr fun v ↦ ?_
  rw [map_pow, MonoidHom.comp_apply]

variable (K) in

def IsClassOf (𝔣 : Ideal (𝓞 K)) (C : NarrowRayClassGroup K 𝔣) (I : Ideal (𝓞 K)) : Prop :=
  ∃ hI : I ≠ ⊥, ∃ hc : idealUnit K I hI ∈ coprimeToModulus K 𝔣,
    NarrowRayClassGroup.mk K 𝔣 ⟨idealUnit K I hI, hc⟩ = C

theorem isClassOf_iff_of_mem {𝔣 : Ideal (𝓞 K)} {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hc : idealUnit K I hI ∈ coprimeToModulus K 𝔣) (C : NarrowRayClassGroup K 𝔣) :
    IsClassOf K 𝔣 C I ↔ NarrowRayClassGroup.mk K 𝔣 ⟨idealUnit K I hI, hc⟩ = C := by
  constructor
  · rintro ⟨_, _, h⟩
    exact h
  · intro h
    exact ⟨hI, hc, h⟩

theorem not_isClassOf_of_not_mem {𝔣 : Ideal (𝓞 K)} {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hc : idealUnit K I hI ∉ coprimeToModulus K 𝔣) (C : NarrowRayClassGroup K 𝔣) :
    ¬ IsClassOf K 𝔣 C I := by
  rintro ⟨_, hc', _⟩
  exact hc hc'

variable (K) in

def classSum (𝔣 : Ideal (𝓞 K)) [Fintype (NarrowRayClassGroup K 𝔣)]
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  ∑ C : NarrowRayClassGroup K 𝔣, if IsClassOf K 𝔣 C I then χ C else 0

theorem classSum_of_mem {𝔣 : Ideal (𝓞 K)} [Fintype (NarrowRayClassGroup K 𝔣)]
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hc : idealUnit K I hI ∈ coprimeToModulus K 𝔣) :
    classSum K 𝔣 χ I = χ (NarrowRayClassGroup.mk K 𝔣 ⟨idealUnit K I hI, hc⟩) := by
  unfold classSum
  rw [← Finset.sum_filter]
  have : Finset.univ.filter (fun C => IsClassOf K 𝔣 C I) =
      {NarrowRayClassGroup.mk K 𝔣 ⟨idealUnit K I hI, hc⟩} := by
    ext C
    rw [Finset.mem_filter, Finset.mem_singleton, isClassOf_iff_of_mem hI hc, eq_comm]
    simp
  rw [this, Finset.sum_singleton]

theorem classSum_of_not_mem {𝔣 : Ideal (𝓞 K)} [Fintype (NarrowRayClassGroup K 𝔣)]
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hc : idealUnit K I hI ∉ coprimeToModulus K 𝔣) : classSum K 𝔣 χ I = 0 := by
  unfold classSum
  refine Finset.sum_eq_zero fun C _ ↦ ?_
  rw [if_neg (not_isClassOf_of_not_mem hI hc C)]

section Artin

variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

theorem idealValue_eq_classSum {𝔣 : Ideal (𝓞 K)} [Fintype (NarrowRayClassGroup K 𝔣)]
    (ψ : (M ≃ₐ[K] M) →* ℂˣ) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (hχ : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣),
      χ (primeClass K 𝔣 v hv) = ArtinL.Abelian.localValue ψ v)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 → ¬ ArtinL.Abelian.IsUnramifiedAt ψ v)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ArtinL.Abelian.idealValue ψ I = classSum K 𝔣 χ I := by
  have hval : ArtinL.Abelian.idealValue ψ I =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ArtinL.Abelian.localValue ψ v ^ cnt K I v := rfl
  by_cases hc : idealUnit K I hI ∈ coprimeToModulus K 𝔣
  · rw [classSum_of_mem χ hI hc, apply_mk_eq_finprod χ hI ⟨_, hc⟩ (idealUnit_val I hI), hval]
    refine finprod_congr fun v ↦ ?_
    by_cases hv : v.asIdeal ∣ 𝔣
    · rw [(idealUnit_mem_iff I hI).1 hc v hv, pow_zero, pow_zero]
    · rw [← hχ v hv, primeCoprime, dif_neg hv]
      rfl
  · rw [classSum_of_not_mem χ hI hc, hval]
    obtain ⟨v, hv, hv0⟩ : ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 ∧ cnt K I v ≠ 0 := by
      by_contra h
      push Not at h
      exact hc ((idealUnit_mem_iff I hI).2 h)
    refine finprod_eq_zero _ v ?_ (hasFiniteMulSupport_pow_cnt hI _)
    have h0 : ArtinL.Abelian.localValue ψ v = 0 := by
      rw [ArtinL.Abelian.localValue, if_neg (hram v hv)]
    rw [h0, zero_pow hv0]

end Artin

def rayZetaEquiv (𝔣 : Ideal (𝓞 K)) (C : NarrowRayClassGroup K 𝔣) (n : ℕ) :
    {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n ∧
      ∃ hc : FractionalIdeal.mk0 K I ∈ coprimeToModulus K 𝔣,
        NarrowRayClassGroup.mk K 𝔣 ⟨FractionalIdeal.mk0 K I, hc⟩ = C} ≃
    {I : Ideal (𝓞 K) // I ∈ ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset.filter
      fun I => IsClassOf K 𝔣 C I)} where
  toFun I := ⟨(I.1 : Ideal (𝓞 K)), by
    rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    refine ⟨I.2.1, ?_⟩
    have hI : (I.1 : Ideal (𝓞 K)) ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact nonZeroDivisors.ne_zero I.1.2
    obtain ⟨hc, hC⟩ := I.2.2
    exact ⟨hI, hc, hC⟩⟩
  invFun I := ⟨⟨I.1, mem_nonZeroDivisors_of_ne_zero (by
      have h := I.2
      rw [Finset.mem_filter] at h
      rw [Ideal.zero_eq_bot]
      exact h.2.1)⟩, by
    have h := I.2
    rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h
    obtain ⟨hn, hI, hc, hC⟩ := h
    exact ⟨hn, hc, hC⟩⟩
  left_inv I := by
    ext1
    rfl
  right_inv I := by
    ext1
    rfl

theorem rayZetaCoeff_eq_card (𝔣 : Ideal (𝓞 K)) (C : NarrowRayClassGroup K 𝔣) (n : ℕ) :
    M4aTorus.rayZetaCoeff K 𝔣 C n =
      (((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset.filter
        fun I => IsClassOf K 𝔣 C I)).card := by
  rw [M4aTorus.rayZetaCoeff, Nat.card_congr (rayZetaEquiv 𝔣 C n), Nat.card_eq_finsetCard]

theorem sum_mul_rayZetaCoeff_eq (𝔣 : Ideal (𝓞 K)) [Fintype (NarrowRayClassGroup K 𝔣)]
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (n : ℕ) :
    ∑ C : NarrowRayClassGroup K 𝔣, χ C * (M4aTorus.rayZetaCoeff K 𝔣 C n : ℂ) =
      ∑ I ∈ (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset, classSum K 𝔣 χ I := by
  unfold classSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  rw [rayZetaCoeff_eq_card, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

section Artin

variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

theorem coeff_eq_sum {𝔣 : Ideal (𝓞 K)} [Fintype (NarrowRayClassGroup K 𝔣)]
    (ψ : (M ≃ₐ[K] M) →* ℂˣ) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (hχ : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣),
      χ (primeClass K 𝔣 v hv) = ArtinL.Abelian.localValue ψ v)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 → ¬ ArtinL.Abelian.IsUnramifiedAt ψ v)
    {n : ℕ} (hn : n ≠ 0) :
    ArtinL.Abelian.coeff ψ n =
      ∑ C : NarrowRayClassGroup K 𝔣, χ C * (M4aTorus.rayZetaCoeff K 𝔣 C n : ℂ) := by
  rw [sum_mul_rayZetaCoeff_eq, ArtinL.Abelian.coeff, if_neg hn]
  refine Finset.sum_congr rfl fun I hI ↦ ?_
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hI
  refine idealValue_eq_classSum ψ χ hχ hram ?_
  rintro rfl
  rw [Ideal.absNorm_bot] at hI
  exact hn hI.symm

end Artin

theorem rayZetaCoeff_le (𝔣 : Ideal (𝓞 K)) (C : NarrowRayClassGroup K 𝔣) (n : ℕ) :
    M4aTorus.rayZetaCoeff K 𝔣 C n ≤ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
  haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).to_subtype
  refine Nat.card_le_card_of_injective
    (fun I => (⟨(I.1 : Ideal (𝓞 K)), I.2.1⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n})) ?_
  intro I J h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext (Subtype.ext h)

theorem summable_rayZetaCoeff (𝔣 : Ideal (𝓞 K)) (C : NarrowRayClassGroup K 𝔣) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (M4aTorus.rayZetaCoeff K 𝔣 C n : ℂ)) s := by
  have h := summable_card_absNorm K hs
  rw [LSeriesSummable, ← summable_norm_iff] at h ⊢
  refine h.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  refine LSeries.norm_term_le s ?_
  simp only [Complex.norm_natCast, Nat.cast_le]
  exact rayZetaCoeff_le 𝔣 C n

section Artin

variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

theorem lSeries_eq (ψ : (M ≃ₐ[K] M) →* ℂˣ) {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (hχ : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣),
      χ (primeClass K 𝔣 v hv) = ArtinL.Abelian.localValue ψ v)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 → ¬ ArtinL.Abelian.IsUnramifiedAt ψ v)
    {s : ℂ} (hs : 1 < s.re) :
    ArtinL.Abelian.LSeries ψ s = M4aTorus.rayClassLSeries K 𝔣 χ s := by
  haveI : Finite (NarrowRayClassGroup K 𝔣) := Deep.NTSupply.finite K h𝔣
  haveI : Fintype (NarrowRayClassGroup K 𝔣) := Fintype.ofFinite _
  rw [M4aTorus.rayClassLSeries, tsum_fintype, ArtinL.Abelian.LSeries]
  have hsum : ∀ C ∈ (Finset.univ : Finset (NarrowRayClassGroup K 𝔣)),
      LSeriesSummable (χ C • fun n ↦ (M4aTorus.rayZetaCoeff K 𝔣 C n : ℂ)) s :=
    fun C _ ↦ (summable_rayZetaCoeff 𝔣 C hs).smul _
  have h1 : ∀ C : NarrowRayClassGroup K 𝔣, χ C * M4aTorus.rayZeta K 𝔣 C s =
      _root_.LSeries (χ C • fun n ↦ (M4aTorus.rayZetaCoeff K 𝔣 C n : ℂ)) s := fun C ↦ by
    rw [M4aTorus.rayZeta, LSeries_smul]
  simp_rw [h1]
  rw [← LSeries_sum hsum]
  refine LSeries_congr (fun {n} hn ↦ ?_) s
  rw [Finset.sum_apply, coeff_eq_sum ψ χ hχ hram hn]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  rfl

end Artin

end ArtinRayDict

end

universe u v

open NumberField IsDedekindDomain Deep.NTSupply in
theorem solution
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (hχ : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣),
      χ (primeClass K 𝔣 v hv) = ArtinL.Abelian.localValue ψ v)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 → ¬ ArtinL.Abelian.IsUnramifiedAt ψ v)
    {s : ℂ} (hs : 1 < s.re) :
    ArtinL.Abelian.LSeries ψ s = M4aTorus.rayClassLSeries K 𝔣 χ s :=
  ArtinRayDict.lSeries_eq ψ h𝔣 χ hχ hram hs

end S_ArtinL_Abelian_lSeries_eq_rayClassLSeries_of_eq_localValue
end P2MW
export P2MW.S_ArtinL_Abelian_lSeries_eq_rayClassLSeries_of_eq_localValue (solution)
