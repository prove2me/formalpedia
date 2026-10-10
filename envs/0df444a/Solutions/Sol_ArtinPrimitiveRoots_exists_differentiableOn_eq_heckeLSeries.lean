-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_differentiableOn_eq_heckeLSeries
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T11:06:23.400651+00:00
-- url     : https://prove2.me/submissions/b0c0c290-ff4b-483a-8766-89a83847882b

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_NumberField_CompletedRayL
import Definitions.Def_NumberField_RayCharacterData
import Theorems.Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
universe u

section
/-! # T12A_Sum: Dirichlet series over ideals as sums over ideals

For `f : Ideal (𝓞 K) → ℂ` bounded by `1` and `Re s > 1`, the `LSeries` whose `n`-th coefficient is
`∑ᶠ I ∈ {absNorm I = n}, f I` is the (absolutely convergent) sum `∑' I, f I * N(I)^{-s}`. -/

set_option maxHeartbeats 4000000
set_option autoImplicit false

open NumberField Complex Filter Topology Ideal

namespace ArtinPrimitiveRoots.T12A

variable {K : Type*} [Field K] [NumberField K]

theorem lseriesSummable_card {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := s) hs
  simpa using h

instance finite_fiber (n : ℕ) : Finite {I : Ideal (𝓞 K) // absNorm I = n} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton {I : Ideal (𝓞 K) // absNorm I = 0} :=
      ⟨fun a b => Subtype.ext (by
        rw [Ideal.absNorm_eq_zero_iff.mp a.2, Ideal.absNorm_eq_zero_iff.mp b.2])⟩
    exact Finite.of_subsingleton
  · exact (finite_setOfPred_absNorm_eq n).to_subtype

/-- The norms `‖N(I)^{-s}‖` are summable over all ideals when `Re s > 1`. -/
theorem summable_norm_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 K) ↦ ‖(absNorm I : ℂ) ^ (-s)‖) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, zero_re] at hs; linarith
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun n ↦ Summable.of_finite, ?_⟩
  have key : ∀ n : ℕ, ∑' I : {I : Ideal (𝓞 K) // absNorm I = n},
      ‖(absNorm (e ⟨n, I⟩) : ℂ) ^ (-s)‖ =
      ‖LSeries.term (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s n‖ := by
    intro n
    have : ∀ I : {I : Ideal (𝓞 K) // absNorm I = n},
        ‖(absNorm (e ⟨n, I⟩) : ℂ) ^ (-s)‖ = ‖(n : ℂ) ^ (-s)‖ := by
      intro I
      show ‖(absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)‖ = _
      rw [I.2]
    rw [tsum_congr this, tsum_const, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term_zero, zero_cpow (neg_ne_zero.mpr hs0)]
    · rw [LSeries.term_of_ne_zero hn.ne', norm_div, cpow_neg, norm_inv, div_eq_mul_inv,
        norm_natCast]
  simp_rw [key]
  exact (lseriesSummable_card hs).norm

/-- **Sum over ideals.** -/
theorem hasSum_ideal (f : Ideal (𝓞 K) → ℂ) (hf : ∀ I, ‖f I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I ↦ f I * (absNorm I : ℂ) ^ (-s))
      (LSeries (fun n ↦ ∑ᶠ I ∈ {I : Ideal (𝓞 K) | absNorm I = n}, f I) s) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, zero_re] at hs; linarith
  have hsum : Summable (fun I : Ideal (𝓞 K) ↦ f I * (absNorm I : ℂ) ^ (-s)) := by
    refine Summable.of_norm_bounded (summable_norm_cpow hs) fun I ↦ ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hf I)
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ absNorm I)
  have h1 := (e.hasSum_iff.mpr hsum.hasSum).sigma (fun n ↦ (Summable.of_finite).hasSum)
  suffices hval : LSeries (fun n ↦ ∑ᶠ I ∈ {I : Ideal (𝓞 K) | absNorm I = n}, f I) s =
      ∑' I, f I * (absNorm I : ℂ) ^ (-s) by
    rw [hval]; exact hsum.hasSum
  rw [← h1.tsum_eq, LSeries]
  congr 1
  funext n
  have hfin : ∑ᶠ I ∈ {I : Ideal (𝓞 K) | absNorm I = n}, f I =
      ∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, f I := by
    rw [← finsum_set_coe_eq_finsum_mem, tsum_eq_finsum (Set.toFinite _)]
    rfl
  have hterm : ∀ I : {I : Ideal (𝓞 K) // absNorm I = n},
      f (e ⟨n, I⟩) * (absNorm (e ⟨n, I⟩) : ℂ) ^ (-s) = f I * (n : ℂ) ^ (-s) := by
    intro I
    show f I * (absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s) = _
    rw [I.2]
  show _ = ∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, f (e ⟨n, I⟩) * (absNorm (e ⟨n, I⟩) : ℂ) ^ (-s)
  rw [tsum_congr hterm, tsum_mul_right, ← hfin]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero, zero_cpow (neg_ne_zero.mpr hs0)]
  · rw [LSeries.term_of_ne_zero hn.ne', cpow_neg, div_eq_mul_inv]

end ArtinPrimitiveRoots.T12A
end

section
/-! # T12A_Ray: a `HeckeChar` as a narrow ray class character

A `HeckeChar K 𝔪` (𝔪 ≠ ⊥) is `I ↦ ψ([I])` on ideals coprime to `𝔪` for a character `ψ` of the narrow
ray class group mod `𝔪` with parity set `∅`, and `χ.LSeries = rayClassLSeries ψ` on `Re s > 1`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply nonZeroDivisors Complex

namespace ArtinPrimitiveRoots.T12A

section Coprime

variable {F : Type*} [Field F] [NumberField F]

theorem sup_eq_top_iff_forall {I 𝔣 : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    I ⊔ 𝔣 = ⊤ ↔ ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ 𝔣 → ¬ v.asIdeal ∣ I := by
  constructor
  · intro h v hf hI'
    apply v.isPrime.ne_top
    rw [eq_top_iff, ← h]
    exact sup_le (Ideal.le_of_dvd hI') (Ideal.le_of_dvd hf)
  · intro h
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmb : m ≠ ⊥ := by
      intro hb
      apply hI
      rw [eq_bot_iff, ← hb]
      exact le_trans le_sup_left hle
    let v : HeightOneSpectrum (𝓞 F) := ⟨m, hm.isPrime, hmb⟩
    exact h v (Ideal.dvd_iff_le.mpr (le_trans le_sup_right hle))
      (Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle))

theorem mk0_mem_coprimeToModulus_iff {I 𝔣 : Ideal (𝓞 F)} (hI : I ∈ (Ideal (𝓞 F))⁰) :
    FractionalIdeal.mk0 F ⟨I, hI⟩ ∈ coprimeToModulus F 𝔣 ↔ I ⊔ 𝔣 = ⊤ := by
  have hI0 : I ≠ 0 := nonZeroDivisors.ne_zero hI
  rw [mem_coprimeToModulus_iff, sup_eq_top_iff_forall hI0]
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.count_coe F v hI0, Nat.cast_eq_zero]
  constructor
  · intro h hd
    exact (Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mpr hd h
  · intro h
    by_contra hc
    exact h ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hc)

theorem span_ne_bot {α : 𝓞 F} (hα : α ≠ 0) : Ideal.span {α} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact hα

theorem span_sup_eq_top {𝔣 : Ideal (𝓞 F)} {α : 𝓞 F} (h1 : α - 1 ∈ 𝔣) :
    Ideal.span {α} ⊔ 𝔣 = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h : (1 : 𝓞 F) = α - (α - 1) := by ring
  rw [h]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self α))
    (Ideal.mem_sup_right h1)

end Coprime

section Factor

variable {F : Type*} [Field F] [NumberField F] {𝔣 : Ideal (𝓞 F)}

theorem hasFiniteMulSupport_pow_count (f : HeightOneSpectrum (𝓞 F) → ℂ) {I : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      f v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  by_contra hd
  apply hv
  have : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
    by_contra hc
    exact hd ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hc)
  simp only [this, pow_zero]

open Classical in
theorem count_prime_eq (v w : HeightOneSpectrum (𝓞 F)) :
    (Associates.mk v.asIdeal).count (Associates.mk w.asIdeal).factors = if v = w then 1 else 0 := by
  split_ifs with h
  · subst h
    exact Associates.count_self v.associates_irreducible
  · by_contra hc
    have hd := (Associates.count_ne_zero_iff_dvd w.ne_bot v.irreducible).mp hc
    apply h
    exact HeightOneSpectrum.ext
      ((w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd hd)).symm)

/-- A `HeckeChar` is determined on nonzero ideals by its values at primes. -/
theorem heckeChar_eq_finprod (η : ArtinPrimitiveRoots.HeckeChar F 𝔣)
    (f : HeightOneSpectrum (𝓞 F) → ℂ) (hf : ∀ v : HeightOneSpectrum (𝓞 F), η.toFun v.asIdeal = f v)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    η.toFun I = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      f v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  revert hI
  refine UniqueFactorizationMonoid.induction_on_prime I ?_ ?_ ?_
  · intro h
    exact absurd rfl h
  · intro x hx _
    rw [Ideal.isUnit_iff] at hx
    subst hx
    have h1 : η.toFun ⊤ = 1 := by
      have := η.map_principal' 1 one_ne_zero (by rw [sub_self]; exact Ideal.zero_mem _)
      rwa [Ideal.span_singleton_one] at this
    rw [h1, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
    exact (finprod_eq_one_of_forall_eq_one fun v => by
      rw [Associates.count_zero v.associates_irreducible, pow_zero]).symm
  · intro a p ha hp ih hpa
    have ha' : a ≠ ⊥ := ha
    let v₀ : HeightOneSpectrum (𝓞 F) := HeightOneSpectrum.ofPrime hp
    have hp0 : p ≠ 0 := hp.ne_zero
    rw [η.map_mul', ih ha']
    have hcount : ∀ v : HeightOneSpectrum (𝓞 F),
        (Associates.mk v.asIdeal).count (Associates.mk (p * a)).factors =
          (Associates.mk v.asIdeal).count (Associates.mk p).factors +
            (Associates.mk v.asIdeal).count (Associates.mk a).factors := by
      intro v
      rw [← Associates.mk_mul_mk]
      exact Associates.count_mul (Associates.mk_ne_zero.mpr hp0) (Associates.mk_ne_zero.mpr ha)
        v.associates_irreducible
    simp_rw [hcount, pow_add]
    rw [finprod_mul_distrib (hasFiniteMulSupport_pow_count f (I := p) hp0)
      (hasFiniteMulSupport_pow_count f ha')]
    congr 1
    have hp' : p = v₀.asIdeal := rfl
    rw [hp', hf v₀, finprod_eq_single _ v₀]
    · rw [count_prime_eq, if_pos rfl, pow_one]
    · intro v hv
      rw [count_prime_eq, if_neg hv, pow_zero]

end Factor

section Ray

variable {K : Type} [Field K] [NumberField K] {𝔪 : Ideal (𝓞 K)}

theorem heckeChar_ne_zero (χ : HeckeChar K 𝔪) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hc : I ⊔ 𝔪 = ⊤) : χ.toFun I ≠ 0 := by
  rw [Ne, χ.eq_zero_iff']
  tauto

theorem heckeChar_eq_zero (χ : HeckeChar K 𝔪) {I : Ideal (𝓞 K)}
    (h : ¬ (I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤)) : χ.toFun I = 0 := by
  rw [χ.eq_zero_iff']
  tauto

open Classical in
/-- The values of `χ` at primes, as units (`1` at primes dividing `𝔪`). -/
noncomputable def primeVal (χ : HeckeChar K 𝔪) (v : HeightOneSpectrum (𝓞 K)) : ℂˣ :=
  if h : v.asIdeal ⊔ 𝔪 = ⊤ then Units.mk0 (χ.toFun v.asIdeal) (heckeChar_ne_zero χ v.ne_bot h)
  else 1

theorem raySymbol_coe (χ : HeckeChar K 𝔪) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hc : I ⊔ 𝔪 = ⊤) :
    ((raySymbol K (primeVal χ) (I : FractionalIdeal (𝓞 K)⁰ K) : ℂˣ) : ℂ) = χ.toFun I := by
  rw [heckeChar_eq_finprod χ (fun v => χ.toFun v.asIdeal) (fun v => rfl) I hI, raySymbol,
    ← Units.coeHom_apply, MonoidHom.map_finprod _ (hasFiniteMulSupport_raySymbol_factors K _ _)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_coe K v hI, zpow_natCast, Units.coeHom_apply, Units.val_pow_eq_pow_val]
  by_cases hd : v.asIdeal ∣ I
  · have hv : v.asIdeal ⊔ 𝔪 = ⊤ :=
      eq_top_iff.mpr (hc ▸ sup_le_sup_right (Ideal.le_of_dvd hd) _)
    rw [primeVal, dif_pos hv, Units.val_mk0]
  · have : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
      by_contra h0
      exact hd ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp h0)
    rw [this, pow_zero, pow_zero]

theorem hkill (χ : HeckeChar K 𝔪) : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔪 →
    (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
    raySymbol K (primeVal χ) ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1 := by
  intro α hα h1 _
  apply Units.ext
  rw [raySymbol_coe χ (span_ne_bot hα) (span_sup_eq_top h1), Units.val_one]
  exact χ.map_principal' α hα h1

/-- The narrow ray class character attached to `χ`. -/
noncomputable def rayChar (χ : HeckeChar K 𝔪) : NarrowRayClassGroup K 𝔪 →* ℂ :=
  (Units.coeHom ℂ).comp (raySymbolDescend K (primeVal χ) (hkill χ))

theorem rayChar_mk (χ : HeckeChar K 𝔪) (y : ↥(coprimeToModulus K 𝔪)) :
    rayChar χ (NarrowRayClassGroup.mk K 𝔪 y) =
      ((raySymbol K (primeVal χ)
        ((y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) : ℂˣ) : ℂ) := by
  rw [rayChar, MonoidHom.comp_apply, raySymbolDescend_mk, raySymbolHom_apply, Units.coeHom_apply]

theorem rayChar_mk_ideal (χ : HeckeChar K 𝔪) {I : Ideal (𝓞 K)} (hI : I ∈ (Ideal (𝓞 K))⁰)
    (hc : FractionalIdeal.mk0 K ⟨I, hI⟩ ∈ coprimeToModulus K 𝔪) :
    rayChar χ (NarrowRayClassGroup.mk K 𝔪 ⟨FractionalIdeal.mk0 K ⟨I, hI⟩, hc⟩) = χ.toFun I := by
  rw [rayChar_mk]
  show ((raySymbol K (primeVal χ) ((FractionalIdeal.mk0 K ⟨I, hI⟩ :
    (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) : ℂˣ) : ℂ) = _
  rw [FractionalIdeal.coe_mk0]
  exact raySymbol_coe χ (nonZeroDivisors.ne_zero hI) ((mk0_mem_coprimeToModulus_iff hI).1 hc)

theorem isParity (χ : HeckeChar K 𝔪) : M4aP2.IsParity K 𝔪 (rayChar χ) ∅ := by
  intro α hα h1
  have hne : ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
    exact hα
  have hcop : Units.mk0 _ hne ∈ coprimeToModulus K 𝔪 := by
    have h := principalUnit_mem_coprimeToModulus K hα h1
    rw [mem_coprimeToModulus_iff] at h ⊢
    intro v hv
    have := h v hv
    rwa [principalUnit_val] at this
  rw [M4aP2.chiIdeal, dif_pos hne, dif_pos hcop, rayChar_mk, M4aP2.signAt, Finset.prod_empty]
  show ((raySymbol K (primeVal χ) ((Units.mk0 _ hne :
    (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) : ℂˣ) : ℂ) = 1
  rw [Units.val_mk0, raySymbol_coe χ (span_ne_bot hα) (span_sup_eq_top h1)]
  exact χ.map_principal' α hα h1

theorem norm_rayChar (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar K 𝔪) (C : NarrowRayClassGroup K 𝔪) :
    ‖rayChar χ C‖ = 1 := by
  haveI := Deep.NTSupply.finite K h𝔪
  have h : rayChar χ C ^ Nat.card (NarrowRayClassGroup K 𝔪) = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  exact norm_eq_one_of_pow_eq_one h Nat.card_pos.ne'

open Classical in
/-- The class of an ideal (`1` when it is zero or not coprime to `𝔪`). -/
noncomputable def cls (𝔪 : Ideal (𝓞 K)) (I : Ideal (𝓞 K)) : NarrowRayClassGroup K 𝔪 :=
  if h : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ then
    NarrowRayClassGroup.mk K 𝔪 ⟨FractionalIdeal.mk0 K ⟨I, mem_nonZeroDivisors_of_ne_zero h.1⟩,
      (mk0_mem_coprimeToModulus_iff _).2 h.2⟩
  else 1

open Classical in
theorem heckeChar_eq_ite (χ : HeckeChar K 𝔪) (I : Ideal (𝓞 K)) :
    χ.toFun I = if I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ then rayChar χ (cls 𝔪 I) else 0 := by
  split_ifs with h
  · rw [cls, dif_pos h, rayChar_mk_ideal]
  · exact heckeChar_eq_zero χ h

theorem norm_heckeChar_le (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar K 𝔪) (I : Ideal (𝓞 K)) :
    ‖χ.toFun I‖ ≤ 1 := by
  rw [heckeChar_eq_ite]
  split_ifs
  · rw [norm_rayChar h𝔪]
  · simp

open Classical in
theorem rayZetaCoeff_eq (C : NarrowRayClassGroup K 𝔪) {n : ℕ} (hn : n ≠ 0) :
    M4aTorus.rayZetaCoeff K 𝔪 C n =
      ((Ideal.finite_setOfPred_absNorm_eq n).toFinset.filter
        (fun I => (I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤) ∧ cls 𝔪 I = C)).card := by
  rw [M4aTorus.rayZetaCoeff, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, ?_⟩
      invFun := fun y => ⟨⟨y.1, mem_nonZeroDivisors_of_ne_zero ?_⟩, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  · obtain ⟨⟨I, hI⟩, hn', hc, hC⟩ := x
    have hcop := (mk0_mem_coprimeToModulus_iff hI).1 hc
    have hgood : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ := ⟨nonZeroDivisors.ne_zero hI, hcop⟩
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨hn', hgood, ?_⟩
    rw [cls, dif_pos hgood]
    exact hC
  · have h := y.2
    rw [Finset.mem_filter] at h
    exact h.2.1.1
  · have h := y.2
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at h
    refine ⟨h.1, (mk0_mem_coprimeToModulus_iff _).2 h.2.1.2, ?_⟩
    have hC := h.2.2
    rw [cls, dif_pos h.2.1] at hC
    exact hC

open Classical in
theorem coeff_sum (χ : HeckeChar K 𝔪) [Fintype (NarrowRayClassGroup K 𝔪)] {n : ℕ} (hn : n ≠ 0) :
    ∑ C, rayChar χ C * (M4aTorus.rayZetaCoeff K 𝔪 C n : ℂ) = χ.coeff n := by
  set S := (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset
  have h1 : ∀ C, rayChar χ C * (M4aTorus.rayZetaCoeff K 𝔪 C n : ℂ) =
      ∑ I ∈ (S.filter (fun I => I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤)).filter (fun I => cls 𝔪 I = C),
        rayChar χ (cls 𝔪 I) := by
    intro C
    rw [rayZetaCoeff_eq C hn, Finset.filter_filter]
    rw [Finset.sum_congr rfl (g := fun _ => rayChar χ C) (fun I hI => by
      rw [(Finset.mem_filter.mp hI).2.2]), Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl (fun C _ => h1 C), Finset.sum_fiberwise, HeckeChar.coeff,
    finsum_mem_eq_finite_toFinset_sum _ (Ideal.finite_setOfPred_absNorm_eq n),
    Finset.sum_filter]
  exact Finset.sum_congr rfl fun I _ => (heckeChar_eq_ite χ I).symm

open Classical in
theorem lseriesSummable_rayZetaCoeff (C : NarrowRayClassGroup K 𝔪) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (M4aTorus.rayZetaCoeff K 𝔪 C n : ℂ)) s := by
  refine Summable.of_norm_bounded (lseriesSummable_card (K := K) hs).norm fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  refine LSeries.norm_term_le s ?_
  rw [norm_natCast, norm_natCast, Nat.cast_le, rayZetaCoeff_eq C hn.ne']
  have hc : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} =
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset.card :=
    Nat.card_eq_card_finite_toFinset (Ideal.finite_setOfPred_absNorm_eq n)
  rw [hc]
  exact Finset.card_filter_le _ _

theorem rayClassLSeries_eq (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar K 𝔪) {s : ℂ} (hs : 1 < s.re) :
    M4aTorus.rayClassLSeries K 𝔪 (rayChar χ) s = χ.LSeries s := by
  haveI := Deep.NTSupply.finite K h𝔪
  letI : Fintype (NarrowRayClassGroup K 𝔪) := Fintype.ofFinite _
  classical
  rw [M4aTorus.rayClassLSeries, tsum_fintype]
  simp_rw [M4aTorus.rayZeta, ← LSeries_smul]
  rw [← LSeries_sum (fun C _ => (lseriesSummable_rayZetaCoeff C hs).smul _), HeckeChar.LSeries]
  refine LSeries_congr (fun {n} hn => ?_) s
  rw [Finset.sum_apply]
  simp_rw [Pi.smul_apply, smul_eq_mul]
  exact coeff_sum χ hn

end Ray

end ArtinPrimitiveRoots.T12A
end

section
/-! # T12A_Prin: removing Euler factors from `ζ_K`

For a finite set `T` of primes and `Re s > 1`,
`∑_{I coprime to T} N(I)^{-s} = ∏_{v ∈ T} (1 - N(v)^{-s}) · ζ_K(s)`. -/

set_option maxHeartbeats 4000000
set_option autoImplicit false

open NumberField Complex Ideal IsDedekindDomain

namespace ArtinPrimitiveRoots.T12A

variable {K : Type*} [Field K] [NumberField K]

open Classical in
/-- `1` on ideals divisible by no prime of `T`, `0` otherwise. -/
noncomputable def coprimeInd (T : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K)) : ℂ :=
  if ∀ v ∈ T, ¬ v.asIdeal ∣ I then 1 else 0

theorem norm_coprimeInd_le (T : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K)) :
    ‖coprimeInd T I‖ ≤ 1 := by
  unfold coprimeInd
  split_ifs <;> simp

/-- The partial zeta function of ideals coprime to `T`. -/
noncomputable def zetaCop (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∑' I : Ideal (𝓞 K), coprimeInd T I * (absNorm I : ℂ) ^ (-s)

theorem summable_bounded (c : Ideal (𝓞 K) → ℂ) (hc : ∀ I, ‖c I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 K) ↦ c I * (absNorm I : ℂ) ^ (-s)) := by
  refine Summable.of_norm_bounded (summable_norm_cpow hs) fun I ↦ ?_
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hc I)

theorem zetaCop_empty {s : ℂ} (hs : 1 < s.re) : zetaCop (K := K) ∅ s = dedekindZeta K s := by
  have h := hasSum_ideal (K := K) (fun _ ↦ (1 : ℂ)) (fun _ ↦ by simp) hs
  have hind : ∀ I : Ideal (𝓞 K), coprimeInd ∅ I = 1 := fun I ↦ by simp [coprimeInd]
  rw [zetaCop]
  simp_rw [hind]
  rw [h.tsum_eq, dedekindZeta]
  refine LSeries_congr (fun {n} _ ↦ ?_) s
  rw [finsum_mem_eq_finite_toFinset_sum _ (Ideal.finite_setOfPred_absNorm_eq n),
    Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} =
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset.card :=
    Nat.card_eq_card_finite_toFinset (Ideal.finite_setOfPred_absNorm_eq n)
  rw [hc]

theorem dvd_mul_iff_of_ne {v w : HeightOneSpectrum (𝓞 K)} (hvw : v ≠ w) (J : Ideal (𝓞 K)) :
    w.asIdeal ∣ v.asIdeal * J ↔ w.asIdeal ∣ J := by
  constructor
  · intro h
    rcases (Ideal.prime_of_isPrime w.ne_bot w.isPrime).dvd_or_dvd h with h' | h'
    · exfalso
      apply hvw
      exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.le_of_dvd h'))
    · exact h'
  · exact fun h ↦ dvd_mul_of_dvd_right h _

theorem coprimeInd_mul {T : Finset (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ T) (J : Ideal (𝓞 K)) : coprimeInd T (v.asIdeal * J) = coprimeInd T J := by
  have : (∀ w ∈ T, ¬ w.asIdeal ∣ v.asIdeal * J) ↔ (∀ w ∈ T, ¬ w.asIdeal ∣ J) := by
    refine forall₂_congr fun w hw ↦ ?_
    rw [dvd_mul_iff_of_ne (fun h ↦ hv (by rw [h]; exact hw))]
  unfold coprimeInd
  by_cases h : ∀ w ∈ T, ¬ w.asIdeal ∣ J
  · rw [if_pos (this.mpr h), if_pos h]
  · rw [if_neg (fun h' ↦ h (this.mp h')), if_neg h]

open Classical in
theorem zetaCop_insert {T : Finset (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ T) {s : ℂ} (hs : 1 < s.re) :
    zetaCop (insert v T) s = (1 - (absNorm v.asIdeal : ℂ) ^ (-s)) * zetaCop T s := by
  set b : Ideal (𝓞 K) → ℂ := fun I ↦
    (if v.asIdeal ∣ I then coprimeInd T I else 0) * (absNorm I : ℂ) ^ (-s) with hb
  have hsplit : ∀ I, coprimeInd T I * (absNorm I : ℂ) ^ (-s) =
      coprimeInd (insert v T) I * (absNorm I : ℂ) ^ (-s) + b I := by
    intro I
    rw [hb, ← add_mul]
    congr 1
    unfold coprimeInd
    by_cases hd : v.asIdeal ∣ I
    · have : ¬ ∀ w ∈ insert v T, ¬ w.asIdeal ∣ I := fun h ↦ h v (Finset.mem_insert_self v T) hd
      rw [if_neg this, if_pos hd, zero_add]
    · rw [if_neg hd, add_zero]
      congr 1
      simp only [Finset.mem_insert, forall_eq_or_imp, eq_iff_iff]
      exact ⟨fun h ↦ ⟨hd, h⟩, fun h ↦ h.2⟩
  have hbsum : Summable b := by
    refine summable_bounded (fun I ↦ if v.asIdeal ∣ I then coprimeInd T I else 0) (fun I ↦ ?_) hs
    split_ifs
    · exact norm_coprimeInd_le T I
    · simp
  have hinj : Function.Injective (fun J : Ideal (𝓞 K) ↦ v.asIdeal * J) := fun J₁ J₂ h ↦
    mul_left_cancel₀ (show v.asIdeal ≠ 0 from v.ne_bot) h
  have hsupp : Function.support b ⊆ Set.range (fun J : Ideal (𝓞 K) ↦ v.asIdeal * J) := by
    intro I hI
    by_contra hr
    apply hI
    have hd : ¬ v.asIdeal ∣ I := by
      rintro ⟨J, rfl⟩
      exact hr ⟨J, rfl⟩
    rw [hb]
    simp only [if_neg hd, zero_mul]
  have hbt : ∑' I, b I = (absNorm v.asIdeal : ℂ) ^ (-s) * zetaCop T s := by
    rw [← hinj.tsum_eq hsupp, zetaCop, ← tsum_mul_left]
    refine tsum_congr fun J ↦ ?_
    rw [hb]
    simp only [dvd_mul_right, if_true]
    rw [coprimeInd_mul hv, map_mul, Nat.cast_mul, natCast_mul_natCast_cpow]
    ring
  have h := (summable_bounded _ (norm_coprimeInd_le (insert v T)) hs).tsum_add hbsum
  rw [← tsum_congr hsplit, ← zetaCop, ← zetaCop, hbt] at h
  linear_combination -h

open Classical in
theorem zetaCop_eq (T : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    zetaCop T s = (∏ v ∈ T, (1 - (absNorm v.asIdeal : ℂ) ^ (-s))) * dedekindZeta K s := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, one_mul, zetaCop_empty hs]
  | insert v T hv ih => rw [zetaCop_insert hv hs, ih, Finset.prod_insert hv, mul_assoc]

end ArtinPrimitiveRoots.T12A
end

section
/-! # T12A_Main: continuation of `HeckeChar.LSeries` (cut T1)

* nontrivial ray class character: entire, by 17728196 (`IsParity` with `S = ∅`);
* trivial: `L(s, χ) = ∏_{v ∣ 𝔪} (1 - N v^{-s}) · ζ_K(s)`, continued by 8087d96f;
* a field in an arbitrary universe is moved to `Type` along a ring isomorphism. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply Complex

namespace ArtinPrimitiveRoots

namespace T12A

section Principal

variable {K : Type} [Field K] [NumberField K] {𝔪 : Ideal (𝓞 K)}

theorem principal_LSeries (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar K 𝔪) (hψ : rayChar χ = 1) {s : ℂ}
    (hs : 1 < s.re) :
    χ.LSeries s = (∏ v ∈ (Ideal.finite_factors (R := 𝓞 K) h𝔪).toFinset,
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) * dedekindZeta K s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, zero_re] at hs; linarith
  rw [← zetaCop_eq _ hs, HeckeChar.LSeries]
  unfold HeckeChar.coeff
  rw [← (hasSum_ideal χ.toFun (norm_heckeChar_le h𝔪 χ) hs).tsum_eq, zetaCop]
  refine tsum_congr fun I => ?_
  by_cases hI : I = ⊥
  · subst hI
    simp [zero_cpow (neg_ne_zero.mpr hs0)]
  congr 1
  rw [heckeChar_eq_ite, coprimeInd, hψ, MonoidHom.one_apply]
  have : (I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤) ↔
      ∀ v ∈ (Ideal.finite_factors (R := 𝓞 K) h𝔪).toFinset, ¬ v.asIdeal ∣ I := by
    rw [sup_eq_top_iff_forall hI]
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨hI, h⟩⟩
  by_cases h : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤
  · rw [if_pos h, if_pos (this.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]

/-- T1 for a number field in `Type`. -/
theorem continuation_type (K : Type) [Field K] [NumberField K]
    (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar K 𝔪) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {s | s ≠ 1} ∧ ∀ s : ℂ, 1 < s.re → g s = χ.LSeries s := by
  by_cases hψ : rayChar χ = 1
  · obtain ⟨R, hR, -, hReq, -⟩ :=
      NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K
    set T := (Ideal.finite_factors (R := 𝓞 K) h𝔪).toFinset
    refine ⟨fun s => (∏ v ∈ T, (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) * (R s / (s - 1)),
      ?_, ?_⟩
    · have hP : Differentiable ℂ
          (fun s : ℂ => ∏ v ∈ T, (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) := by
        refine Differentiable.fun_finsetProd fun v _ => ?_
        refine (differentiable_const _).sub (Differentiable.const_cpow differentiable_neg ?_)
        left
        rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
        exact v.ne_bot
      refine hP.differentiableOn.mul (hR.differentiableOn.div
        (differentiableOn_id.sub (differentiableOn_const _)) fun s hs => sub_ne_zero.mpr hs)
    · intro s hs
      have hs1 : s ≠ 1 := by
        intro h; rw [h, one_re] at hs; exact lt_irrefl _ hs
      dsimp only
      rw [principal_LSeries h𝔪 χ hψ hs, hReq s hs,
        mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs1)]
  · obtain ⟨g, hg, heq⟩ := NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one K 𝔪 h𝔪
      (rayChar χ) hψ ∅ (isParity χ)
    exact ⟨g, hg.differentiableOn, fun s hs => (heq s hs).trans (rayClassLSeries_eq h𝔪 χ hs)⟩

end Principal

section Transport


theorem exists_small_model (F : Type u) [Field F] [NumberField F] :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : NumberField F₀), Nonempty (F₀ ≃+* F) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  haveI : Fact (Irreducible (minpoly ℚ α)) := ⟨minpoly.irreducible hint⟩
  let e : AdjoinRoot (minpoly ℚ α) ≃ₐ[ℚ] F :=
    (IntermediateField.adjoinRootEquivAdjoin ℚ hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly ℚ α)) :=
    LinearEquiv.finiteDimensional e.toLinearEquiv.symm
  haveI : NumberField (AdjoinRoot (minpoly ℚ α)) := { }
  exact ⟨_, inferInstance, inferInstance, ⟨e.toRingEquiv⟩⟩

theorem absNorm_map_ringEquiv {F : Type} {F' : Type u} [Field F] [NumberField F] [Field F']
    [NumberField F'] (f : 𝓞 F ≃+* 𝓞 F') (I : Ideal (𝓞 F)) :
    Ideal.absNorm (I.map f) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (I.map f) f rfl).toEquiv).symm

/-- Transport of a `HeckeChar` along a ring isomorphism of number fields. -/
theorem heckeChar_transport {F : Type} {F' : Type u} [Field F] [NumberField F] [Field F']
    [NumberField F'] (e : F ≃+* F') {𝔣' : Ideal (𝓞 F')} (h𝔣 : 𝔣' ≠ ⊥)
    (η' : ArtinPrimitiveRoots.HeckeChar F' 𝔣') :
    ∃ 𝔣 : Ideal (𝓞 F), 𝔣 ≠ ⊥ ∧ ∃ η : ArtinPrimitiveRoots.HeckeChar F 𝔣,
      η.LSeries = η'.LSeries := by
  set f : 𝓞 F ≃+* 𝓞 F' := RingOfIntegers.mapRingEquiv e
  have h1 : ∀ I : Ideal (𝓞 F), (I.map f).map f.symm = I := fun I => Ideal.map_of_equiv f
  have h2 : ∀ J : Ideal (𝓞 F'), (J.map f.symm).map f = J := fun J => by
    have := Ideal.map_of_equiv (I := J) f.symm; rwa [RingEquiv.symm_symm] at this
  have htop : ∀ I : Ideal (𝓞 F), I.map f = ⊤ ↔ I = ⊤ := fun I => by
    constructor
    · intro h; rw [← h1 I, h, Ideal.map_top]
    · rintro rfl; exact Ideal.map_top _
  have hbot : ∀ I : Ideal (𝓞 F), I.map f = ⊥ ↔ I = ⊥ := fun I =>
    Ideal.map_eq_bot_iff_of_injective f.injective
  have hmc : (𝔣'.comap f).map f = 𝔣' := Ideal.map_comap_of_surjective _ f.surjective _
  refine ⟨𝔣'.comap f, fun h => h𝔣 (by rw [← hmc, h, Ideal.map_bot]), ?_⟩
  refine ⟨{ toFun := fun I => η'.toFun (I.map f)
            map_mul' := fun I J => by rw [Ideal.map_mul]; exact η'.map_mul' _ _
            eq_zero_iff' := fun I => by
              have hsup : I.map f ⊔ 𝔣' = (I ⊔ 𝔣'.comap f).map f := by
                rw [Ideal.map_sup, hmc]
              rw [η'.eq_zero_iff', hbot, hsup, Ne, htop]
            map_principal' := fun α hα h1α => by
              rw [Ideal.map_span, Set.image_singleton]
              refine η'.map_principal' (f α) (by simpa using hα) ?_
              rw [← map_one f, ← map_sub]
              exact h1α }, ?_⟩
  funext s
  refine LSeries_congr (fun {n} _ => ?_) s
  unfold ArtinPrimitiveRoots.HeckeChar.coeff
  refine finsum_mem_eq_of_bijOn (fun I => I.map f) ⟨?_, ?_, ?_⟩ (fun I _ => rfl)
  · intro I hI
    simp only [Set.mem_ofPred_eq] at hI ⊢
    rw [absNorm_map_ringEquiv, hI]
  · intro I _ J _ hIJ
    rw [← h1 I, ← h1 J]
    exact congrArg (Ideal.map f.symm) hIJ
  · intro J hJ
    refine ⟨J.map f.symm, ?_, h2 J⟩
    simp only [Set.mem_ofPred_eq] at hJ ⊢
    rw [← hJ, ← absNorm_map_ringEquiv f, h2]

end Transport

end T12A

end ArtinPrimitiveRoots

end

section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open NumberField IsDedekindDomain Deep.NTSupply Complex
open ArtinPrimitiveRoots
open T12A in
theorem solution (F : Type*) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {s | s ≠ 1} ∧ ∀ s : ℂ, 1 < s.re → g s = χ.LSeries s := by
  obtain ⟨F₀, _, _, ⟨e⟩⟩ := exists_small_model F
  obtain ⟨𝔣, h𝔣, η, hη⟩ := heckeChar_transport e h𝔪 χ
  obtain ⟨g, hg, heq⟩ := continuation_type F₀ 𝔣 h𝔣 η
  exact ⟨g, hg, fun s hs => (heq s hs).trans (congrFun hη s)⟩
end
