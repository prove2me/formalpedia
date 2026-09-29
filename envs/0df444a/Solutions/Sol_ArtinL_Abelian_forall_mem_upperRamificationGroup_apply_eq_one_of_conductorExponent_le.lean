-- Prove2me | solution 1 for ArtinL.Abelian.forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/fb3eaa23-7a68-59d9-9035-c60676215b2c

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Theorems.Thm_Ideal_inertia_pow_succ_eq_map_lowerRamificationGroup_of_dense
import Theorems.Thm_IsLocalRing_forall_mem_upperRamificationGroup_iff_finsum_indicator_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le

set_option autoImplicit false

open NumberField IsDedekindDomain

universe u v

namespace ArtinL
p2m_export "ArtinL" "Abelian.inertiaGroup Abelian.ramificationGroup Abelian.IsUnramifiedAt Abelian.swanConductor Abelian.conductorExponent"
namespace Abelian
p2m_export "ArtinL.Abelian" "inertiaGroup ramificationGroup IsUnramifiedAt swanConductor conductorExponent conductor"
namespace ValBridge
p2m_open "ArtinL.Abelian ArtinL"

open IsDedekindDomain IsLocalRing

section withZero

theorem exp_lt_exp_iff_le (m n : ℤ) : (WithZero.exp m : WithZero (Multiplicative ℤ)) < WithZero.exp n ↔ WithZero.exp m ≤ WithZero.exp (n - 1) := by
  rw [WithZero.exp_lt_exp, WithZero.exp_le_exp]
  omega

theorem lt_exp_iff_le_exp_sub_one (x : WithZero (Multiplicative ℤ)) (n : ℤ) : x < WithZero.exp n ↔ x ≤ WithZero.exp (n - 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← WithZero.exp_log hx]
    exact exp_lt_exp_iff_le _ _

end withZero

section dvr

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

noncomputable abbrev VA : ValuationSubring K := (v.valuation K).valuationSubring

theorem coe_mem_iff (x : K) : x ∈ VA K v ↔ v.valuation K x ≤ 1 := Valuation.mem_valuationSubring_iff _ _

theorem exists_uniformizer : ∃ π : VA K v, v.valuation K (π : K) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  refine ⟨⟨π, (coe_mem_iff K v π).2 ?_⟩, hπ⟩
  rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
  norm_num

variable {K v}

theorem uniformizer_ne_zero {π : VA K v} (hπ : v.valuation K (π : K) = WithZero.exp (-1 : ℤ)) : (π : K) ≠ 0 := by
  intro h
  rw [h, map_zero] at hπ
  exact WithZero.zero_ne_coe hπ

theorem maximalIdeal_eq_span {π : VA K v} (hπ : v.valuation K (π : K) = WithZero.exp (-1 : ℤ)) :
    maximalIdeal (VA K v) = Ideal.span {π} := by
  apply le_antisymm
  · intro x hx
    rw [Valuation.mem_maximalIdeal_iff] at hx
    rw [Ideal.mem_span_singleton']
    have hx' : v.valuation K (x : K) ≤ WithZero.exp (-1 : ℤ) := by
      have := (lt_exp_iff_le_exp_sub_one (v.valuation K (x : K)) 0).1 (by rwa [WithZero.exp_zero])
      simpa using this
    refine ⟨⟨(x : K) / π, (coe_mem_iff K v _).2 ?_⟩, ?_⟩
    · rw [map_div₀, hπ, div_le_one₀ (by rw [← hπ]; exact (Valuation.pos_iff _).2 (uniformizer_ne_zero hπ))]
      exact hx'
    · apply Subtype.ext
      change (x : K) / π * π = x
      rw [div_mul_cancel₀ _ (uniformizer_ne_zero hπ)]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Valuation.mem_maximalIdeal_iff, hπ, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]
    norm_num

theorem mem_maximalIdeal_pow_iff {π : VA K v} (hπ : v.valuation K (π : K) = WithZero.exp (-1 : ℤ)) (n : ℕ) (x : VA K v) :
    x ∈ maximalIdeal (VA K v) ^ n ↔ v.valuation K (x : K) ≤ WithZero.exp (-(n : ℤ)) := by
  have hπn : v.valuation K ((π : K) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]
    simp
  have hπ0 : (π : K) ^ n ≠ 0 := pow_ne_zero _ (uniformizer_ne_zero hπ)
  rw [maximalIdeal_eq_span hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    change v.valuation K ((a : K) * (π : K) ^ n) ≤ _
    rw [map_mul, hπn]
    exact mul_le_of_le_one_left' ((coe_mem_iff K v _).1 a.2)
  · intro hx
    refine ⟨⟨(x : K) / (π : K) ^ n, (coe_mem_iff K v _).2 ?_⟩, ?_⟩
    · rw [map_div₀, hπn, div_le_one₀ (by rw [← hπn]; exact (Valuation.pos_iff _).2 hπ0)]
      exact hx
    · apply Subtype.ext
      change (x : K) / (π : K) ^ n * (π : K) ^ n = x
      rw [div_mul_cancel₀ _ hπ0]

variable (K v)

noncomputable def toVal : R →+* VA K v :=
  (algebraMap R K).codRestrict (VA K v).toSubring (fun r => (coe_mem_iff K v _).2 (v.valuation_le_one r))

@[scoped simp] theorem coe_toVal (r : R) : ((toVal K v r : VA K v) : K) = algebraMap R K r := rfl

theorem comap_maximalIdeal_pow (n : ℕ) : (maximalIdeal (VA K v) ^ n).comap (toVal K v) = v.asIdeal ^ n := by
  obtain ⟨π, hπ⟩ := exists_uniformizer K v
  ext r
  rw [Ideal.mem_comap, mem_maximalIdeal_pow_iff hπ, coe_toVal, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_le_pow_iff_mem]

theorem exists_sub_toVal_mem_pow (n : ℕ) (y : VA K v) : ∃ x : R, y - toVal K v x ∈ maximalIdeal (VA K v) ^ n := by
  classical
  obtain ⟨π, hπ⟩ := exists_uniformizer K v
  obtain ⟨a, b, hb, hy⟩ := IsFractionRing.div_surjective (A := R) (y : K)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  set k := Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) with hk
  have hsb : Ideal.span {b} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hsup : ∀ m : ℕ, v.asIdeal ^ m ⊔ Ideal.span {b} = v.asIdeal ^ min k m := fun m => irreducible_pow_sup hsb v.irreducible m
  have hbk : b ∈ v.asIdeal ^ k := by
    have e := hsup k
    rw [min_self] at e
    exact e ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self b)
  have hbk1 : b ∉ v.asIdeal ^ (k + 1) := fun h => by
    have e := hsup (k + 1)
    rw [min_eq_left (Nat.le_succ k), sup_eq_left.2 ((Ideal.span_singleton_le_iff_mem _).2 h)] at e
    exact absurd e (Ideal.pow_succ_lt_pow v.ne_bot k).ne

  have hvb : v.valuation K (algebraMap R K b) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]; exact hbk
  have hak : a ∈ v.asIdeal ^ k := by
    have hvy : v.valuation K (y : K) ≤ 1 := (coe_mem_iff K v _).1 y.2
    rw [← hy, map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 hbK)] at hvy
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
    exact hvy.trans hvb

  have ha' : a ∈ v.asIdeal ^ (k + n) ⊔ Ideal.span {b} := by
    rw [hsup (k + n), min_eq_left (Nat.le_add_right k n)]; exact hak
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 ha'
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.1 hq
  refine ⟨x, ?_⟩
  rw [mem_maximalIdeal_pow_iff hπ]
  have hval : (((y - toVal K v x : VA K v)) : K) = algebraMap R K p / algebraMap R K b := by
    rw [eq_div_iff hbK]
    change ((y : K) - algebraMap R K x) * algebraMap R K b = algebraMap R K p
    rw [← hy, sub_mul, div_mul_cancel₀ _ hbK, ← map_mul, ← map_sub, ← hpq]
    congr 1; ring
  rw [hval, map_div₀]
  have hvp : v.valuation K (algebraMap R K p) ≤ WithZero.exp (-((k + n : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]; exact hp
  have hvb' : WithZero.exp (-(k : ℤ)) ≤ v.valuation K (algebraMap R K b) := by
    have h1 : ¬ v.valuation K (algebraMap R K b) ≤ WithZero.exp (-((k + 1 : ℕ) : ℤ)) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]; exact hbk1
    rw [not_le] at h1

    by_contra h3
    rw [not_le] at h3
    have h4 := (lt_exp_iff_le_exp_sub_one (v.valuation K (algebraMap R K b)) (-(k : ℤ))).1 h3
    have : (-(k : ℤ) - 1) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this] at h4
    exact absurd (lt_of_le_of_lt h4 h1) (lt_irrefl _)
  have hbpos : 0 < v.valuation K (algebraMap R K b) := (Valuation.pos_iff _).2 hbK
  rw [div_le_iff₀ hbpos]
  calc v.valuation K (algebraMap R K p) ≤ WithZero.exp (-((k + n : ℕ) : ℤ)) := hvp
    _ = WithZero.exp (-(n : ℤ)) * WithZero.exp (-(k : ℤ)) := by rw [← WithZero.exp_add]; congr 1; push_cast; ring
    _ ≤ WithZero.exp (-(n : ℤ)) * v.valuation K (algebraMap R K b) := mul_le_mul_right hvb' _

end dvr

end ArtinL.Abelian.ValBridge
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian.ValBridge"
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian"
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL"

open NumberField IsDedekindDomain
open scoped Pointwise

namespace ArtinL
p2m_export "ArtinL" "Abelian.inertiaGroup Abelian.ramificationGroup Abelian.IsUnramifiedAt Abelian.swanConductor Abelian.conductorExponent"
namespace Abelian
p2m_export "ArtinL.Abelian" "inertiaGroup ramificationGroup IsUnramifiedAt swanConductor conductorExponent conductor"
namespace SwanInfl
p2m_open "ArtinL.Abelian ArtinL"
section valuationStab

variable (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M))

theorem WithZero.eq_of_forall_le_exp_neg_iff {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by

  obtain ⟨m, hm⟩ : ∃ m : ℕ, a = WithZero.exp (-(m : ℤ)) := by
    refine ⟨(WithZero.log a).natAbs, ?_⟩
    have hlog : WithZero.log a ≤ 0 := by
      rw [← WithZero.exp_log ha, ← WithZero.exp_zero, WithZero.exp_le_exp] at ha1; exact ha1
    rw [Int.ofNat_natAbs_of_nonpos hlog, neg_neg, WithZero.exp_log ha]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b = WithZero.exp (-(n : ℤ)) := by
    refine ⟨(WithZero.log b).natAbs, ?_⟩
    have hlog : WithZero.log b ≤ 0 := by
      rw [← WithZero.exp_log hb, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb1; exact hb1
    rw [Int.ofNat_natAbs_of_nonpos hlog, neg_neg, WithZero.exp_log hb]
  apply le_antisymm
  · rw [hn]; exact (h n).2 (hn ▸ le_rfl)
  · rw [hm]; exact (h m).1 (hm ▸ le_rfl)

variable {K M w}

theorem intValuation_smul_of_mem_stabilizer {σ : M ≃ₐ[K] M} (hσ : σ ∈ MulAction.stabilizer (M ≃ₐ[K] M) w.asIdeal)
    (r : 𝓞 M) : w.intValuation (σ • r) = w.intValuation r := by
  by_cases hr : r = 0
  · subst hr; simp
  have hσr : σ • r ≠ 0 := fun h => hr (by simpa using congrArg (fun y => σ⁻¹ • y) h)
  have hpow : ∀ n : ℕ, σ • (w.asIdeal ^ n) = w.asIdeal ^ n := fun n => by
    rw [smul_pow', MulAction.mem_stabilizer_iff.1 hσ]
  refine WithZero.eq_of_forall_le_exp_neg_iff (w.intValuation_ne_zero _ hσr) (w.intValuation_ne_zero _ hr)
    (w.intValuation_le_one _) (w.intValuation_le_one _) fun n => ?_
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem]
  constructor
  · intro h
    rwa [← hpow n, Ideal.smul_mem_pointwise_smul_iff] at h
  · intro h
    rw [← hpow n]
    exact Ideal.smul_mem_pointwise_smul_iff.2 h

theorem valuation_smul_of_mem_stabilizer {σ : M ≃ₐ[K] M} (hσ : σ ∈ MulAction.stabilizer (M ≃ₐ[K] M) w.asIdeal)
    (x : M) : w.valuation M (σ x) = w.valuation M x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) x
  have hcoe : ∀ r : 𝓞 M, σ (algebraMap (𝓞 M) M r) = algebraMap (𝓞 M) M (σ • r) := fun r => rfl
  rw [map_div₀, hcoe, hcoe, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_smul_of_mem_stabilizer hσ, intValuation_smul_of_mem_stabilizer hσ]

variable (K M w)

theorem stabilizer_le_decompositionSubgroup :
    MulAction.stabilizer (M ≃ₐ[K] M) w.asIdeal ≤ ((w.valuation M).valuationSubring).decompositionSubgroup K := by
  intro σ hσ
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
    AlgEquiv.smul_def, valuation_smul_of_mem_stabilizer (inv_mem hσ)]

theorem stabilizer_eq_decompositionSubgroup :
    MulAction.stabilizer (M ≃ₐ[K] M) w.asIdeal = ((w.valuation M).valuationSubring).decompositionSubgroup K := by
  refine le_antisymm (stabilizer_le_decompositionSubgroup K M w) fun σ hσ => ?_
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hσ

  have hA : ∀ x : M, w.valuation M (σ⁻¹ x) ≤ 1 ↔ w.valuation M x ≤ 1 := fun x => by
    rw [← Valuation.mem_valuationSubring_iff, ← Valuation.mem_valuationSubring_iff, ← AlgEquiv.smul_def,
      ← ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hσ]
  have hA' : ∀ x : M, w.valuation M (σ x) ≤ 1 ↔ w.valuation M x ≤ 1 := fun x => by
    have := hA (σ x)
    rw [show σ⁻¹ (σ x) = x from σ.symm_apply_apply x] at this
    exact this.symm
  have hlt : ∀ x : M, w.valuation M (σ x) < 1 ↔ w.valuation M x < 1 := by

    have key : ∀ y : M, w.valuation M y < 1 ↔ (w.valuation M y ≤ 1 ∧ (y = 0 ∨ ¬ w.valuation M y⁻¹ ≤ 1)) := by
      intro y
      by_cases hy : y = 0
      · simp [hy]
      · rw [map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).2 hy)]
        constructor
        · intro h; exact ⟨h.le, Or.inr (not_le.2 h)⟩
        · rintro ⟨h1, (h2 | h2)⟩
          · exact absurd h2 hy
          · exact not_le.1 h2
    intro x
    rw [key, key, hA', ← map_inv₀, hA', map_inv₀]
    simp [EmbeddingLike.map_eq_zero_iff]
  rw [MulAction.mem_stabilizer_iff]
  apply le_antisymm
  · intro r hr
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hr
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := M)] at hr ⊢
    have := (hlt (algebraMap (𝓞 M) M (σ⁻¹ • r))).2
    rw [show σ (algebraMap (𝓞 M) M (σ⁻¹ • r)) = algebraMap (𝓞 M) M r from by
      change algebraMap (𝓞 M) M (σ • (σ⁻¹ • r)) = _; rw [smul_inv_smul]] at this
    exact this hr
  · intro r hr
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := M)] at hr ⊢
    have := (hlt (algebraMap (𝓞 M) M (σ⁻¹ • r))).1
    rw [show σ (algebraMap (𝓞 M) M (σ⁻¹ • r)) = algebraMap (𝓞 M) M r from by
      change algebraMap (𝓞 M) M (σ • (σ⁻¹ • r)) = _; rw [smul_inv_smul]] at this
    exact this hr

end valuationStab
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian.ValBridge"
end ArtinL.Abelian.SwanInfl
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian.ValBridge"
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian.ValBridge"
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian.ValBridge"

namespace ArtinL
p2m_export "ArtinL" "Abelian.inertiaGroup Abelian.ramificationGroup Abelian.IsUnramifiedAt Abelian.swanConductor Abelian.conductorExponent"
namespace Abelian
p2m_export "ArtinL.Abelian" "inertiaGroup ramificationGroup IsUnramifiedAt swanConductor conductorExponent conductor"
namespace XB1
p2m_open "ArtinL.Abelian ArtinL"

open IsLocalRing ArtinL.Abelian.ValBridge

section frame
variable (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  (v : HeightOneSpectrum (𝓞 K))

noncomputable abbrev wM : HeightOneSpectrum (𝓞 M) :=
  ⟨(LanglandsTunnell.P2.Artin.primeAbove K M v), inferInstance, LanglandsTunnell.P2.Artin.primeAbove_ne_bot K M v⟩

noncomputable abbrev AV : ValuationSubring M := ((wM K M v).valuation M).valuationSubring

noncomputable abbrev DV : Subgroup (M ≃ₐ[K] M) := (AV K M v).decompositionSubgroup K

theorem stabilizer_le_DV : MulAction.stabilizer (M ≃ₐ[K] M) (LanglandsTunnell.P2.Artin.primeAbove K M v) ≤ DV K M v :=
  ArtinL.Abelian.SwanInfl.stabilizer_le_decompositionSubgroup K M (wM K M v)

theorem mem_stabilizer_of_forall_smul_mem {B : Type*} [CommRing B] {G : Type*} [Group G] [MulSemiringAction G B]
    (P : Ideal B) [hP : P.IsMaximal] (σ : G) (h : ∀ x ∈ P, σ • x ∈ P) : σ ∈ MulAction.stabilizer G P := by
  rw [MulAction.mem_stabilizer_iff]
  have hle : σ • P ≤ P := by
    rw [Ideal.pointwise_smul_def, Ideal.map_le_iff_le_comap]
    exact fun x hx => h x hx
  have hmax : (σ • P).IsMaximal := by
    rw [Ideal.pointwise_smul_def]
    exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv G B σ)
  exact hmax.eq_of_le hP.ne_top hle

theorem inertia_pow_succ_eq_map (i : ℕ) :
    ((LanglandsTunnell.P2.Artin.primeAbove K M v) ^ (i + 1)).inertia (M ≃ₐ[K] M) =
      (lowerRamificationGroup (AV K M v) ↥(DV K M v) i).map (DV K M v).subtype := by
  refine Ideal.inertia_pow_succ_eq_map_lowerRamificationGroup_of_dense (LanglandsTunnell.P2.Artin.primeAbove K M v) (DV K M v).subtype
    (fun σ hσ => ⟨⟨σ, stabilizer_le_DV K M v (mem_stabilizer_of_forall_smul_mem _ σ hσ)⟩, rfl⟩)
    (toVal M (wM K M v)) (fun σ x => Subtype.ext rfl) (comap_maximalIdeal_pow M (wM K M v)) (exists_sub_toVal_mem_pow M (wM K M v)) i

theorem card_eq (n : ℕ) : Nat.card (((LanglandsTunnell.P2.Artin.primeAbove K M v) ^ (n + 1)).inertia (M ≃ₐ[K] M)) =
    Nat.card (lowerRamificationGroup (AV K M v) ↥(DV K M v) n) := by
  rw [inertia_pow_succ_eq_map K M v n]
  exact Subgroup.card_map_of_injective Subtype.coe_injective

theorem forall_inertia_iff {A : Type*} [CommGroup A] (ψ : (M ≃ₐ[K] M) →* A) (n : ℕ) :
    (∀ σ ∈ ((LanglandsTunnell.P2.Artin.primeAbove K M v) ^ (n + 1)).inertia (M ≃ₐ[K] M), ψ σ = 1) ↔
      ∀ γ ∈ lowerRamificationGroup (AV K M v) ↥(DV K M v) n, (ψ.comp (DV K M v).subtype) γ = 1 := by
  rw [inertia_pow_succ_eq_map K M v n]
  constructor
  · intro h γ hγ
    exact h _ (Subgroup.mem_map_of_mem _ hγ)
  · intro h σ hσ
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hσ
    exact h γ hγ

open scoped Classical in

theorem swanConductor_eq (ψ : (M ≃ₐ[K] M) →* ℂˣ) :
    ArtinL.Abelian.swanConductor ψ v =
      ∑ᶠ i : ℕ, (Nat.card (lowerRamificationGroup (AV K M v) ↥(DV K M v) (i + 1)) : ℚ) /
          (Nat.card (lowerRamificationGroup (AV K M v) ↥(DV K M v) 0) : ℚ) *
        (if ∀ γ ∈ lowerRamificationGroup (AV K M v) ↥(DV K M v) (i + 1), (ψ.comp (DV K M v).subtype) γ = 1 then 0 else 1) := by
  have h1 : ArtinL.Abelian.swanConductor ψ v =
      ∑ᶠ i : ℕ, (Nat.card (((LanglandsTunnell.P2.Artin.primeAbove K M v) ^ (i + 1 + 1)).inertia (M ≃ₐ[K] M)) : ℚ) / (Nat.card ((LanglandsTunnell.P2.Artin.primeAbove K M v).inertia (M ≃ₐ[K] M)) : ℚ) *
        (if ∀ σ ∈ ((LanglandsTunnell.P2.Artin.primeAbove K M v) ^ (i + 1 + 1)).inertia (M ≃ₐ[K] M), ψ σ = 1 then 0 else 1) := by
    unfold ArtinL.Abelian.swanConductor ArtinL.Abelian.ramificationGroup ArtinL.Abelian.inertiaGroup
    rfl
  rw [h1]
  refine finsum_congr fun i => ?_
  rw [card_eq K M v (i + 1), show Nat.card ((LanglandsTunnell.P2.Artin.primeAbove K M v).inertia (M ≃ₐ[K] M)) = Nat.card (lowerRamificationGroup (AV K M v) ↥(DV K M v) 0) by
      rw [← card_eq K M v 0, zero_add, pow_one]]
  congr 1
  exact if_congr (forall_inertia_iff K M v ψ (i + 1)) rfl rfl

theorem isUnramifiedAt_iff (ψ : (M ≃ₐ[K] M) →* ℂˣ) :
    ArtinL.Abelian.IsUnramifiedAt ψ v ↔ ∀ γ ∈ lowerRamificationGroup (AV K M v) ↥(DV K M v) 0, (ψ.comp (DV K M v).subtype) γ = 1 := by
  rw [← forall_inertia_iff K M v ψ 0, zero_add, pow_one]
  rfl

theorem faithfulSMul_DV : FaithfulSMul ↥(DV K M v) (AV K M v) := by
  refine ⟨fun {σ τ} h => Subtype.ext (AlgEquiv.ext fun m => ?_)⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) m
  have h' : ∀ r : 𝓞 M, (σ : M ≃ₐ[K] M) (r : M) = (τ : M ≃ₐ[K] M) (r : M) := fun r =>
    congrArg (fun y : AV K M v => (y : M)) (h (toVal M (wM K M v) r))
  rw [map_div₀, map_div₀]
  change (σ : M ≃ₐ[K] M) (a : M) / (σ : M ≃ₐ[K] M) (b : M) = (τ : M ≃ₐ[K] M) (a : M) / (τ : M ≃ₐ[K] M) (b : M)
  rw [h' a, h' b]

theorem exists_eq_bot_of_antitone_of_iInf_eq_bot {G : Type*} [Group G] [Finite G] (f : ℕ → Subgroup G) (hf : Antitone f)
    (h : ⨅ i, f i = ⊥) : ∃ N, f N = ⊥ := by
  classical
  obtain ⟨s, hs⟩ := (Set.toFinite (Set.range f)).exists_finset_coe
  have hidx : ∀ H ∈ s, ∃ n, f n = H := fun H hH => by
    have : H ∈ Set.range f := by rw [← hs]; exact hH
    exact this
  choose! idx hidx' using hidx
  refine ⟨s.sup idx, le_bot_iff.mp ?_⟩
  rw [← h]
  refine le_iInf fun m => ?_
  have hm : f m ∈ s := by rw [← Finset.mem_coe, hs]; exact ⟨m, rfl⟩
  rw [← hidx' (f m) hm]
  exact hf (Finset.le_sup hm)

theorem exists_triv {A : Type*} [CommGroup A] (ψ : (M ≃ₐ[K] M) →* A) :
    ∃ N : ℕ, ∀ γ ∈ lowerRamificationGroup (AV K M v) ↥(DV K M v) N, (ψ.comp (DV K M v).subtype) γ = 1 := by
  haveI := faithfulSMul_DV K M v
  have hsep : ⨅ n, (maximalIdeal (AV K M v)) ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  obtain ⟨N, hN⟩ := exists_eq_bot_of_antitone_of_iInf_eq_bot (lowerRamificationGroup (AV K M v) ↥(DV K M v))
    lowerRamificationGroup_antitone (iInf_lowerRamificationGroup_eq_bot hsep)
  exact ⟨N, fun γ hγ => by rw [hN, Subgroup.mem_bot] at hγ; rw [hγ, map_one]⟩

theorem forall_mem_upperRamificationGroup_apply_eq_one_iff_swanConductor_lt'
    (ψ : (M ≃ₐ[K] M) →* ℂˣ) (hram : ¬ ArtinL.Abelian.IsUnramifiedAt ψ v) (u : ℚ) (hu : 0 ≤ u) :
    (∀ σ ∈ ValuationSubring.upperRamificationGroup K (AV K M v) u, ψ ((σ : ↥(DV K M v)) : M ≃ₐ[K] M) = 1) ↔
      ArtinL.Abelian.swanConductor ψ v < u := by
  rw [swanConductor_eq K M v ψ]
  rw [isUnramifiedAt_iff K M v ψ] at hram
  have key := IsLocalRing.forall_mem_upperRamificationGroup_iff_finsum_indicator_lt (ψ.comp (DV K M v).subtype)
    (exists_triv K M v ψ) hram u hu
  refine Iff.trans ?_ (key.trans ?_)
  · rfl
  · refine Iff.of_eq (congrArg (· < u) (finsum_congr fun i => congrArg₂ (· * ·) rfl (@if_congr ℚ _ _ (_) (_) _ _ _ _ Iff.rfl rfl rfl)))

end frame
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian.ValBridge"

end ArtinL.Abelian.XB1
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian.ValBridge"
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian.ValBridge"
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian.ValBridge"

namespace ArtinL
p2m_export "ArtinL" "Abelian.inertiaGroup Abelian.ramificationGroup Abelian.IsUnramifiedAt Abelian.swanConductor Abelian.conductorExponent"
namespace Abelian
p2m_export "ArtinL.Abelian" "inertiaGroup ramificationGroup IsUnramifiedAt swanConductor conductorExponent conductor"
namespace XB1
p2m_open "ArtinL.Abelian ArtinL"

open IsLocalRing

section xb1a
variable (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  (v : HeightOneSpectrum (𝓞 K))

theorem forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le'
    (ψ : (M ≃ₐ[K] M) →* ℂˣ) (n : ℕ) (hn : ArtinL.Abelian.conductorExponent ψ v ≤ n) :
    ∀ σ ∈ ValuationSubring.upperRamificationGroup K (AV K M v) (n : ℚ), ψ ((σ : ↥(DV K M v)) : M ≃ₐ[K] M) = 1 := by
  by_cases hram : ArtinL.Abelian.IsUnramifiedAt ψ v
  ·
    intro σ hσ
    have h0 : σ ∈ lowerRamificationGroup (AV K M v) ↥(DV K M v) 0 := IsLocalRing.upperRamificationGroup_le_zero (n : ℚ) hσ
    exact (isUnramifiedAt_iff K M v ψ).1 hram σ h0
  ·
    have hlt : ArtinL.Abelian.swanConductor ψ v < (n : ℚ) := by
      unfold ArtinL.Abelian.conductorExponent at hn
      rw [if_neg hram] at hn
      calc ArtinL.Abelian.swanConductor ψ v ≤ (⌈ArtinL.Abelian.swanConductor ψ v⌉₊ : ℚ) := Nat.le_ceil _
        _ < ((1 + ⌈ArtinL.Abelian.swanConductor ψ v⌉₊ : ℕ) : ℚ) := by push_cast; linarith
        _ ≤ n := by exact_mod_cast hn
    exact (forall_mem_upperRamificationGroup_apply_eq_one_iff_swanConductor_lt' K M v ψ hram (n : ℚ) (Nat.cast_nonneg n)).2 hlt

end xb1a
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian.ValBridge"

end ArtinL.Abelian.XB1
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian.ValBridge"
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian.ValBridge"
p2m_reactivate "P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le.ArtinL.Abelian.ValBridge"

theorem solution
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : ArtinL.Abelian.conductorExponent ψ v ≤ n) :
    ∀ σ ∈ ValuationSubring.upperRamificationGroup K (((⟨LanglandsTunnell.P2.Artin.primeAbove K M v, inferInstance, LanglandsTunnell.P2.Artin.primeAbove_ne_bot K M v⟩ :
          HeightOneSpectrum (𝓞 M)).valuation M).valuationSubring) (n : ℚ),
      ψ ((σ : ↥((((⟨LanglandsTunnell.P2.Artin.primeAbove K M v, inferInstance, LanglandsTunnell.P2.Artin.primeAbove_ne_bot K M v⟩ :
          HeightOneSpectrum (𝓞 M)).valuation M).valuationSubring).decompositionSubgroup K)) : M ≃ₐ[K] M) = 1 :=
  ArtinL.Abelian.XB1.forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le' K M v ψ n hn

end S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le
end P2MW
export P2MW.S_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le (solution)
