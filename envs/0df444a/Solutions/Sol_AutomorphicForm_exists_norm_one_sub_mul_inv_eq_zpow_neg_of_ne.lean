-- Prove2me | solution 1 for AutomorphicForm.exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6930783d-850a-50e2-aa5f-8c79340f813e

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain

noncomputable section

namespace P2mWInert

namespace G8

open AutomorphicForm

section Norms

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev qv : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

theorem one_lt_qv : 1 < qv K v := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  unfold qv
  exact_mod_cast this

theorem qv_pos : 0 < qv K v := lt_trans zero_lt_one (one_lt_qv K v)

theorem qv_ne_zero : qv K v ≠ 0 := (qv_pos K v).ne'

theorem mem_integers_iff_norm (y : v.adicCompletion K) :
    y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem exists_norm_eq_zpow_and_v_eq {x : v.adicCompletion K} (hx : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = qv K v ^ k ∧ (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hv0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv0), ?_, ?_⟩
  · rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv0]
    push_cast
    rfl
  · conv_lhs => rw [← WithZero.coe_unzero hv0]
    rfl

theorem norm_eq_zero_or_zpow (x : v.adicCompletion K) : ‖x‖ = 0 ∨ ∃ n : ℤ, ‖x‖ = qv K v ^ n := by
  by_cases hx : x = 0
  · exact Or.inl (by rw [hx, norm_zero])
  · obtain ⟨k, hk, -⟩ := exists_norm_eq_zpow_and_v_eq K v hx
    exact Or.inr ⟨k, hk⟩

theorem v_eq_exp_of_norm_eq_zpow {x : v.adicCompletion K} {k : ℤ} (h : ‖x‖ = qv K v ^ k) :
    (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at h
    exact (zpow_pos (qv_pos K v) k).ne h
  obtain ⟨k', hk', hv⟩ := exists_norm_eq_zpow_and_v_eq K v hx
  rw [hk'] at h
  have hk : k' = k := zpow_right_injective₀ (qv_pos K v) (one_lt_qv K v).ne' h
  rw [hv, hk]

theorem norm_eq_zpow_of_v_eq_exp {x : v.adicCompletion K} {k : ℤ}
    (h : (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k) : ‖x‖ = qv K v ^ k := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, map_zero] at h
    exact WithZero.coe_ne_zero h.symm
  obtain ⟨k', hk', hv⟩ := exists_norm_eq_zpow_and_v_eq K v hx
  rw [hv] at h
  have : k' = k := WithZero.exp_injective h
  rw [hk', this]

theorem norm_eq_one_iff_v (x : v.adicCompletion K) :
    ‖x‖ = 1 ↔ (Valued.v x : WithZero (Multiplicative ℤ)) = 1 := by
  constructor
  · intro h
    have := v_eq_exp_of_norm_eq_zpow K v (k := 0) (by rw [h, zpow_zero])
    rwa [WithZero.exp_zero] at this
  · intro h
    have := norm_eq_zpow_of_v_eq_exp K v (k := 0) (by rw [h, WithZero.exp_zero])
    rwa [zpow_zero] at this

theorem zpow_add_one_le_norm_of_lt {x : v.adicCompletion K} {n : ℤ} (h : qv K v ^ n < ‖x‖) :
    qv K v ^ (n + 1) ≤ ‖x‖ := by
  rcases norm_eq_zero_or_zpow K v x with h0 | ⟨k, hk⟩
  · rw [h0] at h; exact absurd h (not_lt.2 (zpow_nonneg (qv_pos K v).le _))
  · rw [hk] at h ⊢
    have hlt : n < k := (zpow_lt_zpow_iff_right₀ (one_lt_qv K v)).1 h
    exact zpow_le_zpow_right₀ (one_lt_qv K v).le (by omega)

theorem exists_norm_eq_inv : ∃ ϖ : v.adicCompletion K, ‖ϖ‖ = (qv K v)⁻¹ := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1))
  exact ⟨x, by rw [norm_eq_zpow_of_v_eq_exp K v hx, zpow_neg, zpow_one]⟩

end Norms

section Unramified

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w)

scoped instance isScalarTower_int : IsScalarTower (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem liesOver : w.1.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩

variable (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
include hw

theorem v_algebraMap (x : Kv) :
    (Valued.v (algebraMap Kv Lw x) : WithZero (Multiplicative ℤ)) = Valued.v x := by
  change Valued.v (w.adicCompletionSemialgHom K L x) = _
  rw [HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w x, hw, pow_one]

theorem norm_algebraMap_eq_one_iff (x : Kv) : ‖algebraMap Kv Lw x‖ = 1 ↔ ‖x‖ = 1 := by
  rw [norm_eq_one_iff_v, norm_eq_one_iff_v, v_algebraMap K L v w hw]

theorem norm_algebraMap_uniformizer {ϖ : Kv} (hϖ : ‖ϖ‖ = (qv K v)⁻¹) :
    ‖algebraMap Kv Lw ϖ‖ = (qv L w.1)⁻¹ := by
  have h1 := v_eq_exp_of_norm_eq_zpow K v (k := -1) (by rw [hϖ, zpow_neg, zpow_one])
  rw [← v_algebraMap K L v w hw] at h1
  rw [norm_eq_zpow_of_v_eq_exp L w.1 h1, zpow_neg, zpow_one]

theorem exists_eq_algebraMap_mul_unit {y : Lw} (hy : y ≠ 0) :
    ∃ x : Kv, x ≠ 0 ∧ (Valued.v (y * (algebraMap Kv Lw x)⁻¹) : WithZero (Multiplicative ℤ)) = 1 := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v
    (Valued.v y : WithZero (Multiplicative ℤ))
  have hy0 : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact hy0 hx.symm
  refine ⟨x, hx0, ?_⟩
  rw [map_mul, map_inv₀, v_algebraMap K L v w hw, hx, mul_inv_cancel₀ hy0]

theorem qv_w_eq_pow : qv L w.1 = qv K v ^ Module.finrank Kv Lw := by
  have hef := HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L w
  have hw' : v.asIdeal.ramificationIdx' w.1.asIdeal = 1 := by
    have h2 : HeightOneSpectrum.under (𝓞 K) w.1 = v := w.2
    have h3 := hw
    rw [h2] at h3
    exact h3
  rw [hw', one_mul] at hef
  haveI := liesOver K L v w
  unfold qv
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.1.asIdeal v.asIdeal v.isPrime v.ne_bot, hef]
  push_cast
  rfl

omit hw in

theorem isIntegral_of_mem {y : Lw} (hy : y ∈ w.1.adicCompletionIntegers L) :
    IsIntegral (v.adicCompletionIntegers K) y := by
  haveI : Algebra.IsIntegral (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
    Algebra.IsIntegral.of_finite _ _
  have h : IsIntegral (v.adicCompletionIntegers K) (⟨y, hy⟩ : w.1.adicCompletionIntegers L) :=
    Algebra.IsIntegral.isIntegral _
  exact h.map (IsScalarTower.toAlgHom (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L))

omit hw in

theorem mem_of_isIntegral {y : Lw} (hy : IsIntegral (v.adicCompletionIntegers K) y) :
    y ∈ w.1.adicCompletionIntegers L := by
  have h2 : IsIntegral (w.1.adicCompletionIntegers L) y := hy.tower_top
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.1.adicCompletionIntegers L)
    (K := w.1.adicCompletion L)).1 h2
  rw [← hz]
  exact z.2

variable (θ : (w.1.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.1.adicCompletion L))

omit hw in

theorem theta_mem {y : Lw} (hy : y ∈ w.1.adicCompletionIntegers L) : θ y ∈ w.1.adicCompletionIntegers L := by
  apply mem_of_isIntegral K L v w
  exact (isIntegral_of_mem K L v w hy).map (θ.restrictScalars (v.adicCompletionIntegers K)).toAlgHom

omit hw in

theorem v_theta_eq_one {y : Lw} (hy : (Valued.v y : WithZero (Multiplicative ℤ)) = 1) :
    (Valued.v (θ y) : WithZero (Multiplicative ℤ)) = 1 := by
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact zero_ne_one hy
  have h1 : θ y ∈ w.1.adicCompletionIntegers L :=
    theta_mem K L v w θ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hy.le)
  have h2 : θ y⁻¹ ∈ w.1.adicCompletionIntegers L :=
    theta_mem K L v w θ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hy, inv_one]))
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  rw [map_inv₀, map_inv₀] at h2
  have h3 : (Valued.v (θ y) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ θ.injective).2 hy0)
  exact le_antisymm h1 (by rwa [inv_le_one₀ (zero_lt_iff.2 h3)] at h2)

theorem v_theta (y : Lw) : (Valued.v (θ y) : WithZero (Multiplicative ℤ)) = Valued.v y := by
  by_cases hy : y = 0
  · rw [hy, map_zero]
  obtain ⟨x, hx0, hu⟩ := exists_eq_algebraMap_mul_unit K L v w hw hy
  have ha0 : algebraMap Kv Lw x ≠ 0 := (map_ne_zero _).2 hx0
  have hy' : y = (y * (algebraMap Kv Lw x)⁻¹) * algebraMap Kv Lw x := by
    rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  conv_lhs => rw [hy', map_mul, AlgEquiv.commutes, map_mul, v_theta_eq_one K L v w θ hu]
  conv_rhs => rw [hy', map_mul, hu]

theorem norm_theta (y : Lw) : ‖θ y‖ = ‖y‖ := by
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, v_theta K L v w hw θ]

theorem norm_theta_pow (i : ℕ) (y : Lw) : ‖(θ ^ i) y‖ = ‖y‖ := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', AlgEquiv.mul_apply, norm_theta K L v w hw, ih]

theorem norm_eq_one_iff_of_normString {ℓ : ℕ} (hℓ : 0 < ℓ) (α : Lw) (a : Kv)
    (h : ∏ i ∈ Finset.range ℓ, (θ ^ i) α = algebraMap Kv Lw a) : ‖α‖ = 1 ↔ ‖a‖ = 1 := by
  have key : ‖algebraMap Kv Lw a‖ = ‖α‖ ^ ℓ := by
    rw [← h, norm_prod, Finset.prod_congr rfl fun i _ => norm_theta_pow K L v w hw θ i α, Finset.prod_const,
      Finset.card_range]
  rw [← norm_algebraMap_eq_one_iff K L v w hw, key]
  constructor
  · intro h1; rw [h1, one_pow]
  · intro h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hℓ.ne').1 h1

end Unramified

section Extraction

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w)

omit L w in

theorem norm_units_eq_zpow (x : Kvˣ) : ∃ r : ℤ, ‖(x : Kv)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-r) := by
  obtain ⟨k, hk, -⟩ := exists_norm_eq_zpow_and_v_eq K v x.ne_zero
  exact ⟨-k, by rw [neg_neg]; exact hk⟩

variable (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)

include hw in

theorem norm_algebraMap_eq_pow (x : Kv) :
    ‖algebraMap Kv Lw x‖ = ‖x‖ ^ Module.finrank Kv Lw := by
  by_cases hx : x = 0
  · rw [hx, map_zero, norm_zero, norm_zero, zero_pow Module.finrank_pos.ne']
  obtain ⟨k, hk, hv⟩ := exists_norm_eq_zpow_and_v_eq K v hx
  rw [← v_algebraMap K L v w hw] at hv
  rw [norm_eq_zpow_of_v_eq_exp L w.1 hv, qv_w_eq_pow K L v w hw, hk, ← zpow_natCast, ← zpow_natCast,
    ← zpow_mul, ← zpow_mul, mul_comm]

include hw in

theorem norm_eq_zpow_of_prod_pow_apply_eq
    (θ : Lw ≃ₐ[Kv] Lw) (α : Lwˣ) (a : Kvˣ)
    (hN : ∏ i ∈ Finset.range (Module.finrank Kv Lw), (θ ^ i) (α : Lw) = algebraMap Kv Lw a)
    (ra : ℤ) (hα : ‖(α : Lw)‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-ra)) :
    ‖(a : Kv)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-((Module.finrank Kv Lw : ℤ) * ra)) := by
  have hℓ : 0 < Module.finrank Kv Lw := Module.finrank_pos
  have key : ‖algebraMap Kv Lw a‖ = ‖(α : Lw)‖ ^ Module.finrank Kv Lw := by
    rw [← hN, norm_prod, Finset.prod_congr rfl fun i _ => norm_theta_pow K L v w hw θ i α, Finset.prod_const,
      Finset.card_range]
  rw [norm_algebraMap_eq_pow K L v w hw] at key
  have hα' : ‖(a : Kv)‖ = ‖(α : Lw)‖ := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hℓ.ne').1 key
  rw [hα', hα]
  show qv L w.1 ^ (-ra) = qv K v ^ (-((Module.finrank Kv Lw : ℤ) * ra))
  rw [qv_w_eq_pow K L v w hw, ← zpow_natCast, ← zpow_mul, mul_neg]

omit L w in

theorem norm_div_eq_one_and_exists_of_norm_eq (a b : Kvˣ) (hab : a ≠ b) (h : ‖(a : Kv)‖ = ‖(b : Kv)‖) :
    ‖((b * a⁻¹ : Kvˣ) : Kv)‖ = 1 ∧
      ∃ d : ℕ, ‖1 - ((b * a⁻¹ : Kvˣ) : Kv)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(d : ℤ)) := by
  have ha0 : ‖(a : Kv)‖ ≠ 0 := norm_ne_zero_iff.2 a.ne_zero
  have hn : ‖((b * a⁻¹ : Kvˣ) : Kv)‖ = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, ← h, mul_inv_cancel₀ ha0]
  refine ⟨hn, ?_⟩
  have hne : (1 : Kv) - ((b * a⁻¹ : Kvˣ) : Kv) ≠ 0 := by
    intro h0
    apply hab
    have h1 : ((b * a⁻¹ : Kvˣ) : Kv) = 1 := (sub_eq_zero.1 h0).symm
    have h2 : b * a⁻¹ = 1 := Units.ext h1
    rw [mul_inv_eq_one] at h2
    exact h2.symm
  obtain ⟨k, hk, -⟩ := exists_norm_eq_zpow_and_v_eq K v hne
  have hle : ‖(1 : Kv) - ((b * a⁻¹ : Kvˣ) : Kv)‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by rw [norm_one]) ?_)
    rw [norm_neg]; exact hn.le
  have hk0 : k ≤ 0 := by
    by_contra hk0
    have h1 : (1 : ℝ) < qv K v ^ k := one_lt_zpow₀ (one_lt_qv K v) (by omega)
    rw [hk] at hle
    exact absurd (lt_of_lt_of_le h1 hle) (lt_irrefl _)
  refine ⟨(-k).toNat, ?_⟩
  rw [hk, Int.toNat_of_nonneg (by omega), neg_neg]

theorem prod_pow_apply_div_eq (θ : Lw ≃ₐ[Kv] Lw) (α β : Lwˣ) (a b : Kvˣ) (ℓ : ℕ)
    (hNα : ∏ i ∈ Finset.range ℓ, (θ ^ i) (α : Lw) = algebraMap Kv Lw a)
    (hNβ : ∏ i ∈ Finset.range ℓ, (θ ^ i) (β : Lw) = algebraMap Kv Lw b) :
    ∏ i ∈ Finset.range ℓ, (θ ^ i) ((β * α⁻¹ : Lwˣ) : Lw) = algebraMap Kv Lw ((b * a⁻¹ : Kvˣ) : Kv) := by
  have key : ∀ i ∈ Finset.range ℓ,
      (θ ^ i) ((β * α⁻¹ : Lwˣ) : Lw) = (θ ^ i) (β : Lw) * ((θ ^ i) (α : Lw))⁻¹ := by
    intro i _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  rw [Finset.prod_congr rfl key, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hNα, hNβ, Units.val_mul,
    Units.val_inv_eq_inv_val, map_mul, map_inv₀]

end Extraction

end G8
p2m_reactivate "P2MW.S_AutomorphicForm_exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne.P2mWInert.G8"

end P2mWInert
p2m_reactivate "P2MW.S_AutomorphicForm_exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne.P2mWInert.G8 P2MW.S_AutomorphicForm_exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne.P2mWInert"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne.P2mWInert.G8 P2MW.S_AutomorphicForm_exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne.P2mWInert"

open P2mWInert.G8 in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b) :
    ∃ d : ℕ, ‖(a : v.adicCompletion K)‖ = ‖(b : v.adicCompletion K)‖ →
      ‖1 - ((b * a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(d : ℤ)) := by
  by_cases h : ‖(a : v.adicCompletion K)‖ = ‖(b : v.adicCompletion K)‖
  · obtain ⟨-, d, hd⟩ := P2mWInert.G8.norm_div_eq_one_and_exists_of_norm_eq K v a b hab h
    exact ⟨d, fun _ => hd⟩
  · exact ⟨0, fun h' => absurd h' h⟩

end S_AutomorphicForm_exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne
end P2MW
export P2MW.S_AutomorphicForm_exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne (solution)
