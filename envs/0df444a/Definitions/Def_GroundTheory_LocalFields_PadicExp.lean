-- Prove2me | Definitions.Def_GroundTheory_LocalFields_PadicExp
-- name    : GroundTheory_LocalFields_PadicExp
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:54.451006+00:00
-- url     : https://prove2.me/theorems/0b99b57f-0245-4f19-bd2a-c6a4e51a1d6e
-- title:
--   Padic Exp
-- statement:
--   Definitions and structural lemmas for Padic Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicExp.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Theorems.Thm_GroundTheory_LocalField_continuous_padicLog
import Theorems.Thm_GroundTheory_LocalField_div_natCast_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_eq_zero_of_logSeries_eq_zero
import Theorems.Thm_GroundTheory_LocalField_expSeries_add
import Theorems.Thm_GroundTheory_LocalField_expSeries_sub_one_mem
import Theorems.Thm_GroundTheory_LocalField_expTerm_mem
import Theorems.Thm_GroundTheory_LocalField_isOpen_valBall
import Theorems.Thm_GroundTheory_LocalField_logSeries_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_mul_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_le_one_iff
import Theorems.Thm_GroundTheory_LocalField_one_le_absRamificationIndex
import Theorems.Thm_GroundTheory_LocalField_one_le_of_lt_sub_one_mul
import Theorems.Thm_GroundTheory_LocalField_pow_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_sub_one_le_of_lt
import Theorems.Thm_GroundTheory_LocalField_summable_expSeries
import Theorems.Thm_GroundTheory_LocalField_tendsto_zero_iff_valBall
import Theorems.Thm_GroundTheory_LocalField_tsum_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_unitFiltrationUnits_antitone
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
namespace GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
section ExpLog
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
omit [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K] in
theorem expSeries_zero : expSeries (0 : K) = 1 := by
  rw [expSeries, tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]
theorem expSeries_nsmul {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) (m : ℕ) :
    expSeries (m • x) = expSeries x ^ m := by
  induction m with
  | zero => simp [expSeries_zero]
  | succ m ih =>
    rw [succ_nsmul, expSeries_add p (nsmul_mem hx m) hx ha, ih, pow_succ]
theorem expSeries_mul_sub_one_sub_mem {a d : ℤ} {x c : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) (hc : c ∈ valBall K d) (hd : 0 ≤ d) :
    expSeries (c * x) - 1 - c * x ∈ valBall K (2 * d + a + 1) := by
  have hcx : c * x ∈ valBall K a := by
    simpa using valBall_antitone (by omega : a ≤ d + a) (mul_mem_valBall hc hx)
  have hs := summable_expSeries p hcx ha
  rw [expSeries, hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
    Nat.factorial_one]
  have : ∀ t : K, 1 + (c * x + t) - 1 - c * x = t := fun t ↦ by ring
  rw [this]
  refine tsum_mem_valBall fun k ↦ ?_
  have h1 : (c * x) ^ (k + 1 + 1) / ((k + 1 + 1).factorial : K) =
      c ^ (k + 1 + 1) * (x ^ (k + 1 + 1) / ((k + 1 + 1).factorial : K)) := by
    rw [mul_pow, mul_div_assoc]
  rw [h1]
  have hxk := expTerm_mem p hx (k + 1 + 1)
  have hck := pow_mem_valBall hc (k + 1 + 1)
  refine valBall_antitone ?_ (mul_mem_valBall hck hxk)
  have h0 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : k + 1 + 1 ≠ 0)
  set v := padicValNat p (k + 1 + 1).factorial
  set e := absRamificationIndex K
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp.out.one_le]; simp
  have h0' : (((p - 1) * v : ℕ) : ℤ) < k + 1 + 1 := by exact_mod_cast h0
  push_cast [hp1] at h0'
  have he : (0 : ℤ) ≤ e := by positivity
  have h0'' : ((p : ℤ) - 1) * v ≤ k + 1 := by linarith
  have ha' : (e : ℤ) + 1 ≤ ((p : ℤ) - 1) * a := by linarith
  have hk : (0 : ℤ) ≤ k + 1 := by positivity
  have hkd : (0 : ℤ) ≤ k * d := by positivity
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h0'' he, mul_le_mul_of_nonneg_left ha' hk]
theorem logSeries_expSeries_sub_one {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    logSeries (expSeries x - 1) = x := by
  have ha1 := one_le_of_lt_sub_one_mul p ha
  have hy : expSeries x - 1 ∈ valBall K 1 :=
    valBall_antitone ha1 (expSeries_sub_one_mem p hx ha)
  have h1 := tendsto_logSeries p hy
  simp only [add_sub_cancel] at h1
  refine tendsto_nhds_unique h1 ?_
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_valBall]
  intro N
  rw [eventually_atTop]
  set e := absRamificationIndex K
  have he := one_le_absRamificationIndex (K := K) p
  refine ⟨N.toNat, fun k hk ↦ ?_⟩
  have hm0 : p ^ k ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hm : ((p ^ k : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have heq : (expSeries x ^ (p ^ k) - 1) / ((p ^ k : ℕ) : K) - x =
      (expSeries (((p ^ k : ℕ) : K) * x) - 1 - ((p ^ k : ℕ) : K) * x) / ((p ^ k : ℕ) : K) := by
    rw [← expSeries_nsmul p hx ha, nsmul_eq_mul]
    field_simp
  rw [heq]
  have hmem := expSeries_mul_sub_one_sub_mem p hx ha (natCast_prime_pow_mem_valBall p k)
    (by positivity)
  have hdiv := div_natCast_mem_valBall p hmem hm0
  refine valBall_antitone ?_ hdiv
  rw [padicValNat.prime_pow]
  have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  have h3 : (N.toNat : ℤ) ≤ k := by exact_mod_cast hk
  have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
  nlinarith
end ExpLog
section Iso
theorem mem_maximalIdeal_pow_iff_valBall {n : ℕ} {y : 𝒪[K]} :
    y ∈ 𝓂[K] ^ n ↔ (y : K) ∈ valBall K n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hset := hϖ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (v := valuation K) n
  have : y ∈ 𝓂[K] ^ n ↔ y ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := Iff.rfl
  rw [this, hset, mem_valBall]
  show valuation K (y : K) ≤ valuation K (ϖ : K) ^ n ↔ _
  rw [← map_pow, ← normalizedValuation_le_iff, map_pow, normalizedValuation_uniformizer hϖ,
    ← WithZero.exp_nsmul]
  simp
theorem mem_integer_of_mem_valBall {n : ℤ} (hn : 0 ≤ n) {x : K} (hx : x ∈ valBall K n) :
    x ∈ 𝒪[K] := by
  rw [← normalizedValuation_le_one_iff]
  exact hx.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
variable (K) in

noncomputable def valBallEquivMaximalIdealPow (n : ℕ) :
    valBall K n ≃ₜ+ (𝓂[K] ^ n : Ideal 𝒪[K]) where
  toFun x := ⟨⟨x, mem_integer_of_mem_valBall (by positivity) x.2⟩,
    mem_maximalIdeal_pow_iff_valBall.mpr x.2⟩
  invFun y := ⟨((y : 𝒪[K]) : K), mem_maximalIdeal_pow_iff_valBall.mp y.2⟩
  left_inv x := rfl
  right_inv y := rfl
  map_add' x y := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
theorem one_le_of_lt_sub_one_mul_nat {n : ℕ}
    (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) : 1 ≤ n := by
  have := one_le_of_lt_sub_one_mul p hn
  omega
omit [CharZero K] in
theorem sub_one_mem_valBall_of_mem {n : ℕ} (hn1 : 1 ≤ n) (u : unitFiltrationUnits K n) :
    ((u : Kˣ) : K) - 1 ∈ valBall K n :=
  (mem_unitFiltrationUnits_iff_valBall hn1).mp u.2
noncomputable def logValBallHom (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Additive (unitFiltrationUnits K n) →+ valBall K n where
  toFun u := ⟨logSeries ((((Additive.toMul u : unitFiltrationUnits K n) : Kˣ) : K) - 1),
    logSeries_mem_valBall p
      (sub_one_mem_valBall_of_mem (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul u)) hn⟩
  map_zero' := Subtype.ext (by simp [logSeries])
  map_add' u w := by
    have h := (padicLog K).map_add
      (Additive.ofMul ⟨((Additive.toMul u : unitFiltrationUnits K n) : Kˣ),
        unitFiltrationUnits_antitone (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul u).2⟩)
      (Additive.ofMul ⟨((Additive.toMul w : unitFiltrationUnits K n) : Kˣ),
        unitFiltrationUnits_antitone (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul w).2⟩)
    exact Subtype.ext h
theorem coe_logValBallHom (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n)
    (u : Additive (unitFiltrationUnits K n)) :
    (logValBallHom p n hn u : K) =
      logSeries ((((Additive.toMul u : unitFiltrationUnits K n) : Kˣ) : K) - 1) := rfl
theorem logValBallHom_injective (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Function.Injective (logValBallHom p n hn) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have h := congrArg Subtype.val hu
  rw [coe_logValBallHom] at h
  have hx := eq_zero_of_logSeries_eq_zero p hn
    (sub_one_mem_valBall_of_mem (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul u)) h
  apply Additive.toMul.injective
  ext
  simpa [sub_eq_zero] using hx
omit [CharZero K] in
theorem expSeries_ne_zero {n : ℕ} (hn1 : 1 ≤ n) {x : K} (hx : expSeries x - 1 ∈ valBall K n) :
    expSeries x ≠ 0 := by
  intro h
  rw [h, zero_sub, mem_valBall, Valuation.map_neg, map_one, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at hx
  omega
noncomputable def expUnit (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n)
    (x : valBall K n) : unitFiltrationUnits K n :=
  ⟨Units.mk0 (expSeries (x : K))
    (expSeries_ne_zero (one_le_of_lt_sub_one_mul_nat p hn) (expSeries_sub_one_mem p x.2 hn)),
    (mem_unitFiltrationUnits_iff_valBall (one_le_of_lt_sub_one_mul_nat p hn)).mpr
      (expSeries_sub_one_mem p x.2 hn)⟩
theorem logValBallHom_expUnit (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n)
    (x : valBall K n) : logValBallHom p n hn (Additive.ofMul (expUnit p n hn x)) = x :=
  Subtype.ext (logSeries_expSeries_sub_one p x.2 hn)
theorem continuous_expSeries_valBall (n : ℕ)
    (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Continuous fun x : valBall K n ↦ expSeries (x : K) := by
  rw [continuous_iff_continuousAt]
  intro x0
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_valBall]
  intro N
  set r : ℤ := max N n
  have hr : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * r :=
    sub_one_le_of_lt p hn (le_max_right _ _)
  have hopen := (isOpen_valBall r).preimage
    (continuous_subtype_val.sub continuous_const : Continuous fun x : valBall K n ↦ (x : K) - x0)
  filter_upwards [hopen.mem_nhds (by simp)] with x hx
  have hx' : (x : K) - x0 ∈ valBall K r := hx
  have hxn : (x : K) - x0 ∈ valBall K n := valBall_antitone (le_max_right _ _) hx'
  have heq : expSeries (x : K) = expSeries (x0 : K) * expSeries ((x : K) - x0) := by
    rw [← expSeries_add p x0.2 hxn hn, add_sub_cancel]
  have h0 : expSeries (x0 : K) ∈ valBall K 0 := by
    have h1 := valBall_antitone (by positivity : (0 : ℤ) ≤ n) (expSeries_sub_one_mem p x0.2 hn)
    have h2 : (1 : K) ∈ valBall K 0 := by simp [mem_valBall]
    simpa using add_mem h1 h2
  rw [heq, show expSeries (x0 : K) * expSeries ((x : K) - x0) - expSeries (x0 : K) =
    expSeries (x0 : K) * (expSeries ((x : K) - x0) - 1) by ring]
  have hNr : N ≤ 0 + r := by rw [zero_add]; exact le_max_left _ _
  refine valBall_antitone hNr (mul_mem_valBall h0 ?_)
  exact expSeries_sub_one_mem p hx' hr
noncomputable def logValBallEquiv (n : ℕ) (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Additive (unitFiltrationUnits K n) ≃ₜ+ valBall K n where
  toFun := logValBallHom p n hn
  invFun x := Additive.ofMul (expUnit p n hn x)
  left_inv u := logValBallHom_injective p n hn (logValBallHom_expUnit p n hn _)
  right_inv x := logValBallHom_expUnit p n hn x
  map_add' := map_add _
  continuous_toFun := by
    have hι : Continuous fun u : Additive (unitFiltrationUnits K n) ↦
        (Additive.ofMul (⟨((Additive.toMul u : unitFiltrationUnits K n) : Kˣ),
          unitFiltrationUnits_antitone (one_le_of_lt_sub_one_mul_nat p hn)
            (Additive.toMul u).2⟩ : unitFiltrationUnits K 1)) :=
      continuous_ofMul.comp ((continuous_subtype_val.comp continuous_toMul).subtype_mk _)
    exact (continuous_padicLog.comp hι).subtype_mk _
  continuous_invFun := by
    refine continuous_ofMul.comp (Continuous.subtype_mk ?_ _)
    rw [Units.isEmbedding_val₀.continuous_iff]
    exact continuous_expSeries_valBall p n hn
noncomputable def unitFiltrationLogEquiv (n : ℕ)
    (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    Additive (unitFiltrationUnits K n) ≃ₜ+ (𝓂[K] ^ n : Ideal 𝒪[K]) :=
  (logValBallEquiv p n hn).trans (valBallEquivMaximalIdealPow K n)
end Iso
end GroundTheory.LocalField


