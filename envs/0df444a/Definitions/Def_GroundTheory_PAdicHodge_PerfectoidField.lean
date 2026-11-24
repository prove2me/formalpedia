-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
-- name    : GroundTheory_PAdicHodge_PerfectoidField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:48.005795+00:00
-- url     : https://prove2.me/theorems/c34b71a3-b785-449f-b4a9-274c0b52af0f
-- title:
--   Perfectoid Field
-- statement:
--   Definitions and structural lemmas for Perfectoid Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
open NNReal
section Integers
variable (K : Type*) [NormedField K] [IsUltrametricDist K]
abbrev normInteger : Subring K := (NormedField.valuation (K := K)).integer
variable {K}
theorem mem_normInteger {x : K} : x ∈ normInteger K ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
  simp
theorem normInteger_integers : (NormedField.valuation (K := K)).Integers (normInteger K) :=
  Valuation.integer.integers _
theorem mem_span_singleton_pow_iff {a x : normInteger K} (n : ℕ) :
    x ∈ Ideal.span {a} ^ n ↔ ‖(x : K)‖ ≤ ‖(a : K)‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
    calc ‖(y : K)‖ * ‖(a : K)‖ ^ n ≤ 1 * ‖(a : K)‖ ^ n := by
          gcongr; exact mem_normInteger.1 y.2
      _ = _ := one_mul _
  · intro hx
    by_cases ha : (a : K) ^ n = 0
    · refine ⟨0, ?_⟩
      have : ‖(x : K)‖ = 0 := le_antisymm (by simpa [← norm_pow, ha] using hx) (norm_nonneg _)
      ext; simp [norm_eq_zero.1 this]
    · refine ⟨⟨(x : K) / (a : K) ^ n, mem_normInteger.2 ?_⟩, ?_⟩
      · rw [norm_div, norm_pow]
        exact div_le_one_of_le₀ hx (by positivity)
      · ext; simp [div_mul_cancel₀ _ ha]
theorem isAdicComplete_span_singleton [CompleteSpace K] {a : normInteger K}
    (ha : ‖(a : K)‖ < 1) : IsAdicComplete (Ideal.span {a}) (normInteger K) := by
  have hmem : ∀ (n : ℕ) (x y : normInteger K),
      x ≡ y [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule (normInteger K) (normInteger K))] ↔
        ‖(x : K) - y‖ ≤ ‖(a : K)‖ ^ n := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_singleton_pow_iff]
    simp
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    simp only [hmem, ZeroMemClass.coe_zero, sub_zero] at hx
    have ht : Filter.Tendsto (fun n : ℕ => ‖(a : K)‖ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ha
    have : ‖(x : K)‖ ≤ 0 := ge_of_tendsto' ht hx
    ext; simpa using this
  · intro f hf
    simp only [hmem] at hf
    have ht : Filter.Tendsto (fun n : ℕ => ‖(a : K)‖ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ha
    have hc : CauchySeq (fun n => (f n : K)) := by
      refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
      obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
      refine ⟨N, fun n hn => ?_⟩
      rw [dist_eq_norm, norm_sub_rev]
      exact (hf hn).trans_lt (hN N le_rfl)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L‖ ≤ 1 :=
      le_of_tendsto' hL.norm fun n => mem_normInteger.1 (f n).2
    refine ⟨⟨L, mem_normInteger.2 hL1⟩, fun n => (hmem n _ _).2 ?_⟩
    have h2 : Filter.Tendsto (fun m => (f n : K) - f m) Filter.atTop (nhds ((f n : K) - L)) :=
      tendsto_const_nhds.sub hL
    exact le_of_tendsto h2.norm (Filter.eventually_atTop.2 ⟨n, fun m hm => hf hm⟩)
theorem surjective_pow_modP_of_exists_pow_eq {p : ℕ} (hp : p ≠ 0)
    (h : ∀ x : K, ‖x‖ ≤ 1 → ∃ y : K, y ^ p = x) :
    Function.Surjective (fun x : ModP (normInteger K) p => x ^ p) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨y, hy⟩ := h x (mem_normInteger.1 x.2)
  have hy1 : ‖y‖ ≤ 1 := by
    have : ‖y‖ ^ p ≤ 1 := by rw [← norm_pow, hy]; exact mem_normInteger.1 x.2
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp).1 this
  refine ⟨Ideal.Quotient.mk _ ⟨y, mem_normInteger.2 hy1⟩, ?_⟩
  simp only [← map_pow]
  congr 1
  ext; simp [hy]
end Integers
class IsPerfectoidField (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    (p : ℕ) [Fact p.Prime] : Prop where

  complete : CompleteSpace K

  norm_natCast_lt_one : ‖(p : K)‖ < 1

  exists_norm_mem_Ioo : ∀ r : ℝ, r < 1 → ∃ x : K, r < ‖x‖ ∧ ‖x‖ < 1

  surjective_pow : Function.Surjective (fun x : ModP (normInteger K) p => x ^ p)
namespace IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
theorem completeSpace (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] : CompleteSpace K :=
  IsPerfectoidField.complete p
theorem norm_natCast_integer_lt_one : ‖((p : normInteger K) : K)‖ < 1 := by
  simpa using IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
instance fact_not_isUnit : Fact (¬ IsUnit (p : normInteger K)) := by
  refine ⟨fun hu => ?_⟩
  obtain ⟨u, hu⟩ := hu
  have h1 : ‖((u : normInteger K) : K)‖ * ‖(((u⁻¹ : (normInteger K)ˣ) : normInteger K) : K)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, Units.mul_inv]; simp
  have ha : ‖((u : normInteger K) : K)‖ < 1 := hu ▸ norm_natCast_integer_lt_one p
  have hb := mem_normInteger.1 ((u⁻¹ : (normInteger K)ˣ) : normInteger K).2
  nlinarith [norm_nonneg ((u : normInteger K) : K)]
instance fact_valuation_ne_one : Fact (NormedField.valuation (p : K) ≠ 1) := by
  refine ⟨fun h => ?_⟩
  have h' : ‖(p : K)‖ = 1 := by
    rw [NormedField.valuation_apply] at h
    exact congrArg NNReal.toReal h
  exact (IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)).ne h'
instance isAdicComplete : IsAdicComplete (Ideal.span {(p : normInteger K)}) (normInteger K) :=
  haveI := completeSpace (K := K) p
  isAdicComplete_span_singleton (norm_natCast_integer_lt_one p)
example : Field (Tilt K NormedField.valuation (normInteger K) normInteger_integers p) :=
  inferInstance
example : PreTilt (normInteger K) p →* normInteger K := PreTilt.untilt
end IsPerfectoidField
namespace IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
omit [IsUltrametricDist K] in

theorem exists_norm_mem_Ioo_of_exists_pow_eq
    (h : ∀ (x : K) (n : ℕ), 0 < n → ∃ y : K, y ^ n = x) :
    ∀ r : ℝ, r < 1 → ∃ x : K, r < ‖x‖ ∧ ‖x‖ < 1 := by
  intro r hr
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  set r' := max r 0 with hr'
  have hr'0 : 0 ≤ r' := le_max_right _ _
  have hr'1 : r' < 1 := max_lt hr zero_lt_one
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hc0 hr'1
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hN
    exact absurd (hN.trans hc1) (lt_irrefl _)
  obtain ⟨y, hy⟩ := h c N (Nat.pos_of_ne_zero hN0)
  have hyN : ‖y‖ ^ N = ‖c‖ := by rw [← norm_pow, hy]
  refine ⟨y, lt_of_le_of_lt (le_max_left r 0) ?_, ?_⟩
  · rw [← pow_lt_pow_iff_left₀ hr'0 (norm_nonneg y) hN0, hyN]
    exact hN
  · rw [← pow_lt_one_iff_of_nonneg (norm_nonneg y) hN0, hyN]
    exact hc1
theorem of_isAlgClosed (p : ℕ) [Fact p.Prime] [CompleteSpace K] [IsAlgClosed K]
    (hp : ‖(p : K)‖ < 1) : IsPerfectoidField K p where
  complete := inferInstance
  norm_natCast_lt_one := hp
  exists_norm_mem_Ioo :=
    exists_norm_mem_Ioo_of_exists_pow_eq fun x _ hn => IsAlgClosed.exists_pow_nat_eq x hn
  surjective_pow := surjective_pow_modP_of_exists_pow_eq (Fact.out : p.Prime).ne_zero
    fun x _ => IsAlgClosed.exists_pow_nat_eq x (Fact.out : p.Prime).pos
instance padicComplex (p : ℕ) [Fact p.Prime] : IsPerfectoidField ℂ_[p] p :=
  of_isAlgClosed p (by
    have h := PadicComplex.norm_extends' p (p : ℚ_[p])
    have hc : (((p : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) = (p : ℂ_[p]) := by
      rw [map_natCast, PadicComplex.coe_natCast]
    rw [← hc, h]
    exact Padic.norm_p_lt_one)
end IsPerfectoidField
end GroundTheory.PAdicHodge
end


