-- Prove2me | solution 1 for AlmostSSDPortfolio.AASSD.step_12c
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:53:35.833846+00:00
-- url     : https://prove2.me/submissions/4d51694b-2e0c-4b89-acb3-f10710f3cae7

import Mathlib
import Definitions.Def_AlmostSSDPortfolio_AASSD_Model
open MeasureTheory Set

namespace Aux_SSDW31
open AlmostSSDPortfolio.AASSD

lemma cont_max (c : ℝ) : Continuous (fun x : ℝ => max (x - c) 0) := by fun_prop

lemma key (c a b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    ∫ x in a..b, max (x - c) 0 = (b - c) ^ 2 / 2 := by
  have hint : ∀ u w : ℝ, IntervalIntegrable (fun x => max (x - c) 0) volume u w :=
    fun u w => (cont_max c).intervalIntegrable u w
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint a c) (hint c b)]
  have h1 : ∫ x in a..c, max (x - c) 0 = ∫ x in a..c, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hac] at hx
    exact max_eq_right (by linarith [hx.2])
  have h2 : ∫ x in c..b, max (x - c) 0 = ∫ x in c..b, (x - c) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hcb] at hx
    exact max_eq_left (by linarith [hx.1])
  rw [h1, h2, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
    intervalIntegrable_const, integral_id, intervalIntegral.integral_const,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

lemma lpm_cont {m : ℕ} (p v : Fin m → ℝ) : Continuous (lpm p v) := by
  unfold lpm; fun_prop

lemma lemma1 {m : ℕ} (p v : Fin m → ℝ) (a b : ℝ) (hp : IsProbVec p)
    (hv : ∀ t, v t ∈ Icc a b) :
    var p v + (b - mean p v) ^ 2 = 2 * ∫ x in a..b, lpm p v x := by
  have hsum : ∑ t, p t = 1 := hp.2
  unfold lpm
  rw [intervalIntegral.integral_finsetSum (f := fun t x => p t * max (x - v t) 0) (fun t _ =>
    ((continuous_const.mul (cont_max (v t))) : Continuous fun x => p t * max (x - v t) 0).intervalIntegrable _ _)]
  have h : ∀ t, ∫ x in a..b, p t * max (x - v t) 0 = p t * ((b - v t) ^ 2 / 2) := fun t => by
    rw [intervalIntegral.integral_const_mul, key (v t) a b (hv t).1 (hv t).2]
  simp only [h]
  unfold var mean
  have e1 : ∀ M : ℝ, ∑ t, p t * (v t - M) ^ 2 =
      ∑ t, p t * v t ^ 2 - 2 * M * ∑ t, p t * v t + M ^ 2 * ∑ t, p t := by
    intro M
    have : ∀ t, p t * (v t - M) ^ 2 = p t * v t ^ 2 - 2 * M * (p t * v t) + M ^ 2 * p t :=
      fun t => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have e2 : 2 * ∑ t, p t * ((b - v t) ^ 2 / 2) =
      b ^ 2 * ∑ t, p t - 2 * b * ∑ t, p t * v t + ∑ t, p t * v t ^ 2 := by
    rw [Finset.mul_sum]
    have : ∀ t, 2 * (p t * ((b - v t) ^ 2 / 2)) = b ^ 2 * p t - 2 * b * (p t * v t) + p t * v t ^ 2 :=
      fun t => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [e1, e2, hsum]
  ring

end Aux_SSDW31

open AlmostSSDPortfolio.AASSD in
theorem solution {n T Tb : ℕ} (S : Setting n T Tb) (hS : S.Standing)
    (lam : Fin n → ℝ) (hlam : lam ∈ simplex n) :
    var S.q S.bv + (S.b - mean S.q S.bv) ^ 2 - var S.p (S.ret lam) -
        (S.b - mean S.p (S.ret lam)) ^ 2
      = 2 * ∫ t in S.a..S.b, (S.G2 t - S.F2 lam t) := by
  obtain ⟨hab, hp, hq, hx, hbv⟩ := hS
  have hl0 : ∀ i, 0 ≤ lam i := hlam.1
  have hl1 : ∑ i, lam i = 1 := hlam.2
  have hret : ∀ t, S.ret lam t ∈ Icc S.a S.b := by
    intro t
    unfold Setting.ret
    constructor
    · calc S.a = ∑ i, S.a * lam i := by rw [← Finset.mul_sum, hl1, mul_one]
        _ ≤ ∑ i, S.x i t * lam i :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx i t).1 (hl0 i)
    · calc ∑ i, S.x i t * lam i ≤ ∑ i, S.b * lam i :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx i t).2 (hl0 i)
        _ = S.b := by rw [← Finset.mul_sum, hl1, mul_one]
  unfold Setting.G2 Setting.F2
  rw [intervalIntegral.integral_sub ((Aux_SSDW31.lpm_cont _ _).intervalIntegrable _ _)
    ((Aux_SSDW31.lpm_cont _ _).intervalIntegrable _ _), mul_sub,
    ← Aux_SSDW31.lemma1 S.q S.bv S.a S.b hq hbv, ← Aux_SSDW31.lemma1 S.p (S.ret lam) S.a S.b hp hret]
  ring
