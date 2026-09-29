-- Prove2me | solution 1 for ArithmeticE.division_preserves_minimal_order
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T20:55:27.590976+00:00
-- url     : https://prove2.me/submissions/7039c714-6a2a-47b9-9885-8839fb9c0890

import Definitions.Def_beukersLiftingData
set_option autoImplicit false
set_option maxHeartbeats 1600000
open ArithmeticE Polynomial PowerSeries
namespace EulerEOperator
lemma derivative_division_product (g : PowerSeries ℂ) (n : ℕ) :
    (PowerSeries.derivative ℂ)^[n+1] ((1-PowerSeries.X)*g) =
      (1-PowerSeries.X)*(PowerSeries.derivative ℂ)^[n+1] g -
        ((n+1:ℕ):PowerSeries ℂ)*(PowerSeries.derivative ℂ)^[n] g := by
  induction n with
  | zero => simp [map_sub,Derivation.leibniz]; ring
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,map_sub]
    simp only [Derivation.leibniz,map_sub,PowerSeries.derivative_one,PowerSeries.derivative_X,zero_sub,
      neg_one_mul,Derivation.map_natCast,zero_mul,zero_add]
    simp only [Function.iterate_succ_apply',smul_eq_mul]
    push_cast
    ring

lemma operator_division_identity (p : ℕ → PowerSeries ℂ) (g : PowerSeries ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), p k * (PowerSeries.derivative ℂ)^[k] ((1-PowerSeries.X)*g)) =
      (1-PowerSeries.X)*(∑ k ∈ Finset.range (n+1), p k*(PowerSeries.derivative ℂ)^[k] g) -
      ∑ k ∈ Finset.range n, ((k+1:ℕ):PowerSeries ℂ)*p (k+1)*(PowerSeries.derivative ℂ)^[k] g := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ (fun k => p k*(PowerSeries.derivative ℂ)^[k] ((1-PowerSeries.X)*g)) (n+1),
      Finset.sum_range_succ (fun k => p k*(PowerSeries.derivative ℂ)^[k] g) (n+1),
      Finset.sum_range_succ (fun k => ((k+1:ℕ):PowerSeries ℂ)*p (k+1)*(PowerSeries.derivative ℂ)^[k] g) n,
      ih,derivative_division_product]
    ring
end EulerEOperator
namespace ClassicalGauge
local notation "D" => PowerSeries.derivative ℂ
local notation "h" => (1 - Polynomial.X : Polynomial ℂ)
local notation "H" => (1 - PowerSeries.X : PowerSeries ℂ)

lemma jet (g : PowerSeries ℂ) (n : ℕ) :
    D^[n+1] (H*g) = H*D^[n+1] g - ((n+1:ℕ):PowerSeries ℂ)*D^[n] g := by
  induction n with
  | zero => simp [map_sub, Derivation.leibniz]; ring
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_sub]
    simp only [Derivation.leibniz, map_sub, PowerSeries.derivative_one, PowerSeries.derivative_X, zero_sub,
      neg_one_mul, Derivation.map_natCast, zero_mul, zero_add]
    simp only [Function.iterate_succ_apply', smul_eq_mul]
    push_cast
    ring

lemma reverse_jet (g : PowerSeries ℂ) (k : ℕ) :
    H^(k+1) * D^[k] g =
      ∑ j ∈ Finset.range (k+1), PowerSeries.C ((k.factorial:ℂ)/(j.factorial:ℂ)) *
        H^j * D^[j] (H*g) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk : (k.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hs : ((k+1).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    simp only [div_self hs, map_one, one_mul]
    have he : ∑ j ∈ Finset.range (k+1),
        PowerSeries.C (((k+1).factorial:ℂ)/(j.factorial:ℂ))*H^j*D^[j] (H*g) =
        ((k+1:ℕ):PowerSeries ℂ) * (H^(k+1)*D^[k] g) := by
      rw [ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.factorial_succ]
      push_cast
      simp only [mul_div_assoc, map_mul, map_add, map_natCast, map_one]
      ring
    rw [he, jet]
    simp only [Nat.succ_eq_add_one, pow_succ]
    ring

lemma reverse_operator (g : PowerSeries ℂ) (q : ℕ → Polynomial ℂ) (n : ℕ)
    (hq : q n ≠ 0) (hz : operatorValue q n g = 0) :
    ∃ r : ℕ → Polynomial ℂ, r n ≠ 0 ∧ operatorValue r n (H*g) = 0 := by
  let a : ℕ → ℕ → Polynomial ℂ := fun k j =>
    if j ≤ k then q k * Polynomial.C ((k.factorial:ℂ)/(j.factorial:ℂ)) * h^(n-k+j)
    else 0
  let r : ℕ → Polynomial ℂ := fun j => ∑ k ∈ Finset.range (n+1), a k j
  have hr : r n = q n * h^n := by
    dsimp [r]
    rw [Finset.sum_eq_single n]
    · simp [a, Nat.factorial_ne_zero]
    · intro k hk hkn
      have : ¬ n ≤ k := by have := Finset.mem_range.mp hk; omega
      simp [a, this]
    · simp
  refine ⟨r, ?_, ?_⟩
  · rw [hr]
    apply mul_ne_zero hq (pow_ne_zero _ ?_)
    intro hh
    have := congrArg (Polynomial.coeff · 1) hh
    norm_num [Polynomial.coeff_one] at this
  · have he : operatorValue r n (H*g) = H^(n+1) * operatorValue q n g := by
      unfold operatorValue
      simp only [r, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, Finset.sum_mul]
      simp only [Polynomial.coeToPowerSeries.ringHom_apply]
      rw [Finset.sum_comm]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      have hs : (∑ j ∈ Finset.range (n+1), (a k j : PowerSeries ℂ)*D^[j] (H*g)) =
          ∑ j ∈ Finset.range (k+1), (a k j : PowerSeries ℂ)*D^[j] (H*g) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j hj hjk
        have : ¬ j ≤ k := by simp only [Finset.mem_range] at hjk; omega
        simp [a, this]
      rw [hs]
      calc
        _ = (q k : PowerSeries ℂ)*H^(n-k) *
            (∑ j ∈ Finset.range (k+1), PowerSeries.C ((k.factorial:ℂ)/(j.factorial:ℂ))*
              H^j*D^[j] (H*g)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
          simp only [a, if_pos hjk, Polynomial.coe_mul, Polynomial.coe_C,
            Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X,
            pow_add]
          ring
        _ = H^(n+1) * ((q k : PowerSeries ℂ)*D^[k] g) := by
          rw [← reverse_jet]
          have hp : H^(n-k) * H^(k+1) = H^(n+1) := by
            rw [← pow_add]; congr 1; omega
          linear_combination (q k : PowerSeries ℂ)*D^[k] g * hp
    rw [he, hz, mul_zero]

lemma division_minimal (g : PowerSeries ℂ) (p : ℕ → Polynomial ℂ) (n : ℕ)
    (hm : MinimalEquation p n (H*g)) :
    ∃ q : ℕ → Polynomial ℂ, MinimalEquation q n g ∧ q n = h*p n := by
  let q : ℕ → Polynomial ℂ := fun k => h*p k -
    if k < n then ((k+1:ℕ):Polynomial ℂ)*p (k+1) else 0
  have hqn : q n = h*p n := by simp [q]
  refine ⟨q, ⟨?_, ?_, ?_⟩, hqn⟩
  · rw [hqn]
    apply mul_ne_zero _ hm.1
    intro hh
    have := congrArg (Polynomial.coeff · 1) hh
    norm_num [Polynomial.coeff_one] at this
  · have hh := EulerEOperator.operator_division_identity
        (fun k => (p k : PowerSeries ℂ)) g n
    change operatorValue p n (H*g) = _ at hh
    rw [hm.2.1] at hh
    unfold operatorValue
    rw [hh]
    simp only [q, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_one,
      Polynomial.coe_X, sub_mul, Finset.sum_sub_distrib]
    congr 1
    · simp [← Finset.mul_sum, mul_assoc]
    · rw [Finset.sum_range_succ]
      simp only [lt_self_iff_false, if_false, Polynomial.coe_zero, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [if_pos (Finset.mem_range.mp hk), Polynomial.coe_mul]
      congr 2
      exact map_natCast (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ) (k+1)
  · intro k hkn r hr hz
    obtain ⟨s, hs, hsz⟩ := reverse_operator g r k hr hz
    exact hm.2.2 k hkn s hs hsz
end ClassicalGauge

theorem solution (g : PowerSeries ℂ) (p : ℕ → Polynomial ℂ) (n : ℕ)
    (hm : MinimalEquation p n ((1-PowerSeries.X)*g)) :
    ∃ q : ℕ → Polynomial ℂ, MinimalEquation q n g ∧ q n = (1-Polynomial.X)*p n := by
  exact ClassicalGauge.division_minimal g p n hm
#print axioms solution
