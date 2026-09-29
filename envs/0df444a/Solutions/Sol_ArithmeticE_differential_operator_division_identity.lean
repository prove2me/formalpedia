-- Prove2me | solution 1 for ArithmeticE.differential_operator_division_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T16:03:33.611022+00:00
-- url     : https://prove2.me/submissions/2f0fd6df-42a7-4d0c-b3f8-41dac52d8f86

import Mathlib
open PowerSeries
namespace EulerEOperator
lemma derivative_division_product (g : PowerSeries ℂ) (n : ℕ) :
    (PowerSeries.derivative ℂ)^[n+1] ((1-PowerSeries.X)*g) =
      (1-PowerSeries.X)*(PowerSeries.derivative ℂ)^[n+1] g -
        ((n+1:ℕ):PowerSeries ℂ)*(PowerSeries.derivative ℂ)^[n] g := by
  induction n with
  | zero => simp [map_sub,Derivation.leibniz]; ring
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,map_sub]
    simp only [Derivation.leibniz,map_sub,derivative_one,derivative_X,zero_sub,
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


theorem solution (p : ℕ → PowerSeries ℂ) (g : PowerSeries ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), p k * (PowerSeries.derivative ℂ)^[k] ((1-PowerSeries.X)*g)) =
      (1-PowerSeries.X)*(∑ k ∈ Finset.range (n+1), p k*(PowerSeries.derivative ℂ)^[k] g) -
      ∑ k ∈ Finset.range n, ((k+1:ℕ):PowerSeries ℂ)*p (k+1)*(PowerSeries.derivative ℂ)^[k] g := by
  exact EulerEOperator.operator_division_identity p g n

#print axioms solution
