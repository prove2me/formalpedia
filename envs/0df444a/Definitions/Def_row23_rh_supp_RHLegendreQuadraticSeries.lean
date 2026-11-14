-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreQuadraticSeries
-- name    : row23_rh_supp_RHLegendreQuadraticSeries
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:11:21.433534+00:00
-- url     : https://prove2.me/theorems/8eb821b2-7f5b-441f-9077-10a54fc775db
-- title:
--   Row 23 RH support: RHLegendreQuadraticSeries
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreSeriesIntegrable
import Definitions.Def_row23_rh_supp_RHLegendreSecondDerivative
import Definitions.Def_dusart_psi_433_20261014_ZeroSeries
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Polynomial MeasureTheory intervalIntegral
open DusartSmoothing
lemma nontrivial_zero_set_countable : {ρ : ℂ | RvM.IsNontrivialZero ρ}.Countable := by
  have hc : (⋃ n : ℕ, {ρ : ℂ | RvM.IsNontrivialZero ρ ∧ |ρ.im| ≤ (n:ℝ)}).Countable :=
    Set.countable_iUnion (fun n => (RvM.finite_symmetric_zero_window n).countable)
  apply hc.mono
  intro ρ hρ
  obtain ⟨n,hn⟩ := exists_nat_ge |ρ.im|
  exact Set.mem_iUnion.mpr ⟨n,⟨hρ,hn⟩⟩
instance countable_nontrivial_zeros : Countable NontrivialZetaZero :=
  nontrivial_zero_set_countable.to_subtype
lemma finite_quadratic_subtype_norm_bound (S : Finset NontrivialZetaZero) (y : ℝ) (hy : 1 ≤ y) :
    (∑ ρ ∈ S, ‖(RvM.zeroMult ρ.val:ℂ)*quadraticKernel y ρ.val‖) ≤ 24*y^3 := by
  classical
  let Z := S.image (fun ρ : NontrivialZetaZero => ρ.val)
  have hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ := by
    intro ρ hρ
    obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hρ
    exact τ.property
  have h := finite_quadratic_zero_norm_sum_bound y hy Z hZ
  dsimp only [Z] at h
  rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at h
  exact h
 theorem weighted_quadratic_zero_series_integrable_and_interchange (m : ℕ) (x δ : ℝ)
    (hx : 1 ≤ x) (hd : 0 < δ) :
    IntervalIntegrable (fun t : ℝ => ((iteratedDeriv 2 (weight m) t:ℝ):ℂ)*
      (∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val:ℂ)*quadraticKernel (x*(1+δ*t)) ρ.val)) volume 0 1 ∧
    (∫ t : ℝ in 0..1, ((iteratedDeriv 2 (weight m) t:ℝ):ℂ)*
      (∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val:ℂ)*quadraticKernel (x*(1+δ*t)) ρ.val)) =
    ∑' ρ : NontrivialZetaZero, ∫ t : ℝ in 0..1,
      ((iteratedDeriv 2 (weight m) t:ℝ):ℂ)*((RvM.zeroMult ρ.val:ℂ)*quadraticKernel (x*(1+δ*t)) ρ.val) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let U := Set.uIcc (0:ℝ) 1
  let B := x*(1+δ)
  let F := fun (ρ : NontrivialZetaZero) (t : ℝ) =>
    ((iteratedDeriv 2 (weight m) t:ℝ):ℂ)*((RvM.zeroMult ρ.val:ℂ)*quadraticKernel (x*(1+δ*t)) ρ.val)
  let g := fun t : ℝ => |iteratedDeriv 2 (weight m) t| *(24*B^3)
  have hw : Continuous (iteratedDeriv 2 (weight m)) := by
    have he : iteratedDeriv 2 (weight m) = fun t : ℝ => (Polynomial.derivative^[2] (densityPolynomial m)).eval t :=
      funext (iteratedDeriv_weight m 2)
    rw [he]
    exact (Polynomial.derivative^[2] (densityPolynomial m)).continuous
  have hbase (t : ℝ) (ht : t ∈ U) : 1 ≤ x*(1+δ*t) := by
    dsimp only [U] at ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    nlinarith [mul_nonneg hd.le ht.1,mul_nonneg hx0.le (mul_nonneg hd.le ht.1)]
  have hF (ρ : NontrivialZetaZero) : IntervalIntegrable (F ρ) volume 0 1 := by
    have hb : ContinuousOn (fun t : ℝ => ((x*(1+δ*t):ℝ):ℂ)) U := by fun_prop
    have hs : ∀ t ∈ U, ((x*(1+δ*t):ℝ):ℂ) ∈ Complex.slitPlane := by
      intro t ht
      exact Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le zero_lt_one (hbase t ht))
    have hq : ContinuousOn (fun t : ℝ => quadraticKernel (x*(1+δ*t)) ρ.val) U := by
      unfold quadraticKernel
      exact (hb.cpow_const (b:=ρ.val+2) hs).div_const _
    exact ((Complex.continuous_ofReal.comp hw).continuousOn.mul (continuousOn_const.mul hq)).intervalIntegrable
  have hg : IntervalIntegrable g volume 0 1 := by
    exact (hw.abs.mul continuous_const).intervalIntegrable 0 1
  have hbound (S : Finset NontrivialZetaZero) (t : ℝ) (ht : t ∈ Set.Ioc (0:ℝ) 1) :
      (∑ ρ ∈ S, ‖F ρ t‖) ≤ g t := by
    have ht' : t ∈ U := by
      change t ∈ Set.uIcc (0:ℝ) 1
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ⟨ht.1.le,ht.2⟩
    have hy := hbase t ht'
    have hyB : x*(1+δ*t) ≤ B := by
      dsimp only [B]
      nlinarith [mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hx0.le hd.le)]
    have hpow : (x*(1+δ*t))^3 ≤ B^3 := pow_le_pow_left₀ (by linarith) hyB 3
    have hz := (finite_quadratic_subtype_norm_bound S _ hy).trans (mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ) ≤ 24))
    have hn (ρ : NontrivialZetaZero) : ‖F ρ t‖ =
        |iteratedDeriv 2 (weight m) t| *‖(RvM.zeroMult ρ.val:ℂ)*quadraticKernel (x*(1+δ*t)) ρ.val‖ := by
      dsimp only [F]
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    dsimp only [g]
    simp_rw [hn]
    rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  constructor
  · simpa only [F,tsum_mul_left] using interval_tsum_integrable_of_finite_norm_bound F g hF hg hbound
  · simpa only [F,tsum_mul_left] using interval_tsum_of_finite_norm_bound F g hF hg hbound
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.weighted_quadratic_zero_series_integrable_and_interchange


