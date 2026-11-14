-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreRationalRowTransfer
-- name    : row23_rh_supp_RHLegendreRationalRowTransfer
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:15:22.983113+00:00
-- url     : https://prove2.me/theorems/42634404-3f70-4104-b0f6-5aea0eac2f05
-- title:
--   Row 23 RH support: RHLegendreRationalRowTransfer
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreRationalRowModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing.RationalRows
lemma eighth_power_rpow_inverse (q : ℝ) (hq : 0 < q) (k : ℕ) :
    (q^8)^(-((k:ℝ)/8))=(q^k)⁻¹ := by
  rw [←Real.rpow_natCast q 8,←Real.rpow_mul hq.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (8:ℝ)*(-((k:ℝ)/8))= -(k:ℝ) by ring,
    Real.rpow_neg hq.le,Real.rpow_natCast]
 theorem threshold (p : Parameters) (h : arithmeticChecks p) :
    1 ≤ (p.q:ℝ)^8 ∧ (p.q:ℝ)^8 ≤ Real.exp (p.b:ℝ)/(1+(p.δ:ℝ)) := by
  have hq : (1:ℝ) ≤ p.q := by exact_mod_cast h.1
  have hd : (0:ℝ) < p.δ := by exact_mod_cast h.2.1
  have hc : (p.q:ℝ)^8*(1+(p.δ:ℝ)) ≤ (27182818283/10^10:ℝ)^p.b := by
    have hc0 := Rat.cast_mono (K:=ℝ) h.2.2.2.1
    push_cast at hc0
    norm_num at hc0 ⊢
    exact hc0
  have hbase : (27182818283/10^10:ℝ) ≤ Real.exp 1 := by
    rw [show (27182818283/10^10:ℝ)=2.7182818283 by norm_num]
    exact Real.exp_one_gt_d9.le
  have he : (27182818283/10^10:ℝ)^p.b ≤ (Real.exp 1)^p.b :=
    pow_le_pow_left₀ (by norm_num) hbase p.b
  rw [←Real.exp_nat_mul, mul_one] at he
  exact ⟨one_le_pow₀ hq,(le_div_iff₀ (by positivity : 0 < 1+(p.δ:ℝ))).2 (hc.trans he)⟩
 theorem final_inequality (p : Parameters) (h : arithmeticChecks p) :
    (p.δ:ℝ)/2+((1+(p.δ:ℝ)/2)*(p.B₁:ℝ)+(p.M:ℝ)/(p.δ:ℝ)^p.m*(p.B₂:ℝ))*
      ((p.q:ℝ)^8)^(-1/2:ℝ)+
      ((p.M:ℝ)/(p.δ:ℝ)^p.m*(p.B₃:ℝ))*((p.q:ℝ)^8)^((7/8:ℝ)-1)+
      2*((p.q:ℝ)^8)^(-1:ℝ)+(4096/Real.pi+32*(p.m:ℝ)/(p.δ:ℝ))*
      ((p.q:ℝ)^8)^(-3/2:ℝ) ≤ (p.ε:ℝ) := by
  have hq : (1:ℝ) ≤ p.q := by exact_mod_cast h.1
  have hq0 : (0:ℝ) < p.q := lt_of_lt_of_le zero_lt_one hq
  have hb : (p.δ:ℝ)/2+((1+(p.δ:ℝ)/2)*(p.B₁:ℝ)+(p.M:ℝ)/(p.δ:ℝ)^p.m*(p.B₂:ℝ))/(p.q:ℝ)^4+
      ((p.M:ℝ)/(p.δ:ℝ)^p.m*(p.B₃:ℝ))/(p.q:ℝ)+2/(p.q:ℝ)^8+
      (4096/3+32*(p.m:ℝ)/(p.δ:ℝ))/(p.q:ℝ)^12 ≤ (p.ε:ℝ) := by
    have hb0 := Rat.cast_mono (K:=ℝ) h.2.2.2.2
    push_cast at hb0
    norm_num at hb0
    exact hb0
  have h4 := eighth_power_rpow_inverse (p.q:ℝ) hq0 4
  have h1 := eighth_power_rpow_inverse (p.q:ℝ) hq0 1
  have h8 := eighth_power_rpow_inverse (p.q:ℝ) hq0 8
  have h12 := eighth_power_rpow_inverse (p.q:ℝ) hq0 12
  norm_num at h4 h1 h8 h12
  norm_num only [show (7/8:ℝ)-1=(-1/8:ℝ) by norm_num]
  rw [h4,h1,h8,h12]
  simp only [←div_eq_mul_inv]
  have hpi : (4096:ℝ)/Real.pi ≤ 4096/3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) Real.pi_gt_three.le
  have hh := div_le_div_of_nonneg_right
    (add_le_add_right hpi (32*(p.m:ℝ)/(p.δ:ℝ))) (pow_nonneg hq0.le 12)
  have hh' : (4096/Real.pi+32*(p.m:ℝ)/(p.δ:ℝ))/(p.q:ℝ)^12 ≤
      (4096/3+32*(p.m:ℝ)/(p.δ:ℝ))/(p.q:ℝ)^12 := by
    simpa only [add_comm] using hh
  exact (add_le_add (le_refl _) hh').trans hb
end DusartLegendreSmoothing.RationalRows
#print axioms DusartLegendreSmoothing.RationalRows.threshold
#print axioms DusartLegendreSmoothing.RationalRows.final_inequality


