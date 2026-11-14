-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalPsiTrivialZeroRegion
-- name    : row23_rh_supp_RHLocalPsiTrivialZeroRegion
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:27:07.317083+00:00
-- url     : https://prove2.me/theorems/2e7ee6a9-6acf-48c5-8bf6-0d6d6e588a20
-- title:
--   Row 23 RH support: RHLocalPsiTrivialZeroRegion
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendrePsiExplicitFormula
import Definitions.Def_row23_rh_supp_RHLegendrePerronTotalSharp
import Definitions.Def_row23_rh_supp_RHLegendrePowerErrorAssembly
import Definitions.Def_row23_rh_supp_RHLegendreThreeBands
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open DusartSmoothing
 theorem psi_bound_of_trivial_strip_and_zero_estimates (m : ℕ) (hm : 2 ≤ m)
    (A x δ T H M B₁ B₂ B₃ ε : ℝ)
    (hA : 1 ≤ A) (hx : 0 ≤ x) (hd : 0 < δ) (hd1 : δ ≤ 1) (hAx : A ≤ x/(1+δ)) (hTH : T ≤ H)
    (hM0 : 0 ≤ M) (hM : derivativeMass m δ ≤ M)
    (hB₁0 : 0 ≤ B₁) (hB₂0 : 0 ≤ B₂) (hB₃0 : 0 ≤ B₃)
    (hRH : ∀ ρ : NontrivialZetaZero, |ρ.val.im| ≤ H → ρ.val.re=1/2)
    (hs₁ : Summable (heightMoment (fun ρ : NontrivialZetaZero => ρ.val) (fun ρ => RvM.zeroMult ρ.val) 1 (fun t => t ≤ T)))
    (hs₂ : Summable (heightMoment (fun ρ : NontrivialZetaZero => ρ.val) (fun ρ => RvM.zeroMult ρ.val) (m+1) (fun t => T < t ∧ t ≤ H)))
    (hs₃ : Summable (heightMoment (fun ρ : NontrivialZetaZero => ρ.val) (fun ρ => RvM.zeroMult ρ.val) (m+1) (fun t => H < t)))
    (hB₁ : (∑' ρ : NontrivialZetaZero, heightMoment (fun τ : NontrivialZetaZero => τ.val) (fun τ => RvM.zeroMult τ.val) 1 (fun t => t ≤ T) ρ) ≤ B₁)
    (hB₂ : (∑' ρ : NontrivialZetaZero, heightMoment (fun τ : NontrivialZetaZero => τ.val) (fun τ => RvM.zeroMult τ.val) (m+1) (fun t => T < t ∧ t ≤ H) ρ) ≤ B₂)
    (hB₃ : (∑' ρ : NontrivialZetaZero, heightMoment (fun τ : NontrivialZetaZero => τ.val) (fun τ => RvM.zeroMult τ.val) (m+1) (fun t => H < t) ρ) ≤ B₃)
    (hfinal : δ/2+((1+δ/2)*B₁+M/δ^m*B₂)*A^(-1/2:ℝ)+
      (M/δ^m*B₃)*A^((1:ℝ)-1)+2*A^(-1:ℝ)+
      (4096/Real.pi+32*(m:ℝ)/δ)*A^(-3/2:ℝ) ≤ ε) :
    |Chebyshev.psi x-x| ≤ ε*x := by
  let σ : ℝ := 1
  let C₁ := (1+δ/2)*B₁+M/δ^m*B₂
  let C₂ := M/δ^m*B₃
  let Q := 4096/Real.pi+32*(m:ℝ)/δ
  let Z := fun y : ℝ => ∑' ρ : NontrivialZetaZero,
    (RvM.zeroMult ρ.val:ℂ)*((y:ℂ)^ρ.val*zeroKernel m ρ.val δ)
  let R := fun y : ℝ => -logDeriv riemannZeta 0+legendrePerronRemainder m y δ
  have hi (ρ : NontrivialZetaZero) : 0 < |ρ.val.im| := by
    have hh := RvM.nontrivial_zero_abs_height ρ.val ρ.property
    linarith [Real.pi_pos]
  have hZ (y : ℝ) (hy : A ≤ y) : ‖Z y‖ ≤ C₁*y^(1/2:ℝ)+C₂*y^σ := by
    have h := zero_series_three_band_bound m (fun ρ : NontrivialZetaZero => ρ.val)
      (fun ρ => RvM.zeroMult ρ.val) y δ T H σ M B₁ B₂ B₃ (hA.trans hy) hd hTH
      (by norm_num [σ]) hM0 hM hi hRH
      (fun ρ => ρ.property.2.2.le) hs₁ hs₂ hs₃ hB₁ hB₂ hB₃
    exact h.2.trans_eq (by dsimp [C₁,C₂]; ring)
  have hformula (y : ℝ) (hy : A ≤ y) :
      ((average m Chebyshev.psi y δ-y*(1+δ/2):ℝ):ℂ) = -Z y+R y :=
    psi_average_explicit_formula m hm y δ (hA.trans hy) hd
  have hR (y : ℝ) (hy : A ≤ y) : ‖R y‖ ≤ 2+Q*y^(-1/2:ℝ) :=
    norm_total_legendre_remainder_sharp m hm y δ (lt_of_lt_of_le zero_lt_one (hA.trans hy)) hd hd1
  have h := desmoothing_power_remainder m Chebyshev.psi Chebyshev.psi_mono A x δ σ (-1/2)
    C₁ C₂ 2 Q Z R (lt_of_lt_of_le zero_lt_one hA) hx hd.le (by norm_num [σ]) (by norm_num)
    hAx (by dsimp [C₁]; positivity) (by dsimp [C₂]; positivity) (by norm_num)
    (by dsimp [Q]; positivity) hformula hZ hR
  norm_num only [show (1/2:ℝ)-1=(-1/2:ℝ) by norm_num,
    show (-1/2:ℝ)-1=(-3/2:ℝ) by norm_num] at h
  dsimp only [C₁,C₂,Q,σ] at h
  norm_num only at h hfinal
  exact h.trans (mul_le_mul_of_nonneg_right hfinal hx)
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.psi_bound_of_trivial_strip_and_zero_estimates


