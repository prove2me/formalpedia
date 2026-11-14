-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreActualHighMoments
-- name    : row23_rh_supp_RHLegendreActualHighMoments
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:09:30.402025+00:00
-- url     : https://prove2.me/theorems/ad4e80bc-6b53-4cbe-afcf-40b6ea552edd
-- title:
--   Row 23 RH support: RHLegendreActualHighMoments
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreActualMomentTransfer
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing
open DusartSmoothing
noncomputable def positiveMomentPrimitive (k : ℕ) (a : ℝ) : ℝ :=
  (1+((k:ℝ)+1)*Real.log (a/(2*Real.pi)))/(((k:ℝ)+1)^2*a^(k+1))
noncomputable def positiveMomentTailBound (k : ℕ) (a : ℝ) : ℝ :=
  2*(9*Real.log (a+5)+79)/a^(k+2)+zeroCountSlope a*positiveMomentPrimitive k a
noncomputable def positiveMomentBandBound (k : ℕ) (a b : ℝ) : ℝ :=
  2*(9*Real.log (a+5)+79)/a^(k+2)+zeroCountSlope a*
    (positiveMomentPrimitive k a-positiveMomentPrimitive k b)
 theorem actual_moment_tail (k : ℕ) (a : ℝ) (ha : 1000 ≤ a) :
    Summable (heightMoment (fun ρ : NontrivialZetaZero => ρ.val)
      (fun ρ => RvM.zeroMult ρ.val) (k+2) (fun t => a < t)) ∧
    (∑' ρ : NontrivialZetaZero, heightMoment (fun τ : NontrivialZetaZero => τ.val)
      (fun τ => RvM.zeroMult τ.val) (k+2) (fun t => a < t) ρ) ≤
      2*positiveMomentTailBound k a := by
  apply actual_height_moment_of_finite_bound
  intro Z hZ
  exact finite_absolute_moment_of_positive_bound (k+2) (fun t => a < t)
    (positiveMomentTailBound k a)
    (fun W hW => finite_positive_zero_moment_tail k W
      (fun ρ hρ => ⟨(hW ρ hρ).1,(hW ρ hρ).2.1⟩) a ha
      (fun ρ hρ => (hW ρ hρ).2.2)) Z
    (fun ρ hρ => (hZ ρ hρ).1) (fun ρ hρ => (hZ ρ hρ).2)
 theorem actual_moment_band (k : ℕ) (a b : ℝ) (ha : 1000 ≤ a) (hab : a ≤ b) :
    Summable (heightMoment (fun ρ : NontrivialZetaZero => ρ.val)
      (fun ρ => RvM.zeroMult ρ.val) (k+2) (fun t => a < t ∧ t ≤ b)) ∧
    (∑' ρ : NontrivialZetaZero, heightMoment (fun τ : NontrivialZetaZero => τ.val)
      (fun τ => RvM.zeroMult τ.val) (k+2) (fun t => a < t ∧ t ≤ b) ρ) ≤
      2*positiveMomentBandBound k a b := by
  apply actual_height_moment_of_finite_bound
  intro Z hZ
  exact finite_absolute_moment_of_positive_bound (k+2) (fun t => a < t ∧ t ≤ b)
    (positiveMomentBandBound k a b)
    (fun W hW => finite_positive_zero_moment_band k W
      (fun ρ hρ => ⟨(hW ρ hρ).1,(hW ρ hρ).2.1⟩) a b ha hab
      (fun ρ hρ => (hW ρ hρ).2.2)) Z
    (fun ρ hρ => (hZ ρ hρ).1) (fun ρ hρ => (hZ ρ hρ).2)
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.actual_moment_tail
#print axioms DusartLegendreSmoothing.actual_moment_band


