-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalMoment380kActual
-- name    : row23_rh_supp_RHLocalMoment380kActual
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:19:46.845368+00:00
-- url     : https://prove2.me/theorems/16f0b179-24a9-425b-a21e-5c6ca9da0665
-- title:
--   Row 23 RH support: RHLocalMoment380kActual
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLocalMoment380kReal
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing.Moment380k
open RationalRows DusartSmoothing
 theorem actual_moment_caps (p : Parameters) (d : Data) (hc : checks p d) (hl : logBounds p d)
    (hS : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ (lowHeight:ℝ)) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (d.S:ℝ)) :
    Summable (heightMoment (fun ρ : NontrivialZetaZero => ρ.val)
      (fun ρ => RvM.zeroMult ρ.val) 1 (fun t => t ≤ (p.T:ℝ))) ∧
    (∑' ρ : NontrivialZetaZero, heightMoment (fun τ : NontrivialZetaZero => τ.val)
      (fun τ => RvM.zeroMult τ.val) 1 (fun t => t ≤ (p.T:ℝ)) ρ) ≤ (p.B₁:ℝ) ∧
    Summable (heightMoment (fun ρ : NontrivialZetaZero => ρ.val)
      (fun ρ => RvM.zeroMult ρ.val) (p.m+1) (fun t => (p.T:ℝ) < t ∧ t ≤ (highHeight:ℝ))) ∧
    (∑' ρ : NontrivialZetaZero, heightMoment (fun τ : NontrivialZetaZero => τ.val)
      (fun τ => RvM.zeroMult τ.val) (p.m+1) (fun t => (p.T:ℝ) < t ∧ t ≤ (highHeight:ℝ)) ρ) ≤ (p.B₂:ℝ) ∧
    Summable (heightMoment (fun ρ : NontrivialZetaZero => ρ.val)
      (fun ρ => RvM.zeroMult ρ.val) (p.m+1) (fun t => (highHeight:ℝ) < t)) ∧
    (∑' ρ : NontrivialZetaZero, heightMoment (fun τ : NontrivialZetaZero => τ.val)
      (fun τ => RvM.zeroMult τ.val) (p.m+1) (fun t => (highHeight:ℝ) < t) ρ) ≤ (p.B₃:ℝ) := by
  have hcaps := real_moment_caps p d hc hl
  rcases hc with ⟨hm,hTa,hTH,hL0,hLU0,hLT,hLUT,hLH,hLUH,hc1,hc2,hc3⟩
  have hTaR : (lowHeight:ℝ) ≤ (p.T:ℝ) := by exact_mod_cast hTa
  have hTHR : (p.T:ℝ) ≤ (highHeight:ℝ) := by exact_mod_cast hTH
  have hlow : (1000:ℝ) ≤ lowHeight := by norm_num [lowHeight]
  have hhigh : (1000:ℝ) ≤ highHeight := by norm_num [highHeight]
  have hn2 : p.m-1+2=p.m+1 := by omega
  have h1 := actual_low_moment (lowHeight:ℝ) (p.T:ℝ) (d.S:ℝ) hlow hTaR hS
  have h2 := actual_moment_band (p.m-1) (p.T:ℝ) (highHeight:ℝ) (hlow.trans hTaR) hTHR
  have h3 := actual_moment_tail (p.m-1) (highHeight:ℝ) hhigh
  norm_num only [hn2] at h2 h3
  exact ⟨h1.1,h1.2.trans hcaps.1,h2.1,h2.2.trans hcaps.2.1,h3.1,h3.2.trans hcaps.2.2⟩
end DusartLegendreSmoothing.Moment380k
#print axioms DusartLegendreSmoothing.Moment380k.actual_moment_caps


