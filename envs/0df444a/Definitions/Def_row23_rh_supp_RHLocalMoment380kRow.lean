-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalMoment380kRow
-- name    : row23_rh_supp_RHLocalMoment380kRow
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:30:48.856029+00:00
-- url     : https://prove2.me/theorems/b7616d5d-1e03-4058-95e9-0f4c2f4c5833
-- title:
--   Row 23 RH support: RHLocalMoment380kRow
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLocalMoment380kActual
import Definitions.Def_row23_rh_supp_RHLocalPsiTrivialZeroRegion
import Definitions.Def_row23_rh_supp_RHLegendreRationalRowTransfer
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing.Moment380k
open RationalRows DusartSmoothing
 lemma actual_heightMoment_nonneg (n : ℕ) (P : ℝ → Prop) (ρ : NontrivialZetaZero) :
    0 ≤ heightMoment (fun τ : NontrivialZetaZero => τ.val)
      (fun τ => RvM.zeroMult τ.val) n P ρ := by
  classical
  unfold heightMoment
  split_ifs <;> positivity
 theorem row_of_RH_and_low_sum (p : Parameters) (d : Data)
    (hp : arithmeticChecks p) (hc : checks p d) (hl : logBounds p d)
    (hM0 : (0:ℝ) ≤ p.M) (hM : derivativeMass p.m (p.δ:ℝ) ≤ (p.M:ℝ))
    (hRH : ∀ ρ : NontrivialZetaZero, |ρ.val.im| ≤ (highHeight:ℝ) → ρ.val.re=1/2)
    (hS : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ (lowHeight:ℝ)) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (d.S:ℝ))
    (hfinal : (p.δ:ℝ)/2+((1+(p.δ:ℝ)/2)*(p.B₁:ℝ)+(p.M:ℝ)/(p.δ:ℝ)^p.m*(p.B₂:ℝ))*((p.q:ℝ)^8)^(-1/2:ℝ)+
      ((p.M:ℝ)/(p.δ:ℝ)^p.m*(p.B₃:ℝ))*((p.q:ℝ)^8)^((1:ℝ)-1)+2*((p.q:ℝ)^8)^(-1:ℝ)+
      (4096/Real.pi+32*(p.m:ℝ)/(p.δ:ℝ))*((p.q:ℝ)^8)^(-3/2:ℝ) ≤ (p.ε:ℝ))
    (x : ℝ) (hx : Real.exp (p.b:ℝ) ≤ x) :
    |Chebyshev.psi x-x| ≤ (p.ε:ℝ)*x := by
  obtain ⟨hs1,hB1,hs2,hB2,hs3,hB3⟩ := actual_moment_caps p d hc hl hS
  have hδ : (0:ℝ) < p.δ := by exact_mod_cast hp.2.1
  have hδ1 : (p.δ:ℝ) ≤ 1 := by exact_mod_cast hp.2.2.1
  have hTH : (p.T:ℝ) ≤ (highHeight:ℝ) := by exact_mod_cast hc.2.2.1
  have hx0 : 0 ≤ x := (Real.exp_pos (p.b:ℝ)).le.trans hx
  have hA := threshold p hp
  have hAx : (p.q:ℝ)^8 ≤ x/(1+(p.δ:ℝ)) :=
    hA.2.trans (div_le_div_of_nonneg_right hx (by positivity))
  have hB10 : (0:ℝ) ≤ p.B₁ :=
    (tsum_nonneg (fun ρ => actual_heightMoment_nonneg 1 (fun t => t ≤ (p.T:ℝ)) ρ)).trans hB1
  have hB20 : (0:ℝ) ≤ p.B₂ :=
    (tsum_nonneg (fun ρ => actual_heightMoment_nonneg (p.m+1)
      (fun t => (p.T:ℝ) < t ∧ t ≤ (highHeight:ℝ)) ρ)).trans hB2
  have hB30 : (0:ℝ) ≤ p.B₃ :=
    (tsum_nonneg (fun ρ => actual_heightMoment_nonneg (p.m+1) (fun t => (highHeight:ℝ) < t) ρ)).trans hB3
  exact psi_bound_of_trivial_strip_and_zero_estimates p.m hc.1
    ((p.q:ℝ)^8) x (p.δ:ℝ) (p.T:ℝ) (highHeight:ℝ) (p.M:ℝ)
    (p.B₁:ℝ) (p.B₂:ℝ) (p.B₃:ℝ) (p.ε:ℝ) hA.1 hx0 hδ hδ1 hAx hTH
    hM0 hM hB10 hB20 hB30 hRH hs1 hs2 hs3 hB1 hB2 hB3 hfinal
end DusartLegendreSmoothing.Moment380k
#print axioms DusartLegendreSmoothing.Moment380k.row_of_RH_and_low_sum


