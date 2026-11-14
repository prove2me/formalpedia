-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreActualMomentTransfer
-- name    : row23_rh_supp_RHLegendreActualMomentTransfer
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:07:50.429484+00:00
-- url     : https://prove2.me/theorems/c9c8a7b6-c3b9-4337-a5a6-74613b44c9a2
-- title:
--   Row 23 RH support: RHLegendreActualMomentTransfer
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreAbsoluteZeroMoments
import Definitions.Def_row23_rh_supp_RHLegendreThreeBands
import Definitions.Def_dusart_psi_433_20261014_ZeroSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing
open DusartSmoothing
 theorem actual_height_moment_of_finite_bound (n : ℕ) (P : ℝ → Prop) (B : ℝ)
    (hB : ∀ Z : Finset ℂ,
      (∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ P |ρ.im|) →
      (∑ ρ ∈ Z, (RvM.zeroMult ρ:ℝ)*(1/|ρ.im|^n)) ≤ B) :
    Summable (heightMoment (fun ρ : NontrivialZetaZero => ρ.val)
      (fun ρ => RvM.zeroMult ρ.val) n P) ∧
    (∑' ρ : NontrivialZetaZero, heightMoment (fun τ : NontrivialZetaZero => τ.val)
      (fun τ => RvM.zeroMult τ.val) n P ρ) ≤ B := by
  classical
  let f := heightMoment (fun ρ : NontrivialZetaZero => ρ.val) (fun ρ => RvM.zeroMult ρ.val) n P
  have hf : 0 ≤ f := by
    intro ρ
    dsimp only [f,heightMoment]
    split_ifs <;> positivity
  have hFin (S : Finset NontrivialZetaZero) : (∑ ρ ∈ S, f ρ) ≤ B := by
    let W := S.filter (fun ρ => P |ρ.val.im|)
    let Z := W.image (fun ρ : NontrivialZetaZero => ρ.val)
    have hZ (ρ : ℂ) (hρ : ρ ∈ Z) : RvM.IsNontrivialZero ρ ∧ P |ρ.im| := by
      obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hρ
      exact ⟨τ.property,(Finset.mem_filter.mp hτ).2⟩
    have he : (∑ ρ ∈ S, f ρ) = ∑ ρ ∈ Z, (RvM.zeroMult ρ:ℝ)*(1/|ρ.im|^n) := by
      dsimp only [Z]
      rw [Finset.sum_image (fun a _ b _ he => Subtype.ext he)]
      dsimp only [W]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ρ hρ
      dsimp only [f,heightMoment]
      split_ifs <;> simp only [div_eq_mul_inv,one_mul]
    exact he.le.trans (hB Z hZ)
  exact ⟨summable_of_sum_le hf hFin,Real.tsum_le_of_sum_le hf hFin⟩
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.actual_height_moment_of_finite_bound


