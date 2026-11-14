-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreAbsoluteZeroMoments
-- name    : row23_rh_supp_RHLegendreAbsoluteZeroMoments
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:02:47.324202+00:00
-- url     : https://prove2.me/theorems/0eb32e5d-a484-4230-991d-b6c80cc53dff
-- title:
--   Row 23 RH support: RHLegendreAbsoluteZeroMoments
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendrePositiveZeroTail
import Definitions.Def_dusart_psi_433_20261014_ZeroConjugation
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing
open DusartSmoothing Set
 theorem finite_absolute_moment_of_positive_bound (n : ℕ) (P : ℝ → Prop) (B : ℝ)
    (hB : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ P ρ.im) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im^n)) ≤ B)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ)
    (hP : ∀ ρ ∈ Z, P |ρ.im|) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ:ℝ)*(1/|ρ.im|^n)) ≤ 2*B := by
  classical
  let f : ℂ → ℝ := fun ρ => (RvM.zeroMult ρ:ℝ)*(1/|ρ.im|^n)
  let g : ℂ → ℝ := fun ρ => (RvM.zeroMult ρ:ℝ)*(1/ρ.im^n)
  let A := Z.filter (fun ρ => 0 < ρ.im)
  let N := Z.filter (fun ρ => ¬0 < ρ.im)
  have hNeg (ρ : ℂ) (hρ : ρ ∈ N) : ρ.im < 0 := by
    obtain ⟨hz,hn⟩ := Finset.mem_filter.mp hρ
    have hh := RvM.nontrivial_zero_abs_height ρ (hZ ρ hz)
    rw [abs_of_nonpos (le_of_not_gt hn)] at hh
    linarith [Real.pi_pos]
  have hA : (∑ ρ ∈ A, g ρ) ≤ B := by
    apply hB
    intro ρ hρ
    obtain ⟨hz,hpos⟩ := Finset.mem_filter.mp hρ
    exact ⟨hZ ρ hz,hpos,by simpa only [abs_of_pos hpos] using hP ρ hz⟩
  have hN : (∑ ρ ∈ N.image (starRingEnd ℂ), g ρ) ≤ B := by
    apply hB
    intro ρ hρ
    obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hρ
    have hτZ := (Finset.mem_filter.mp hτ).1
    have hneg := hNeg τ hτ
    have hz : RvM.IsNontrivialZero (starRingEnd ℂ τ) := by
      rcases hZ τ hτZ with ⟨hz,hr0,hr1⟩
      exact ⟨by rw [riemannZeta_conj,hz,map_zero],by simpa using hr0,by simpa using hr1⟩
    refine ⟨hz,by simpa only [Complex.conj_im] using neg_pos.mpr hneg,?_⟩
    simpa only [Complex.conj_im,abs_of_nonpos hneg.le] using hP τ hτZ
  have heA : (∑ ρ ∈ A, f ρ) = ∑ ρ ∈ A, g ρ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    dsimp only [f,g]
    rw [abs_of_pos (Finset.mem_filter.mp hρ).2]
  have heN : (∑ ρ ∈ N, f ρ) = ∑ ρ ∈ N.image (starRingEnd ℂ), g ρ := by
    rw [Finset.sum_image (fun a _ b _ he => by
      have hh := congrArg (starRingEnd ℂ) he
      simpa only [Complex.conj_conj] using hh)]
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hneg := hNeg ρ hρ
    have hn1 : ρ ≠ 1 := by
      intro he
      have hi := congrArg Complex.im he
      norm_num at hi
      linarith
    dsimp only [f,g]
    rw [RvM.zeroMult_conj ρ hn1,Complex.conj_im,abs_of_nonpos hneg.le]
  have hs : (∑ ρ ∈ Z, f ρ) = (∑ ρ ∈ A, f ρ)+(∑ ρ ∈ N, f ρ) :=
    (Finset.sum_filter_add_sum_filter_not Z (fun ρ => 0 < ρ.im) f).symm
  change (∑ ρ ∈ Z, f ρ) ≤ _
  rw [hs,heA,heN]
  exact (add_le_add hA hN).trans_eq (by ring)
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.finite_absolute_moment_of_positive_bound


