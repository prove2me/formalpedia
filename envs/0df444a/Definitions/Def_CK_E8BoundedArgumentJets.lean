-- Prove2me | Definitions.Def_CK_E8BoundedArgumentJets
-- name    : CK_E8BoundedArgumentJets
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T12:05:00.825356+00:00
-- url     : https://prove2.me/theorems/53b3236a-1058-4f92-a85e-7f4a1ad67482
-- title:
--   Courtade–Kumar proof module `E8BoundedArgumentJets` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8BoundedArgumentJets` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8BoundedArgumentJets` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8BoundedArgumentJets (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8BoundedArgumentJets.lean)

import Definitions.Def_CK_E8GlobalRatioCertificate
import Definitions.Def_CK_GeneralCK_PureGapE8TailSixteenDerivatives

-- ===== source module E8BoundedArgumentJets =====
section

namespace GeneralCK.E8LargeTSAxis

open Set Certificates
open E8CompactAnchorRegularJetDerivatives E8TAxisDeltaDirectionalJet
open E8TAxisStableInterval E8TAxisReparamInterval DyadicInterval

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem endpoint_mem : (63/20 : ℝ) ∈ e8SlopeRange := by
  obtain ⟨a, _, ha, hy⟩ := E8LargeSShift.covers
  rw [← hy]
  exact E8TAxisStableJet5.Y_mem_e8SlopeRange ha

theorem endpoint_jets : e8RegularQ (63/20) ≤ 1 ∧
    deriv e8RegularQ (63/20) ≤ 1 ∧ deriv (deriv e8RegularQ) (63/20) ≤ 1 := by
  obtain ⟨a, ha, hapos, hay⟩ := E8LargeSShift.covers
  have hc := checked_stable_contains_canonical E8LargeSShift.whole_primitive_checks.1
    E8LargeSShift.whole_primitive_checks.2 E8LargeSShift.logTwo_checked
    E8LargeSShift.whole_denominators E8LargeSShift.whole_y_derivative_positive ha hapos
  rw [hay] at hc
  have h0 : (eval (xBox E8LargeSShift.wholeInput) (yBox E8LargeSShift.wholeInput)).d0.hi ≤
      scale E8LargeSShift.precision := by decide +kernel
  have h1 : (eval (xBox E8LargeSShift.wholeInput) (yBox E8LargeSShift.wholeInput)).d1.hi ≤
      scale E8LargeSShift.precision := by decide +kernel
  have h2 : (eval (xBox E8LargeSShift.wholeInput) (yBox E8LargeSShift.wholeInput)).d2.hi ≤
      scale E8LargeSShift.precision := by decide +kernel
  have upper {b : DyadicInterval E8LargeSShift.precision} {x : ℝ}
      (hx : b.Contains x) (hb : b.hi ≤ scale E8LargeSShift.precision) : x ≤ 1 := by
    have hh : (b.hi : ℝ) ≤ (scale E8LargeSShift.precision : ℝ) := by exact_mod_cast hb
    have hm := hx.2.trans hh
    nlinarith [scale_cast_pos E8LargeSShift.precision]
  have hv : qJet.d0 (63/20) ≤ 1 := upper hc.1 h0
  have hd : qJet.d1 (63/20) ≤ 1 := upper hc.2.1 h1
  have hdd : qJet.d2 (63/20) ≤ 1 := upper hc.2.2.1 h2
  rw [qJet_d0, ← e8RegularQ_eq_e8Q (by norm_num : (0 : ℝ) ≤ 63/20)] at hv
  rw [qJet_d1_eq_deriv_regular endpoint_mem] at hd
  rw [qJet_d2_eq_deriv2_regular endpoint_mem] at hdd
  exact ⟨hv, hd, hdd⟩

theorem third_nonnegative {y : ℝ} (hy : y ∈ e8SlopeRange) :
    0 ≤ deriv (deriv (deriv e8RegularQ)) y := by
  have hn := e8LogDerivativeJetNumeratorNonnegative_of_stable
    E8RatioMonotonicity.e8StableJetNumeratorNonnegative y hy
  have hp : 0 < qJet.d1 y := by
    rw [qJet_d1_eq_deriv_regular hy]
    exact deriv_e8RegularQ_pos (Or.inr hy)
  have hprod : 0 ≤ qJet.d1 y * qJet.d3 y := by
    dsimp [e8LogDerivativeJetNumerator] at hn
    nlinarith [sq_nonneg (qJet.d2 y)]
  rw [← qJet_d3_eq_deriv3_regular hy]
  exact nonneg_of_mul_nonneg_right hprod hp

theorem second_monotone {x : ℝ} (hx : x ∈ e8SlopeRange) :
    MonotoneOn (deriv (deriv e8RegularQ)) (Icc 0 x) := by
  have hd (y : ℝ) (hy : y ∈ Icc 0 x) :
      DifferentiableAt ℝ (deriv (deriv e8RegularQ)) y :=
    (((e8RegularQ_contDiffAt_interval hx hy).derivWithin (m := 3) (by norm_num)).derivWithin
      (m := 2) (by norm_num)).differentiableAt (by norm_num)
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
  · exact fun y hy => (hd y hy).continuousAt.continuousWithinAt
  · exact fun y hy => (hd y (interior_subset hy)).differentiableWithinAt
  · intro y hy
    have hy' : y ∈ Ioo 0 x := by simpa using hy
    exact third_nonnegative (e8SlopeRange_downward hx hy'.1 hy'.2.le)

theorem bounded_argument_jets {s : ℝ} (hs : s ∈ e8SlopeRange) (hstop : s ≤ 63/20) :
    e8RegularQ s ≤ 1 ∧ deriv e8RegularQ s ≤ 1 ∧ deriv (deriv e8RegularQ) s ≤ 1 := by
  have hs0 : 0 ≤ s := le_of_lt (e8SlopeRange_subset_pos hs)
  have hmem : s ∈ Icc (0 : ℝ) (63/20) := ⟨hs0, hstop⟩
  have htop : (63/20 : ℝ) ∈ Icc (0 : ℝ) (63/20) := by constructor <;> norm_num
  refine ⟨(e8RegularQ_mono_of_mem hs endpoint_mem hstop).trans endpoint_jets.1, ?_, ?_⟩
  · exact (E8RatioMonotonicity.e8LargeSStructureCertified.derivative_mono
      _ endpoint_mem hmem htop hstop).trans endpoint_jets.2.1
  · exact (second_monotone endpoint_mem hmem htop hstop).trans endpoint_jets.2.2

#print axioms endpoint_jets
#print axioms third_nonnegative
#print axioms second_monotone
#print axioms bounded_argument_jets

end GeneralCK.E8LargeTSAxis

end


