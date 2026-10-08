-- Prove2me | Definitions.Def_CK_E8TightArgumentJets
-- name    : CK_E8TightArgumentJets
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T18:19:55.499117+00:00
-- url     : https://prove2.me/theorems/3a22cfa3-e861-4070-8c6c-bbd6ccb37574
-- title:
--   Courtade–Kumar proof module `E8TightArgumentJets` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8TightArgumentJets` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8TightArgumentJets` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8TightArgumentJets (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8TightArgumentJets.lean)

import Definitions.Def_CK_E8BoundedArgumentJets

-- ===== source module E8TightArgumentJets =====
section

namespace GeneralCK.E8LargeTSAxis

open Set Certificates
open E8CompactAnchorRegularJetDerivatives E8TAxisDeltaDirectionalJet
open E8TAxisStableInterval E8TAxisReparamInterval DyadicInterval

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem endpoint_jets_tight : e8RegularQ (63/20) ≤ 1/2 ∧
    deriv e8RegularQ (63/20) ≤ 1/5 ∧ deriv (deriv e8RegularQ) (63/20) ≤ 1/10 := by
  obtain ⟨a, ha, hapos, hay⟩ := E8LargeSShift.covers
  have hc := checked_stable_contains_canonical E8LargeSShift.whole_primitive_checks.1
    E8LargeSShift.whole_primitive_checks.2 E8LargeSShift.logTwo_checked
    E8LargeSShift.whole_denominators E8LargeSShift.whole_y_derivative_positive ha hapos
  rw [hay] at hc
  have h0 : (eval (xBox E8LargeSShift.wholeInput) (yBox E8LargeSShift.wholeInput)).d0.hi*2 ≤
      scale E8LargeSShift.precision := by decide +kernel
  have h1 : (eval (xBox E8LargeSShift.wholeInput) (yBox E8LargeSShift.wholeInput)).d1.hi*5 ≤
      scale E8LargeSShift.precision := by decide +kernel
  have h2 : (eval (xBox E8LargeSShift.wholeInput) (yBox E8LargeSShift.wholeInput)).d2.hi*10 ≤
      scale E8LargeSShift.precision := by decide +kernel
  have upper {b : DyadicInterval E8LargeSShift.precision} {x : ℝ} {n : ℤ}
      (hn : 0 < n) (hx : b.Contains x) (hb : b.hi*n ≤ scale E8LargeSShift.precision) :
      x ≤ 1/(n : ℝ) := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    apply (le_div_iff₀ hn').2
    apply (mul_le_mul_iff_right₀ (scale_cast_pos E8LargeSShift.precision)).mp
    have hh : (b.hi : ℝ)*(n : ℝ) ≤ (scale E8LargeSShift.precision : ℝ) := by exact_mod_cast hb
    have hm := (mul_le_mul_of_nonneg_right hx.2 hn'.le).trans hh
    nlinarith only [hm]
  have hv : qJet.d0 (63/20) ≤ 1/2 := upper (by norm_num : (0:ℤ)<2) hc.1 h0
  have hd : qJet.d1 (63/20) ≤ 1/5 := upper (by norm_num : (0:ℤ)<5) hc.2.1 h1
  have hdd : qJet.d2 (63/20) ≤ 1/10 := upper (by norm_num : (0:ℤ)<10) hc.2.2.1 h2
  rw [qJet_d0, ← e8RegularQ_eq_e8Q (by norm_num : (0 : ℝ) ≤ 63/20)] at hv
  rw [qJet_d1_eq_deriv_regular endpoint_mem] at hd
  rw [qJet_d2_eq_deriv2_regular endpoint_mem] at hdd
  exact ⟨hv, hd, hdd⟩

theorem bounded_argument_jets_tight {s : ℝ} (hs : s ∈ e8SlopeRange) (hstop : s ≤ 63/20) :
    e8RegularQ s ≤ 1/2 ∧ deriv e8RegularQ s ≤ 1/5 ∧ deriv (deriv e8RegularQ) s ≤ 1/10 := by
  have hs0 : 0 ≤ s := le_of_lt (e8SlopeRange_subset_pos hs)
  have hmem : s ∈ Icc (0 : ℝ) (63/20) := ⟨hs0, hstop⟩
  have htop : (63/20 : ℝ) ∈ Icc (0 : ℝ) (63/20) := by constructor <;> norm_num
  refine ⟨(e8RegularQ_mono_of_mem hs endpoint_mem hstop).trans endpoint_jets_tight.1, ?_, ?_⟩
  · exact (E8RatioMonotonicity.e8LargeSStructureCertified.derivative_mono
      _ endpoint_mem hmem htop hstop).trans endpoint_jets_tight.2.1
  · exact (second_monotone endpoint_mem hmem htop hstop).trans endpoint_jets_tight.2.2

#print axioms endpoint_jets_tight
#print axioms bounded_argument_jets_tight

end GeneralCK.E8LargeTSAxis

end


