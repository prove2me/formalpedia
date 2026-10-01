-- Prove2me | Definitions.Def_CK_E8RatioFactor
-- name    : CK_E8RatioFactor
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:23:29.718831+00:00
-- url     : https://prove2.me/theorems/d4d85100-cc55-499e-ba59-48889f9d237d
-- title:
--   Courtade–Kumar proof module `E8RatioFactor` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8RatioFactor` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8RatioFactor` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8RatioFactor (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8RatioFactor.lean)

import Definitions.Def_CK_E8StableRatio

-- ===== source module E8RatioFactor =====
section

/-! Compact entropy-quotient factor for the remaining E8 sign. -/

namespace GeneralCK.E8RatioMonotonicity

open Set Filter
open Certificates.E8TAxisStableScalar
open Certificates.E8TAxisStableJet5
open Certificates.E8HistoricalLogConvexityBridge

theorem stable_gap_pos {a : ℝ} (ha : 0 < a) : 0 < 2 * ell a - r a ^ 2 := by
  have hp : 0 < historicalYPrime a := by
    rw [← yJet_d1_eq_historicalYPrime a ha]
    exact stable_yPrime_pos ha
  unfold historicalYPrime at hp
  have hf := (mul_pos_iff_of_pos_left
    (div_pos (by norm_num : (0 : ℝ) < 2) log_two_pos)).mp hp
  have hn := (div_pos_iff_of_pos_right
    (mul_pos (q_pos a) (pow_pos (ell_pos ha) 2))).mp hf
  exact (mul_pos_iff_of_pos_left (h_pos ha)).mp hn

theorem hasDerivAt_historicalYPrime_pos {a : ℝ} (ha : 0 < a) :
    HasDerivAt historicalYPrime
      (historicalYPrime a * (historicalE a + historicalX a)) a := by
  have hh := hasDerivAt_h a
  have hb := hasDerivAt_ell a
  have hr := hasDerivAt_r a
  have hq := hasDerivAt_q a
  have hD := ((hasDerivAt_const a 2).mul hb).sub (hr.pow 2)
  have hfrac := (hh.mul hD).div (hq.mul (hb.pow 2))
    (mul_ne_zero (q_pos a).ne' (pow_ne_zero 2 (ell_pos ha).ne'))
  have hy := ((hasDerivAt_const a 2).div_const (Real.log 2)).mul hfrac
  convert! hy using 1
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
    Pi.div_apply, historicalYPrime, historicalE, historicalX]
  field_simp [(q_pos a).ne', (ell_pos ha).ne', (h_pos ha).ne',
    (stable_gap_pos ha).ne', log_two_pos.ne']
  rw [← one_sub_r_sq]
  ring

theorem stableE_eq_historicalE_pos {a : ℝ} (ha : 0 < a) :
    stableE a = historicalE a := by
  have heq : yJet.d1 =ᶠ[nhds a] historicalYPrime := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    exact yJet_d1_eq_historicalYPrime b hb
  have hj := (yJet_soundAt ha).2.1.congr_of_eventuallyEq heq.symm
  have h2 := hj.unique (hasDerivAt_historicalYPrime_pos ha)
  rw [stableE, xJet_d1_eq_historicalXPrime a ha,
    xJet_d2_eq_historicalXPrime_mul a ha,
    yJet_d1_eq_historicalYPrime a ha, h2]
  have hyp : 0 < historicalYPrime a := by
    rw [← yJet_d1_eq_historicalYPrime a ha]
    exact stable_yPrime_pos ha
  field_simp [(historicalXPrime_pos a ha).ne', hyp.ne']
  ring

theorem hasDerivAt_historicalE_pos {a : ℝ} (ha : 0 < a) :
    HasDerivAt historicalE (historicalEPrime a) a := by
  have hr := hasDerivAt_r a
  have hq := hasDerivAt_q a
  have hh := hasDerivAt_h a
  have hb := hasDerivAt_ell a
  have hD := ((hasDerivAt_const a 2).mul hb).sub (hr.pow 2)
  have hterm1 := (((hasDerivAt_const a (-3)).mul (hasDerivAt_id a)).mul hq).div hh
    (h_pos ha).ne'
  have hterm2 := (((hasDerivAt_const a 2).mul (hr.pow 3))).div hD (stable_gap_pos ha).ne'
  have hterm3 := (hasDerivAt_const a 4).mul hr
  have hterm4 := ((hasDerivAt_const a 3).mul hr).div hb (ell_pos ha).ne'
  have hder := ((hterm1.add hterm2).add hterm3).sub hterm4
  convert! hder using 1
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
    Pi.div_apply, id_eq, historicalE, historicalEPrime]
  field_simp [(h_pos ha).ne', (ell_pos ha).ne', (stable_gap_pos ha).ne']
  rw [← one_sub_r_sq]
  ring

theorem stableEPrime_eq_historicalEPrime_pos {a : ℝ} (ha : 0 < a) :
    stableEPrime a = historicalEPrime a := by
  have heq : historicalE =ᶠ[nhds a] stableE := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    exact (stableE_eq_historicalE_pos hb).symm
  have hd := (hasDerivAt_stableE a ha
    (stable_xPrime_pos ha).ne' (stable_yPrime_pos ha).ne').congr_of_eventuallyEq heq
  exact hd.unique (hasDerivAt_historicalE_pos ha)

noncomputable def entropyQuotient (a : ℝ) : ℝ :=
  (a / r a - ell a) / h a

/-- Only rational combinations of `k=ell(a)`, `t=r(a)^2`, and the single
entropy quotient `d`. The coefficient formula remains factored. -/
noncomputable def compactFactor (k t d : ℝ) : ℝ :=
  let w := t / (2 * k - t)
  6 / k - 4 - 6 * (1 - t) * w +
    t * (6 * d ^ 2 - 4 * d * (1 + 2 * w - 3 / k) +
      2 + 4 * w + 8 * w ^ 2 - (8 + 10 * w) / k + 3 / k ^ 2)

theorem stableL_eq_compactFactor {a : ℝ} (ha : 0 < a) :
    stableL a = compactFactor (ell a) (r a ^ 2) (entropyQuotient a) := by
  rw [stableL, stableE_eq_historicalE_pos ha,
    stableEPrime_eq_historicalEPrime_pos ha, stableX0_eq_historicalX a ha]
  simp only [historicalE, historicalEPrime, historicalX, compactFactor, entropyQuotient]
  field_simp [(r_pos ha).ne', (ell_pos ha).ne', (h_pos ha).ne', (stable_gap_pos ha).ne']
  rw [← one_sub_r_sq, ← h_add_a_mul_r]
  ring

theorem ratio_monotone_iff_compactFactor_nonneg :
    MonotoneOn ratio (Ioi 0) ↔ ∀ a : ℝ, 0 < a →
      0 ≤ compactFactor (ell a) (r a ^ 2) (entropyQuotient a) := by
  rw [ratio_monotone_iff_stableL_nonneg]
  exact forall_congr' (fun a => forall_congr' (fun ha => by
    rw [stableL_eq_compactFactor ha]))

#print axioms stable_gap_pos
#print axioms stableE_eq_historicalE_pos
#print axioms stableEPrime_eq_historicalEPrime_pos
#print axioms stableL_eq_compactFactor
#print axioms ratio_monotone_iff_compactFactor_nonneg

end GeneralCK.E8RatioMonotonicity

end


