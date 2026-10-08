-- Prove2me | Definitions.Def_CK_CKLaneN1_R3Assembly_q02
-- name    : CK_CKLaneN1_R3Assembly_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T17:56:11.637672+00:00
-- url     : https://prove2.me/theorems/f648b77b-9e6e-4a37-8b51-93b740bac461
-- title:
--   Courtade–Kumar proof module `CKLaneN1.R3Assembly (piece 3 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.R3Assembly (piece 3 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.R3Assembly (piece 3 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.R3Assembly (piece 3 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/R3Assembly (piece 3 of 5).lean)

import Definitions.Def_CK_CKLaneN1_R3Assembly_q01

set_option autoImplicit false
namespace CKLaneN1.R3
open GeneralCK CKLaneN1 CKLaneE.FP GeneralCK.SmallMeanPhiCutoff
/-- **Row-3 assembly** (conditional on the cover). -/
theorem transverse_of_cover (hcov : CoverStmt) : CKLaneN1.CEStat.TransverseCurvatureOwner := by
  intro e f c hp _h1 h2 hA
  obtain ⟨hpf, hret⟩ := hp
  have hpf' := hpf
  obtain ⟨he, hef, hf, hbc, hc, _hs⟩ := hpf'
  have hlb := CKLaneM07.CE.gapLB_le hpf
  have hie := entropyInverse_spec he.le (hef.le.trans hf)
  have hif := entropyInverse_spec (he.trans hef).le hf
  have ha : 0 < entropyInverse e := entropyInverse_pos he (hef.le.trans hf)
  have hab : entropyInverse e < entropyInverse f := entropyInverse_strictMonoOn
    ⟨he.le, hef.le.trans hf⟩ ⟨(he.trans hef).le, hf⟩ hef
  have htc := CKLaneN1.CEStat.chart_order hpf
  have hb100 : entropyInverse f < 1 / 100 := lt_of_lt_of_le htc.1 h2
  set a := entropyInverse e with ha_def
  set b := entropyInverse f with hb_def
  have hEF : 0 < e + f := by linarith
  have hA' : c - a ≤ (H a + H b) / 20 := by
    unfold CKLaneN1.CEStat.chartA at hA
    rw [← ha_def, div_le_iff₀ hEF] at hA
    rw [hie.2.2, hif.2.2]
    linarith
  have hret' : 1 / 10000 < a + c := by rw [retainedCutoff_eq] at hret; linarith
  have hlo := a_lower ha hab hbc hc hret' hA'
  have hlo' : (1 : ℝ) / 131072 ≤ a := by
    have : ((alo : ℚ) : ℝ) = 1 / 131072 := by simp [alo]
    linarith
  have hy : 0 < c - a := by linarith
  set y := c - a with hy_def
  set z := (b - a) / y with hz_def
  have hz0 : 0 < z := div_pos (by linarith) hy
  have hz1 : z < 1 := by rw [hz_def, div_lt_one hy]; linarith
  have hbz : a + z * y = b := by rw [hz_def]; field_simp; ring
  have hcy : a + y = c := by rw [hy_def]; ring
  have key := hcov a z y hlo' (by linarith) hz0 hz1 hy (by linarith) (by rw [hbz]; linarith)
    (by linarith) (by rw [hbz]; exact hb100)
  rw [hbz, hcy, hie.2.2, hif.2.2] at key
  linarith

/-! ## Octave dispatch -/

end CKLaneN1.R3


