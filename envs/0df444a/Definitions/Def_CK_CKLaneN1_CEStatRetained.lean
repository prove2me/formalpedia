-- Prove2me | Definitions.Def_CK_CKLaneN1_CEStatRetained
-- name    : CK_CKLaneN1_CEStatRetained
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T21:36:06.651826+00:00
-- url     : https://prove2.me/theorems/f9cca0ee-5f06-4690-a8cb-e3cb6a1b485a
-- title:
--   Courtade–Kumar proof module `CKLaneN1.CEStatRetained` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.CEStatRetained` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.CEStatRetained` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.CEStatRetained (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/CEStatRetained.lean)

import Definitions.Def_CK_CKLaneN1_CEStat
import Definitions.Def_CK_GeneralCK_PsiBoundaryLeafReplay

-- ===== source module CKLaneN1.CEStatRetained =====
section

set_option autoImplicit false

/-!
# Lane N1: CE-stat S.3 row 1 — retained-domain exclusion

`0 < t_C ≤ 1/80000` and `A ≤ 21/200` force `a + c < S = 10⁻⁴`:
`b < t_C ≤ 1/80000` (chart order), so `e < f = H(b) ≤ H(1/80000) ≤ 1/4000`; then
`c - a ≤ (21/200)(e + f) < 21/400000` and `a < b`, whence `a + c < 2/80000 + 21/400000 < 10⁻⁴`.
-/

namespace CKLaneN1.CEStat

open GeneralCK GeneralCK.SmallMeanPhiCutoff

/-- `a = ι(e) < b = ι(f)` for `0 < e < f ≤ 1`. -/
theorem inv_lt_inv {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f ≤ 1) :
    entropyInverse e < entropyInverse f := by
  have hf0 : 0 < f := he.trans hef
  have h1 := entropyInverse_spec he.le (hef.le.trans hf)
  have h2 := entropyInverse_spec hf0.le hf
  by_contra hn
  have hle : entropyInverse f ≤ entropyInverse e := le_of_not_gt hn
  have := H_strictMonoOn.monotoneOn ⟨h2.1, h2.2.1⟩ ⟨h1.1, h1.2.1⟩ hle
  rw [h1.2.2, h2.2.2] at this
  linarith

/-- `H(1/80000) ≤ 1/4000` (`80000 ≤ 2^17`). -/
theorem H_one_80000_le : H (1 / 80000) ≤ 1 / 4000 := by
  refine BoundaryStrip.H_le_of_pow (v := 1 / 80000) (by norm_num) (by norm_num) (b := 80000)
    (by norm_num) (by norm_num) (p := 17) (k := 1) (by norm_num) (by norm_num) ?_
  norm_num

/-- **S.3 row 1 (CLOSED here):** retained-domain exclusion. -/
theorem retainedDomainExclusion : RetainedDomainExclusion := by
  intro e f c hp htc hA
  have hord := chart_order hp
  obtain ⟨he, hef, hf, hbc, hc, -⟩ := hp
  have hf0 : 0 < f := he.trans hef
  obtain ⟨hb0, hb2, hHb⟩ := entropyInverse_spec hf0.le hf
  have hab := inv_lt_inv he hef hf
  have hb80 : entropyInverse f < 1 / 80000 := hord.1.trans_le htc
  have hfH : f ≤ 1 / 4000 := by
    have hm := H_strictMonoOn.monotoneOn ⟨hb0, hb2⟩ ⟨by norm_num, by norm_num⟩ hb80.le
    rw [hHb] at hm
    exact hm.trans H_one_80000_le
  have hE : 0 < e + f := by linarith
  have hcA : c - entropyInverse e ≤ 21 / 200 * (e + f) := by
    unfold chartA at hA
    rwa [div_le_iff₀ hE] at hA
  unfold retainedCutoff
  nlinarith

end CKLaneN1.CEStat

end


