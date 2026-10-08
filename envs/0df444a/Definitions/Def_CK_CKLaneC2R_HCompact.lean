-- Prove2me | Definitions.Def_CK_CKLaneC2R_HCompact
-- name    : CK_CKLaneC2R_HCompact
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T04:19:31.552988+00:00
-- url     : https://prove2.me/theorems/7b71a929-3734-4f35-864e-33a9c9404569
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.HCompact` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.HCompact` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.HCompact` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.HCompact (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/HCompact.lean)

import Definitions.Def_CK_CKLaneC2R_CompactAll
import Definitions.Def_CK_CKLaneC2R_EndpointCover

-- ===== source module CKLaneC2R.HCompact =====
section

/-!
# Lane C2: `hcompact` at the exact consumer type

`GeneralCK.Reflection.curvature_nonneg_of_remaining_regions_post_next_band` takes
`hcompact : ∀ a z, a ∈ Icc (3/20) (999/1000) → z ∈ Ioo (43/500) 1 → 0 ≤ curvature a (a*z)`.
The compact part `z ≤ 999/1000` is `compact_all_certified` (5,079 reflective compact cells);
the endpoint part `999/1000 ≤ z < 1` is `EndpointCover.cover` (regular expression cells).
-/

namespace CKLaneC2R

theorem endpoint_all_certified {a z : ℝ} (ha1 : (3 / 20 : ℝ) ≤ a) (ha2 : a ≤ 999 / 1000)
    (hz1 : (999 / 1000 : ℝ) ≤ z) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  have q0 : ((3 / 20 : ℚ) : ℝ) = 3 / 20 := by norm_num
  have q6 : ((999 / 1000 : ℚ) : ℝ) = 999 / 1000 := by norm_num
  have q7 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  exact EndpointCover.cover (by rw [q0]; exact ha1) (by rw [q6]; exact ha2)
    (by rw [q6]; exact hz1) (by rw [q7]; exact hz.le) hz

theorem hcompact_certified : ∀ a z : ℝ, a ∈ Set.Icc (3 / 20 : ℝ) (999 / 1000) →
    z ∈ Set.Ioo (43 / 500 : ℝ) 1 → 0 ≤ GeneralCK.Reflection.curvature a (a * z) := by
  intro a z ha hz
  rcases le_or_gt z (999 / 1000) with h | h
  · exact (compact_all_certified ha.1 ha.2 hz.1.le h).le
  · exact (endpoint_all_certified ha.1 ha.2 h.le hz.2).le

end CKLaneC2R

end


