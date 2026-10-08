-- Prove2me | Definitions.Def_CK_CKLaneC3_Origin
-- name    : CK_CKLaneC3_Origin
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T18:52:18.886949+00:00
-- url     : https://prove2.me/theorems/14de7be4-41ee-4d68-9be7-1dd9d5a9caba
-- title:
--   Courtade–Kumar proof module `CKLaneC3.Origin` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.Origin` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.Origin` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.Origin (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/Origin.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8SAxisOriginClosure
import Definitions.Def_CK_GeneralCK_PureGapE8CertificateReduction

-- ===== source module CKLaneC3.Origin =====
section

/-!
# Lane C3 — the `origin` field of `GeneralCK.E8CertificateOwners` (by-product)

`0 < e8Delta e8Q s t` on the admissible region with `s + t ≤ 2/25`, from the unconditional
origin second-`s`-derivative bound `e8RegularDeltaSS_pos_on_origin` and the consumer-side
reduction `e8Delta_pos_of_second_s_derivative` (integrate twice in `s` from `s = 0`).
Same proof as `CKLaneC3.Compact.originOwner`, packaged without the compact fleet imports.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC3.Origin

open GeneralCK

/-- The `origin` field of `GeneralCK.E8CertificateOwners`, with its exact type. -/
theorem origin : E8PositiveOn fun s t => s + t ≤ 2 / 25 := by
  intro s t hadm hR
  have hR' : s + t ≤ 2 / 25 := hR
  apply e8Delta_pos_of_second_s_derivative hadm
  intro u hu
  exact e8RegularDeltaSS_pos_on_origin (hadm.mono_s hu.1 hu.2.le) (by linarith [hu.2, hR'])

end CKLaneC3.Origin

end


