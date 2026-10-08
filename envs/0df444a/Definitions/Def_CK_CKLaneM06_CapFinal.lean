-- Prove2me | Definitions.Def_CK_CKLaneM06_CapFinal
-- name    : CK_CKLaneM06_CapFinal
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T00:42:12.011908+00:00
-- url     : https://prove2.me/theorems/a5f32fd0-45ed-4568-af33-cbf3593dc744
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CapFinal` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CapFinal` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CapFinal` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CapFinal (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CapFinal.lean)

import Definitions.Def_CK_CKLaneM06_CapSSAgg
import Definitions.Def_CK_CKLaneM06_CapXHAgg

-- ===== source module CKLaneM06.CapFinal =====
section

/-!
# Lane M06: the cap theorem (5), CAP_REGION — closed

* `capPsi : CapPsi` — archive form `ζ ≥ R_ψ` for every feasible split, canonical laws with
  `a, b ∈ [1/10, 9/10]` and mean entropy deficit `s ≤ 3/40`;
* `centralCap : CentralCap` — the hybrid row (verbatim `CKLaneN23.CentralCap`, route row
  `CentralSquare` cap part), via `hybrid_gap_le_psi`.

Assembled from the two populations:
* `CapSSAgg.capSameSide : CapSameSide` — `SAME_SIDE_CAP` root `[1/10,1/2]²`, 2,108 archived leaves
  (trapezoid checker, fleet `M06-cap-ss`);
* `CapXHAgg.capCross : CapCross` — `EXPANDED_CAP` root `[1/10,1/2] × [1/2,9/10]`, 14,525 archived leaves
  (trapezoid + secant checkers, fleet `M06-cap-xh`).
-/

set_option autoImplicit false

namespace CKLaneM06.Cap.CapFinal

open CKLaneM06.Cap

/-- **Cap theorem (5)**, archive form: `ζ ≥ R_ψ` on the whole cap region at depth `3/40`. -/
theorem capPsi : CapPsi := capPsi_of_parts CapSSAgg.capSameSide CapXHAgg.capCross

/-- **CentralCap** (N23 row 3): strict psi-activity, `a,b ∈ [1/10,9/10]`, `s ≤ 3/40` ⟹ `gap ≤ cost`. -/
theorem centralCap : CentralCap := centralCap_of_parts CapSSAgg.capSameSide CapXHAgg.capCross

end CKLaneM06.Cap.CapFinal

end


