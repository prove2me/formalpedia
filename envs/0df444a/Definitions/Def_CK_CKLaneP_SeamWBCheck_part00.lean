-- Prove2me | Definitions.Def_CK_CKLaneP_SeamWBCheck_part00
-- name    : CK_CKLaneP_SeamWBCheck_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T07:36:07.567536+00:00
-- url     : https://prove2.me/theorems/84716c02-488a-4e82-a22b-460acc6003bb
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamWBCheck (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamWBCheck (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamWBCheck (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamWBCheck (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamWBCheck (part 1 of 2).lean)

import Definitions.Def_CK_CKLaneP_SeamWCheck
/-
Lane P — the value-form seam cell checker for case B (WB): `1 ≤ t0 < t1 ≤ 2` (`q ≥ S/2`).

Base point `y_lo = 2q − S`: `s(y_lo) = cPG(S − q, q)` (`seamCurve_ylo`), right fiber from `p` to `S − q`
(`rightFiber_affine`, derivative bound `c1v − (12/E)(q − x)` as in `wcheckA`), `DC ≥ DCb`, no bulk;
dip `M (y* − y_lo)²/(2E) ≤ M·Yv²/(2E_lo)` (`seam_dip_M`, `Yv` the stationary-point bound).
Needed near `t = 1⁺` for `p ≳ 3.4e-5`, where the stationary point sits just below the top of the
domain (vacuity fails) and the normalized N-B form is too lossy.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

namespace WCell

def LBlo (c : WCell) : ℚ := (2 - c.t1) * (Sq / 2 - c.p1)
def RB (c : WCell) : ℚ := max 0 (c.c1v * c.LBlo - 6 / c.EL * c.bhi ^ 2)

end WCell


end CKLaneP


