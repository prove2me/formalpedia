-- Prove2me | Definitions.Def_CK_CKLaneP_SeamWCheck_q01
-- name    : CK_CKLaneP_SeamWCheck_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:36:33.810978+00:00
-- url     : https://prove2.me/theorems/eed0faa2-e4cf-4232-b13a-eae02d073f94
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamWCheck (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamWCheck (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamWCheck (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamWCheck (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamWCheck (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneP_SeamWCheck_q00

set_option autoImplicit false
namespace CKLaneP
open GeneralCK GeneralCK.Certificates.Mixed Set
namespace WCell
def DCraw (c : WCell) : ℚ :=
  1 / (c.p1 * (2 + c.bhi / c.p0) * L2hiD) - c.rs0 / (4 * L2loD * (c.p0 * (1 - c.p0)) * c.Jq)
def DC0 (c : WCell) : ℚ := c.blo ^ 2 * max 0 c.DCraw
def DC2 (c : WCell) : ℚ :=
  c.blo * max 0 (logDnQ ((c.p0 + c.blo) / c.p1)) / (2 * L2hiD) -
    2 * c.rs0 * (((c.qd * logUpQ (2 * c.qd / (c.qd + c.p0)) / 2 -
      c.p0 * max 0 (logDnQ ((c.p1 + c.p0 + c.blo) / (2 * c.p1))) / 2) +
        c.bhi ^ 2 / (4 * (1 - c.qd))) / L2loD) / c.Jq
def DCb (c : WCell) : ℚ := max c.DC0 c.DC2
def A0v (c : WCell) : ℚ := c.Pmax / 2 * logUpQ (c.fH / c.eL)
end WCell
end CKLaneP


