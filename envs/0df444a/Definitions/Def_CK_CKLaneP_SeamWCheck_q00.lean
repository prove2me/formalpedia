-- Prove2me | Definitions.Def_CK_CKLaneP_SeamWCheck_q00
-- name    : CK_CKLaneP_SeamWCheck_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:27:09.676894+00:00
-- url     : https://prove2.me/theorems/8368e066-f669-4fcd-ba65-6fe6091427fc
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamWCheck (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamWCheck (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamWCheck (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamWCheck (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamWCheck (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneP_SeamWCheck_part00


set_option autoImplicit false
namespace CKLaneP
open GeneralCK GeneralCK.Certificates.Mixed Set
namespace WCell
def kl (c : WCell) : ℚ := c.eL / c.fH
def c1v (c : WCell) : ℚ := c.Pmin * logDnQ ((1 + c.fL / c.eH) / 2)
def R0 (c : WCell) : ℚ :=
  max 0 (min (c.c1v * c.blo - 6 / c.EL * c.blo ^ 2) (c.c1v * c.bhi - 6 / c.EL * c.bhi ^ 2))
def Jv (c : WCell) : ℚ :=
  max (9 / 40 * (1 - c.kh) ^ 2)
    (c.Pmin * logDnQ ((1 + c.kh) ^ 2 / (4 * c.kh)) - (c.Pmax - c.Pmin) * logUpQ (2 / (1 + c.kl)))
def B0 (c : WCell) : ℚ := max 0 (Sq / 2 - c.qd) * max 0 c.Jv
end WCell
end CKLaneP


