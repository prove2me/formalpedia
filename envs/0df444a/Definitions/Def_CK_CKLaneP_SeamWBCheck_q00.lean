-- Prove2me | Definitions.Def_CK_CKLaneP_SeamWBCheck_q00
-- name    : CK_CKLaneP_SeamWBCheck_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T08:25:19.321982+00:00
-- url     : https://prove2.me/theorems/94866fa5-3ae7-4793-a1c4-1b3c7ede9f59
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamWBCheck (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamWBCheck (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamWBCheck (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamWBCheck (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamWBCheck (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneP_SeamWBCheck_part00

set_option autoImplicit false
namespace CKLaneP
open GeneralCK GeneralCK.Certificates.Mixed Set
/-- The Boolean check of a WB-cell (case B, value form). -/
def wcheckB (c : WCell) : Bool := decide (
  VD.okDy 60 c.np0 = true ∧ VD.okDy 60 c.np1 = true ∧ VD.okDy 60 c.nql = true ∧
  VD.okDy 60 c.nq = true ∧ VD.okDy 60 c.nvb = true ∧ VD.okDy 60 c.nva = true ∧
  VD.okDy 60 c.nxb = true ∧ VD.okDy 60 c.nx2 = true ∧
  dyq c.np0 ≤ c.p0 ∧ c.p1 ≤ dyq c.np1 ∧ 0 < c.p0 ∧ c.p0 < c.p1 ∧ c.p1 ≤ Sq / 2 ∧
  1 ≤ c.t0 ∧ c.t0 < c.t1 ∧ c.t1 ≤ 2 ∧
  dyq c.nql ≤ c.p0 + c.blo ∧ c.p1 + c.bhi ≤ c.qd ∧ c.qd ≤ 1 / 10000 ∧
  0 < (dy c.np0).a1 + (dy c.np0).a2 ∧ 0 < c.eL ∧ 0 < c.fL ∧ 0 < c.Jq ∧ c.eH ≤ c.fL ∧
  dyq c.nvb ≤ 1 / 10000 ∧ 4 ≤ (dy c.nvb).a1 ∧
  0 < c.Xmin ∧ 1 - 2 * (dy c.nvb).v ≤ 2 * c.Xmin * (dy c.nvb).Hlo ∧
  0 < c.Vmin ∧ 1 - 2 * (dy c.nvb).v ≤ 2 * c.Vmin * (dy c.nvb).Hlo ∧
  2 * c.Wmax * (dy c.nva).Hhi ≤ 1 - 2 * (dy c.nva).v ∧ 1 < (dy c.nva).b1 ∧
  0 < c.xb ∧ (dy c.nxb).v < 1 / 2 ∧ 1 - 2 * (dy c.nxb).v ≤ 2 * c.xb * (dy c.nxb).Hlo ∧
  2 * c.xb * (dy c.nx2).Hhi ≤ 1 - 2 * (dy c.nx2).v ∧ 0 < (dy dhN).kapLo ∧ 0 ≤ c.M ∧
  0 ≤ c.Pmin ∧ c.Pmin ≤ c.Pmax ∧
  1 ≤ ⌊(1 + c.fL / c.eH) / 2 * 2 ^ 60⌋₊ ∧ 1 ≤ ⌊(1 + c.kh) ^ 2 / (4 * c.kh) * 2 ^ 60⌋₊ ∧
  1 ≤ ⌊(c.p0 + c.blo) / c.p1 * 2 ^ 60⌋₊ ∧ 1 ≤ ⌊(c.p1 + c.p0 + c.blo) / (2 * c.p1) * 2 ^ 60⌋₊ ∧
  c.A0v + c.lam * (Sq - 2 * c.p0) < c.thb ∧ c.lam * c.EH < c.thb / c.xb ∧
  0 ≤ c.DCb + c.RB - c.M * c.Yv ^ 2 / (2 * c.EL))

end CKLaneP


