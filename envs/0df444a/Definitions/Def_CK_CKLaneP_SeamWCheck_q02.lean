-- Prove2me | Definitions.Def_CK_CKLaneP_SeamWCheck_q02
-- name    : CK_CKLaneP_SeamWCheck_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:40:15.141099+00:00
-- url     : https://prove2.me/theorems/0434c371-6717-4dbf-a323-793ba9663663
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamWCheck (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamWCheck (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamWCheck (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamWCheck (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamWCheck (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneP_SeamWCheck_q01

set_option autoImplicit false
namespace CKLaneP
open GeneralCK GeneralCK.Certificates.Mixed Set
namespace WCell
def Yv (c : WCell) : ℚ := c.A0v * c.EH / (c.thb / c.xb - c.lam * c.EH)
def Xmin (c : WCell) : ℚ := (1 - 2 * Sq + 2 * c.p0) / (2 * c.fH)
def Vmin (c : WCell) : ℚ := (1 - 2 * c.qd) / c.EH
def Wmax (c : WCell) : ℚ := 1 / (2 * c.eL)

end WCell

/-- The Boolean check of a W-cell (case A). -/
def wcheckA (c : WCell) : Bool := decide (
  VD.okDy 60 c.np0 = true ∧ VD.okDy 60 c.np1 = true ∧ VD.okDy 60 c.nql = true ∧
  VD.okDy 60 c.nq = true ∧ VD.okDy 60 c.nvb = true ∧ VD.okDy 60 c.nva = true ∧
  VD.okDy 60 c.nxb = true ∧ VD.okDy 60 c.nx2 = true ∧
  dyq c.np0 ≤ c.p0 ∧ c.p1 ≤ dyq c.np1 ∧ 0 < c.p0 ∧ c.p0 < c.p1 ∧ c.p1 ≤ Sq / 2 ∧
  0 < c.t0 ∧ c.t0 < c.t1 ∧ c.t1 ≤ 1 ∧
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
  0 ≤ c.DCb + c.R0 + c.B0 - c.M * c.Yv ^ 2 / (2 * c.EL))

end CKLaneP


