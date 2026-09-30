-- Prove2me | Definitions.Def_CK_CKLaneP_SeamWCheck_part00
-- name    : CK_CKLaneP_SeamWCheck_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:11:39.153933+00:00
-- url     : https://prove2.me/theorems/0f4b53f0-b220-43dc-81d0-a9eb3ae29c71
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamWCheck (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamWCheck (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamWCheck (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamWCheck (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamWCheck (part 1 of 2).lean)

import Definitions.Def_CK_CKLaneP_SeamWBase
import Definitions.Def_CK_CKLaneP_ThetaLip
import Definitions.Def_CK_CKLaneP_DCBound2
/-
Lane P — the value-form (W-mode) seam cell checker, case A (`0 < t0 < t1 ≤ 1`).

Away from the diagonal the normalized mean-value forms lose too much; here every piece of the
seam base and the dip is bounded in value form (logarithms of rational ratios via `logUpQ/logDnQ`):
    DC ≥ β_lo²·max(0, DCraw),   ∫R' ≥ max(0, min_β (c1·β − (6/E_lo)β²)),  c1 = Pmin·log((1+fL/eH)/2),
    bulk ≥ max(0, S/2 − qd)·max(0, 9/40 (1−κh)², Pmin·log((1+κh)²/(4κh)) − (Pmax−Pmin)·log(2/(1+κl))),
    dip ≤ M·Y²/(2E_lo),   Y = A0·E_hi/(θ̄/x̄ − λE_hi),   A0 = (Pmax/2)·log(fH/eL).
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

structure WCell where
  p0 : ℚ
  p1 : ℚ
  np0 : ℕ
  np1 : ℕ
  t0 : ℚ
  t1 : ℚ
  nql : ℕ
  nq : ℕ
  nvb : ℕ
  nva : ℕ
  xb : ℚ
  nxb : ℕ
  nx2 : ℕ
deriving Repr

namespace WCell

def blo (c : WCell) : ℚ := c.t0 * (Sq / 2 - c.p1)
def bhi (c : WCell) : ℚ := c.t1 * (Sq / 2 - c.p0)
def qd (c : WCell) : ℚ := dyq c.nq
def eL (c : WCell) : ℚ := (dy c.np0).Hlo
def eH (c : WCell) : ℚ := (dy c.np1).Hhi
def fL (c : WCell) : ℚ := (dy c.nql).Hlo
def fH (c : WCell) : ℚ := (dy c.nq).Hhi
def EL (c : WCell) : ℚ := c.eL + c.fL
def EH (c : WCell) : ℚ := c.eH + c.fH
def Jq (c : WCell) : ℚ := (dy c.nq).Jlo
def rs0 (c : WCell) : ℚ := (dy c.np0).Shi
def Pmax (c : WCell) : ℚ := PmaxQ (dy c.nvb)
def Pmin (c : WCell) : ℚ := PminQ (dy c.nva) (dy c.nvb)
def lam (c : WCell) : ℚ := c.Pmax / (1 - 2 * Sq + 2 * c.p0)
def thb (c : WCell) : ℚ := (dy c.nxb).Slo
def M (c : WCell) : ℚ := Mof c.xb c.nx2
def kh (c : WCell) : ℚ := c.eH / c.fL
end WCell
end CKLaneP


