-- Prove2me | Definitions.Def_CK_CKLaneE_CertEP3_part00
-- name    : CK_CKLaneE_CertEP3_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T12:44:59.213407+00:00
-- url     : https://prove2.me/theorems/39b8b0d3-f449-421a-97d5-5d4930204ee3
-- title:
--   Courtade–Kumar proof module `CKLaneE.CertEP3 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.CertEP3 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.CertEP3 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.CertEP3 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/CertEP3 (part 1 of 2).lean)

import Definitions.Def_CK_CKLaneE_CertEP
import Definitions.Def_CK_CKLaneE_DropTight

/-!
# Lane E: radial (endpoint) certificate `ep3` (= `ep` with the tight drop bounds of `CKLaneE.DT`)

Identical to `CKLaneE.EP` except that the entropy drop is bounded by `Dx = min(DHi, Dt)` (direct form)
and `Kx = min(K, Dt/dLo²)` (normalized forms), see `CKLaneE.DT.drop_bounds`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.EP3

open GeneralCK GeneralCK.Scalar CKLaneE.FP CKLaneE.Chart CKLaneE.LS CKLaneE.DT
open CKLaneE.EP (Jlo Jlo_le pbar_nonneg)
open CKLaneE.NLS (H_le_H box_geometry)


def modeA (B : Box3) (vS vI vc : ℚ) : Bool :=
  decide (0 < dLo B ∧ B.E2 * (1 - 2 * vc) ≤ dLo B * Hlo vc ∧ 0 ≤ lamLo vc) &&
    (decide (Dx B * pbar vS vI ≤ dLo B * Jlo vc) ||
      decide (Kx B * dHi B * pbar vS vI ≤ Jlo vc))

def modeB (B : Box3) (vS vI vc : ℚ) : Bool :=
  decide (0 < dHi B ∧ dHi B * Hhi vc ≤ B.E1 * (1 - 2 * vc) ∧
    Kx B * pbar vS vI * B.E2 * LqHi ≤ 2 * Hlo vc)

def check (B : Box3) (vS vI vc : ℚ) (mode : ℕ) : Bool :=
  boxOk B && decide (B.E1 ≤ B.E2) && ptOk (aLo B) && ptOk (aHi B) && ptOk B.b1 && ptOk B.b2 &&
    ptOk (mHi B) && anchorOk vS (sHi B) && anchorOk vI (IHi B) && decide (IHi B < 1) &&
    ptOk vc && decide (vc < 1 / 2) && decide (0 ≤ K B) &&
    (if mode = 0 then modeA B vS vI vc else modeB B vS vI vc)

end CKLaneE.EP3


