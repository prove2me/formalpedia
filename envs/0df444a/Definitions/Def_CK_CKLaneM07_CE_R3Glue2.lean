-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_R3Glue2
-- name    : CK_CKLaneM07_CE_R3Glue2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:25:39.201736+00:00
-- url     : https://prove2.me/theorems/82921feb-35b8-4445-8d42-6fc6ae0d6f80
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.R3Glue2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.R3Glue2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.R3Glue2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.R3Glue2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/R3Glue2.lean)

import Definitions.Def_CK_CKLaneN1_R3Q
import Definitions.Def_CK_CKLaneM07_CE_R3Glue

-- ===== source module CKLaneM07.CE.R3Glue2 =====
section

/-!
# Lane M07 / CE-stat row 3: mixed leaf predicate for the numeric cover

`leaf21 B w := leafOK2 B w || leafOK B w` — N1's sharpened checker `leafOK2` (CKLaneN1.R3Q) first, then
the original `leafOK` (retVac || tcVac || M07 `r3BoxOK`); both are sound into the same `CKLaneN1.R3.Sem`.
`sem_of_tree21` is the tree version (N1 `PT.cover`).  The order only matters for kernel cost: most leaves
of the octaves k ≤ 15 pass `leafOK2`.
-/

set_option autoImplicit false

namespace CKLaneM07.CE.R3Glue

open CKLaneN1

def leaf21 (B : B3) (w : CKLaneM07.CE.R3.RWit) : Bool :=
  CKLaneN1.R3.leafOK2 B w || CKLaneN1.R3.leafOK B w

theorem leaf21_sound {B : B3} {w : CKLaneM07.CE.R3.RWit} (h : leaf21 B w = true) :
    CKLaneN1.R3.Sem B := by
  simp only [leaf21, Bool.or_eq_true] at h
  rcases h with h | h
  · exact CKLaneN1.R3.leafOK2_sound h
  · exact CKLaneN1.R3.leafOK_sound h

theorem sem_of_tree21 (R : B3) (T : PT CKLaneM07.CE.R3.RWit)
    (h : T.allLeaves (fun p w => leaf21 (R.ofPath p) w) = true) : CKLaneN1.R3.Sem R := by
  intro a z y hm
  obtain ⟨q, hq, hmq⟩ := PT.cover R T hm
  exact leaf21_sound (PT.allLeaves_sound h q hq) a z y hmq

end CKLaneM07.CE.R3Glue

end


