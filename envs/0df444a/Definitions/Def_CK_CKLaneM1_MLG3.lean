-- Prove2me | Definitions.Def_CK_CKLaneM1_MLG3
-- name    : CK_CKLaneM1_MLG3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T13:06:28.397632+00:00
-- url     : https://prove2.me/theorems/44187399-1e03-46c1-86ab-05ea9af04c4d
-- title:
--   Courtade–Kumar proof module `CKLaneM1.MLG3` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.MLG3` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.MLG3` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.MLG3 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/MLG3.lean)

import Definitions.Def_CK_CKLaneM1_MLChecker
import Definitions.Def_CK_CKLaneG3_SCover

-- ===== source module CKLaneM1.MLG3 =====
section

/-!
# Lane M1 → canonical (S) cover `CKLaneG3.SCover` (BRIEF §7)

`SSBox`/`ssRoot`/`ssStep`/`ssBox`/`InSS` are field-for-field the canonical `SBox`/`sRoot`/`sStep`/`sBox`/`InS`.
`toSBox_ssBox` transports the box recursion (`CKLaneG3.sBox_of_commute`); `SemSS` is definitionally
`CKLaneG3.OwnerStrictS`, closed at `a = b` by `CKLaneG3.sLeafOK_of_ownerStrictS`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM1.ML

open GeneralCK

/-- Field-for-field map to the canonical (S) box. -/
def toSBox (B : SSBox) : CKLaneG3.SBox := ⟨B.x0, B.x1, B.b0, B.b1, B.t0, B.t1⟩

theorem toSBox_step (X : SSBox) (d : ℕ) : toSBox (ssStep X d) = CKLaneG3.sStep (toSBox X) d := by
  rcases d with _ | _ | _ | _ | _ | _ | d <;> rfl

theorem toSBox_ssBox (p : List ℕ) : toSBox (ssBox p) = CKLaneG3.sBox p :=
  CKLaneG3.sBox_of_commute ssStep ssRoot toSBox rfl toSBox_step p

theorem inS_toSBox (B : SSBox) (a b E : ℝ) : CKLaneG3.InS (toSBox B) a b E ↔ InSS B a b E :=
  Iff.rfl

theorem ownerStrictS_of_semSS {B : SSBox} (h : SemSS B) : CKLaneG3.OwnerStrictS (toSBox B) := h

theorem sLeafOK_of_semSS {p : List ℕ} (h : SemSS (ssBox p)) : CKLaneG3.SLeafOK (CKLaneG3.sBox p) := by
  rw [← toSBox_ssBox]
  exact CKLaneG3.sLeafOK_of_ownerStrictS (ownerStrictS_of_semSS h)

/-- Checker soundness in the coordinator's final (S) form. -/
theorem checkLeaf_sLeafOK {p : List ℕ} {w : LeafCert} (h : checkLeaf p w = true) :
    CKLaneG3.SLeafOK (CKLaneG3.sBox p) :=
  sLeafOK_of_semSS (checkLeaf_sound h)

end CKLaneM1.ML

end


