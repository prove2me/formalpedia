-- Prove2me | Definitions.Def_CK_CKLaneM05_SAdapter
-- name    : CK_CKLaneM05_SAdapter
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T17:58:04.017978+00:00
-- url     : https://prove2.me/theorems/a5a6ffb8-cfa8-4114-a1d8-4be257452789
-- title:
--   Courtade–Kumar proof module `CKLaneM05.SAdapter` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM05.SAdapter` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM05.SAdapter` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM05.SAdapter (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM05/SAdapter.lean)

import Definitions.Def_CK_CKLaneM05_Checker
import Definitions.Def_CK_CKLaneG3_SCover

-- ===== source module CKLaneM05.SAdapter =====
section

/-!
# Lane M05: adapter to the canonical (S) cover `CKLaneG3.SCover` (BRIEF §7, route row `SS_Compact`)

`toS` maps the lane box field for field onto `CKLaneG3.SBox`; it commutes with the root and the
halving step, so `toS (ssBox p) = CKLaneG3.sBox p` (`CKLaneG3.sBox_of_commute`). The lane membership
`InSSBox` is literally `CKLaneG3.InS` and `ParentSem` is literally `CKLaneG3.ParentS`, hence parent
dominance on an archived leaf gives the canonical per-leaf obligation `CKLaneG3.SLeafOK`
(`CKLaneG3.sLeafOK_of_parentS`: the strict psi-activity premise is contradicted).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM05

/-- Field-for-field map to the canonical (S) box. -/
def toS (B : SSBox) : CKLaneG3.SBox := ⟨B.x0, B.x1, B.b0, B.b1, B.t0, B.t1⟩

theorem toS_ssRoot : toS ssRoot = CKLaneG3.sRoot := rfl

theorem toS_ssStep (B : SSBox) (d : ℕ) : toS (ssStep B d) = CKLaneG3.sStep (toS B) d := by
  rcases d with _ | _ | _ | _ | _ | _ | d <;> rfl

/-- The lane box recursion is the canonical one. -/
theorem toS_ssBox (p : List ℕ) : toS (ssBox p) = CKLaneG3.sBox p :=
  CKLaneG3.sBox_of_commute ssStep ssRoot toS toS_ssRoot toS_ssStep p

/-- The lane membership is literally the canonical `InS`. -/
theorem inS_toS_iff (B : SSBox) (a b E : ℝ) :
    CKLaneG3.InS (toS B) a b E ↔ InSSBox B a b E := Iff.rfl

/-- The lane parent-dominance statement is literally the canonical `ParentS`. -/
theorem parentS_toS {B : SSBox} (h : ParentSem B) : CKLaneG3.ParentS (toS B) :=
  fun k μ hin => h k μ hin

/-- Adapter: parent dominance on the lane box of an archived path gives the canonical
`SS_Compact` per-leaf obligation on `CKLaneG3.sBox p`. -/
theorem sLeafOK_of_parentSem {p : List ℕ} (h : ParentSem (ssBox p)) :
    CKLaneG3.SLeafOK (CKLaneG3.sBox p) := by
  rw [← toS_ssBox]
  exact CKLaneG3.sLeafOK_of_parentS (parentS_toS h)

end CKLaneM05

#check @CKLaneM05.toS_ssBox
#check @CKLaneM05.sLeafOK_of_parentSem
#print axioms CKLaneM05.toS_ssBox
#print axioms CKLaneM05.sLeafOK_of_parentSem

end


