-- Prove2me | Definitions.Def_CK_CKLaneM07_G3Adapter
-- name    : CK_CKLaneM07_G3Adapter
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T07:13:24.552991+00:00
-- url     : https://prove2.me/theorems/80dbd953-f050-4cb3-8f33-fdfe4222fb26
-- title:
--   Courtade–Kumar proof module `CKLaneM07.G3Adapter` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.G3Adapter` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.G3Adapter` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.G3Adapter (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/G3Adapter.lean)

import Definitions.Def_CK_CKLaneM07_Checker
import Definitions.Def_CK_CKLaneG3_SCover

-- ===== source module CKLaneM07.G3Adapter =====
section

/-!
# Lane M07 → canonical (S) cover adapter (`CKLaneG3.SCover`, BRIEF §7)

`CKLaneM07.SBox ⟨x1,x2,b1,b2,t1,t2⟩` is the canonical `CKLaneG3.SBox ⟨x0,x1,b0,b1,t0,t1⟩` with renamed
fields; `toG` is the field-for-field map.  It commutes with the root and the halving step, hence
`toG (ssBox p) = CKLaneG3.sBox p` (`CKLaneG3.sBox_of_commute`); `CKLaneG3.InS (toG B)` is definitionally
`InSBox B`, and `SemSBox B` is literally `CKLaneG3.OwnerS (toG B)`, so `CKLaneG3.sLeafOK_of_ownerS` applies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM07

/-- Field-for-field map to the canonical box. -/
def toG (B : SBox) : CKLaneG3.SBox := ⟨B.x1, B.x2, B.b1, B.b2, B.t1, B.t2⟩

theorem toG_root : toG ssRoot = CKLaneG3.sRoot := rfl

theorem toG_step (B : SBox) (d : ℕ) : toG (ssStep B d) = CKLaneG3.sStep (toG B) d := by
  rcases d with _ | _ | _ | _ | _ | _ | d
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · have e : d + 1 + 1 + 1 + 1 + 1 + 1 = d + 6 := by ring
    simp only [e, ssStep, CKLaneG3.sStep]

theorem toG_ssBox (p : List ℕ) : toG (ssBox p) = CKLaneG3.sBox p :=
  CKLaneG3.sBox_of_commute ssStep ssRoot toG toG_root toG_step p

theorem inS_toG_iff (B : SBox) (a b E : ℝ) : CKLaneG3.InS (toG B) a b E ↔ InSBox B a b E := Iff.rfl

theorem ownerS_of_semSBox {B : SBox} (h : SemSBox B) : CKLaneG3.OwnerS (toG B) :=
  fun k μ hab hin hact => h k μ hab hin hact

/-- Per-leaf adapter: the M07 semantic statement on `ssBox p` gives the `SS_Compact` obligation on the
canonical box `CKLaneG3.sBox p`. -/
theorem sLeafOK_of_semSBox {p : List ℕ} (h : SemSBox (ssBox p)) : CKLaneG3.SLeafOK (CKLaneG3.sBox p) := by
  rw [← toG_ssBox]
  exact CKLaneG3.sLeafOK_of_ownerS (ownerS_of_semSBox h)

/-- Checker form: a checked witness for path `p` proves the canonical per-leaf obligation. -/
theorem sLeafOK_of_checkLeaf {p : List ℕ} {w : Wit} (h : checkLeaf p w = true) :
    CKLaneG3.SLeafOK (CKLaneG3.sBox p) :=
  sLeafOK_of_semSBox (checkLeaf_sound h)

end CKLaneM07

#check @CKLaneM07.toG_ssBox
#check @CKLaneM07.sLeafOK_of_semSBox
#check @CKLaneM07.sLeafOK_of_checkLeaf
#print axioms CKLaneM07.toG_ssBox
#print axioms CKLaneM07.sLeafOK_of_semSBox
#print axioms CKLaneM07.sLeafOK_of_checkLeaf

end


