-- Prove2me | Definitions.Def_CK_CKLaneM03_G3Bridge
-- name    : CK_CKLaneM03_G3Bridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T08:21:09.591624+00:00
-- url     : https://prove2.me/theorems/0deadd44-da7b-4294-b5de-fd1f49e34fc0
-- title:
--   Courtade–Kumar proof module `CKLaneM03.G3Bridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.G3Bridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.G3Bridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.G3Bridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/G3Bridge.lean)

import Definitions.Def_CK_CKLaneM03_Canary
import Definitions.Def_CK_CKLaneG3_SCover

-- ===== source module CKLaneM03.G3Bridge =====
section

/-!
# Lane M03 → canonical (S) cover adapter (Lane G3 `CKLaneG3.SCover`)

`toG3` is the field-for-field map `SBox → CKLaneG3.SBox` (xlo xhi blo bhi tlo thi ↦ x0 x1 b0 b1 t0 t1);
it commutes with the root and the halving step, so `toG3 (ssBox p) = CKLaneG3.sBox p`
(`CKLaneG3.sBox_of_commute`).  `InSBox X = CKLaneG3.InS (toG3 X)` and `Sem X = CKLaneG3.SemS (toG3 X)`
definitionally; hence every M03 leaf theorem `Sem (ssBox p)` gives `CKLaneG3.SLeafOK (CKLaneG3.sBox p)`
through `CKLaneG3.sLeafOK_of_semS`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM03

open GeneralCK

/-- Field-for-field map to the canonical (S) box. -/
def toG3 (X : SBox) : CKLaneG3.SBox := ⟨X.xlo, X.xhi, X.blo, X.bhi, X.tlo, X.thi⟩

theorem toG3_root : toG3 ssRoot = CKLaneG3.sRoot := rfl

theorem toG3_step (X : SBox) (d : ℕ) : toG3 (ssStep X d) = CKLaneG3.sStep (toG3 X) d := by
  rcases d with _ | _ | _ | _ | _ | _ | d
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [ssStep, CKLaneG3.sStep]

theorem toG3_ssBox (p : List ℕ) : toG3 (ssBox p) = CKLaneG3.sBox p :=
  CKLaneG3.sBox_of_commute ssStep ssRoot toG3 toG3_root toG3_step p

theorem inS_toG3 (X : SBox) (a b E : ℝ) : CKLaneG3.InS (toG3 X) a b E ↔ InSBox X a b E := Iff.rfl

theorem semS_toG3 {X : SBox} (h : Sem X) : CKLaneG3.SemS (toG3 X) := h

/-- Every M03 leaf/subtree theorem discharges the canonical `SS_Compact` per-leaf obligation. -/
theorem sLeafOK_of_sem {p : List ℕ} (h : Sem (ssBox p)) : CKLaneG3.SLeafOK (CKLaneG3.sBox p) := by
  rw [← toG3_ssBox]
  exact CKLaneG3.sLeafOK_of_semS (semS_toG3 h)

/-- Canary in canonical form (archived hardest endpoint leaf). -/
theorem canary_sLeafOK :
    CKLaneG3.SLeafOK (CKLaneG3.sBox [5,0,2,0,2,0,3,0,1,4,2,0,5,2,0,4,3,0,4,2,0,4,3,1]) :=
  sLeafOK_of_sem Canary.ep_502020301420520430420431

end CKLaneM03

end


