-- Prove2me | Definitions.Def_CK_CKLaneM08_Adapter
-- name    : CK_CKLaneM08_Adapter
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T03:56:02.456064+00:00
-- url     : https://prove2.me/theorems/1949658d-c3fb-41f7-9460-333da966634c
-- title:
--   Courtade–Kumar proof module `CKLaneM08.Adapter` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM08.Adapter` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM08.Adapter` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM08.Adapter (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM08/Adapter.lean)

import Definitions.Def_CK_CKLaneM08_Checker
import Definitions.Def_CK_CKLaneG3_SCover

-- ===== source module CKLaneM08.Adapter =====
section

/-!
# Lane M08 → canonical (S) cover adapter (`CKLaneG3.SCover`)

`CKLaneM08.Box` / `root` / `step` / `boxOfPath` / `InBox` are field-for-field the canonical
`CKLaneG3.SBox` / `sRoot` / `sStep` / `sBox` / `InS`; `Sem` is `CKLaneG3.SemS`.
-/

set_option autoImplicit false

namespace CKLaneM08

/-- The identity-on-fields map to the canonical (S) box type. -/
def toS (B : Box) : CKLaneG3.SBox := ⟨B.x0, B.x1, B.b0, B.b1, B.t0, B.t1⟩

theorem toS_root : toS root = CKLaneG3.sRoot := rfl

theorem toS_step (B : Box) (d : ℕ) : toS (step B d) = CKLaneG3.sStep (toS B) d := by
  rcases d with _ | _ | _ | _ | _ | _ | d <;> rfl

theorem toS_boxOfPath (p : List ℕ) : toS (boxOfPath p) = CKLaneG3.sBox p :=
  CKLaneG3.sBox_of_commute step root toS toS_root toS_step p

theorem semS_of_sem {B : Box} (h : Sem B) : CKLaneG3.SemS (toS B) :=
  fun k μ hin => h k μ hin

theorem sLeafOK_of_sem {B : Box} (h : Sem B) : CKLaneG3.SLeafOK (toS B) :=
  CKLaneG3.sLeafOK_of_semS (semS_of_sem h)

/-- Canonical-form leaf theorem for an archived path. -/
theorem sLeafOK_of_path {p : List ℕ} (h : Sem (boxOfPath p)) : CKLaneG3.SLeafOK (CKLaneG3.sBox p) := by
  rw [← toS_boxOfPath p]
  exact sLeafOK_of_sem h

end CKLaneM08

#check @CKLaneM08.toS_boxOfPath
#check @CKLaneM08.sLeafOK_of_path
#print axioms CKLaneM08.toS_boxOfPath
#print axioms CKLaneM08.sLeafOK_of_path

end


