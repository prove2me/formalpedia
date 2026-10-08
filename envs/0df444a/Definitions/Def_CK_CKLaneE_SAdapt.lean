-- Prove2me | Definitions.Def_CK_CKLaneE_SAdapt
-- name    : CK_CKLaneE_SAdapt
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T08:19:03.497793+00:00
-- url     : https://prove2.me/theorems/019eb626-db02-4653-b72d-60b3832ff4b4
-- title:
--   Courtade–Kumar proof module `CKLaneE.SAdapt` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.SAdapt` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.SAdapt` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.SAdapt (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/SAdapt.lean)

import Definitions.Def_CK_CKLaneE_SLeaf
import Definitions.Def_CK_CKLaneG3_SCover

-- ===== source module CKLaneE.SAdapt =====
section

/-!
# Lane E: adapter to the canonical (S) module `CKLaneG3.SCover`

The lane-local `CKLaneE.S.SBox` / `sBoxL` / `InS` are field-for-field copies of `CKLaneG3.SBox` /
`sBox` / `InS`; `toG3` maps boxes, commutes with the root and the halving step, hence
`toG3 (sBoxL p) = CKLaneG3.sBox p`, and `LeafS` is `CKLaneG3.RowS`.  So every lane leaf theorem
`LeafS (sBoxL p)` yields the canonical obligation `CKLaneG3.SLeafOK (CKLaneG3.sBox p)`.
-/

set_option autoImplicit false

namespace CKLaneE.SAdapt

open CKLaneE.S

def toG3 (B : SBox) : CKLaneG3.SBox := ⟨B.x0, B.x1, B.b0, B.b1, B.t0, B.t1⟩

theorem toG3_sBoxL (p : List ℕ) : toG3 (sBoxL p) = CKLaneG3.sBox p :=
  CKLaneG3.sBox_of_commute SBox.child sRoot toG3 rfl
    (fun X d => by rcases d with _ | _ | _ | _ | _ | _ | d <;> rfl) p

theorem rowS_of_leafS {B : SBox} (h : LeafS B) : CKLaneG3.RowS (toG3 B) := by
  intro k μ hab hin hact
  exact h k μ hab hin hact

theorem sLeafOK_of_leafS (p : List ℕ) (h : LeafS (sBoxL p)) :
    CKLaneG3.SLeafOK (CKLaneG3.sBox p) := by
  rw [← toG3_sBoxL p]
  exact CKLaneG3.sLeafOK_of_rowS (rowS_of_leafS h)

/-- Family transport: a lane family over a path list gives the canonical obligations. -/
theorem family_sLeafOK (L : List (List ℕ)) (h : ∀ p ∈ L, LeafS (sBoxL p)) :
    ∀ p ∈ L, CKLaneG3.SLeafOK (CKLaneG3.sBox p) :=
  fun p hp => sLeafOK_of_leafS p (h p hp)

end CKLaneE.SAdapt

#print axioms CKLaneE.SAdapt.family_sLeafOK

end


