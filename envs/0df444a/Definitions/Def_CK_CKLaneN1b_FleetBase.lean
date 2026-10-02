-- Prove2me | Definitions.Def_CK_CKLaneN1b_FleetBase
-- name    : CK_CKLaneN1b_FleetBase
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:10:04.995445+00:00
-- url     : https://prove2.me/theorems/a7b80132-a2eb-48f1-a60b-8102a871e3d8
-- title:
--   Courtade–Kumar proof module `CKLaneN1b.FleetBase` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1b.FleetBase` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1b.FleetBase` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1b.FleetBase (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1b/FleetBase.lean)

import Definitions.Def_CK_CKLaneN1b_Cert
import Definitions.Def_CK_CKLaneN1b_Tree

-- ===== source module CKLaneN1b.FleetBase =====
section

/-!
# Lane N1b: batch soundness over `(path, certificate)` lists

`checkAll_sound`: if every certificate of a list checks on the exact archived box of its path,
then `Sem` holds on every such box.  No other hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN1b

theorem checkAll_sound (L : List (List ℕ × Cert))
    (h : (L.all fun x => checkCert (boxOf x.1) x.2) = true) : ∀ x ∈ L, Sem (boxOf x.1) := by
  intro x hx
  rw [List.all_eq_true] at h
  exact checkCert_sound _ _ (h x hx)

end CKLaneN1b

end


