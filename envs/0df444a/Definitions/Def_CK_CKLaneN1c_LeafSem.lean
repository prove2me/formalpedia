-- Prove2me | Definitions.Def_CK_CKLaneN1c_LeafSem
-- name    : CK_CKLaneN1c_LeafSem
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T13:12:17.782602+00:00
-- url     : https://prove2.me/theorems/83573068-363d-4e3e-81d3-21b067e13915
-- title:
--   Courtade–Kumar proof module `CKLaneN1c.LeafSem` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1c.LeafSem` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1c.LeafSem` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1c.LeafSem (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1c/LeafSem.lean)

import Definitions.Def_CK_CKLaneN1_SubRows
import Definitions.Def_CK_CKLaneG1_OppTransition

-- ===== source module CKLaneN1c.LeafSem =====
section

/-!
# Lane N1c-c: the in-row leaf statement of the transition cover

`LeafSem p`: every law satisfying the hypotheses of `CKLaneN1.SR_Transition` (canonical, central
opposite side, `1/50 ≤ d`, `E ≤ 11/200`, `4E ≤ d ≤ 8E`), lying in the exact image `CKLaneG1.InExy` of the
archived leaf box `CKLaneG1.OppTransition.root.ofPath p`, with strict psi-activity, has `gap ≤ cost`.
-/

set_option autoImplicit false

namespace CKLaneN1c

open GeneralCK CKLaneN1 CKLaneG1

/-- In-row statement on the image of the archived leaf with path `p`. -/
def LeafSem (p : List ℕ) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
    4 * μ.meanEntropy ≤ μ.b - μ.a → μ.b - μ.a ≤ 8 * μ.meanEntropy →
    InExy (OppTransition.root.ofPath p) μ.a μ.b μ.meanEntropy → PsiActive μ →
    μ.gap ≤ μ.cost

end CKLaneN1c

end


