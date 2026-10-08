-- Prove2me | Definitions.Def_CK_CKLaneN1c_NMFamily
-- name    : CK_CKLaneN1c_NMFamily
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T07:19:10.508987+00:00
-- url     : https://prove2.me/theorems/4a73f545-110d-4a8b-81dd-fc0411bc2515
-- title:
--   Courtade–Kumar proof module `CKLaneN1c.NMFamily` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1c.NMFamily` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1c.NMFamily` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1c.NMFamily (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1c/NMFamily.lean)

import Definitions.Def_CK_CKLaneN1c_NMShard_S00
import Definitions.Def_CK_CKLaneN1c_NMShard_S01
import Definitions.Def_CK_CKLaneN1c_NMShard_S02
import Definitions.Def_CK_CKLaneN1c_NMShard_S03
import Definitions.Def_CK_CKLaneN1c_NMShard_S04
import Definitions.Def_CK_CKLaneN1c_NMShard_S05
import Definitions.Def_CK_CKLaneN1c_LeafSem
import Definitions.Def_CK_CKLaneG1_CoverKit3

-- ===== source module CKLaneN1c.NMFamily =====
section

/-!
# Lane N1c-c: the transition `normalized_phi_children` and `prior_collar` families

`nmList` concatenates the fleet shards `NMShard.S00`–`S05` (512 entries: the 508 archived
`normalized_phi_children` leaves and the 4 archived `prior_collar` leaves, archive DFS order); each shard
proves `checkN` on all of its entries by `decide +kernel`.  `nm_walk` checks (kernel) that the entry
paths are exactly the label-2 and label-3 leaves of `CKLaneG1.OppTransition.tree`, in order.

The 4 `prior_collar` leaves (archived delegate: the `q ≤ 2E, d ≥ 6E` collar of SHARPER_COLLARS) are
closed here directly by the transition component's own normalized comparison (10) on the exact archived
leaf boxes (exact margins ≥ 0.12); no collar theorem is assumed.
-/

set_option autoImplicit false

namespace CKLaneN1c

open GeneralCK CKLaneN1 CKLaneG1

/-- The archived label-2/3 leaves with their witnesses `(v_p, v_m, v_l)`, archive (DFS) order. -/
def nmList : List (List ℕ × ℚ × ℚ × ℚ) :=
    NMShard.nmL00 ++
    NMShard.nmL01 ++
    NMShard.nmL02 ++
    NMShard.nmL03 ++
    NMShard.nmL04 ++
    NMShard.nmL05

theorem nmList_ok : nmList.all
    (fun e => checkN (OppTransition.root.ofPath e.1) e.2.1 e.2.2.1 e.2.2.2) = true := by
  simp only [nmList, List.all_append, NMShard.nmL00_ok, NMShard.nmL01_ok, NMShard.nmL02_ok, NMShard.nmL03_ok, NMShard.nmL04_ok, NMShard.nmL05_ok, Bool.and_self]

theorem nmList_length : nmList.length = 512 := by decide +kernel

set_option maxRecDepth 100000 in
theorem nm_walk : PT.walkE (fun l => !(l == 2 || l == 3)) OppTransition.tree [] nmList = some [] := by
  decide +kernel

theorem nm_leafSem : ∀ q ∈ OppTransition.tree.leaves, (q.2 = 2 ∨ q.2 = 3) → LeafSem q.1 := by
  intro q hq hl
  have hP : ∀ e ∈ nmList, LeafSem e.1 := by
    intro e he k μ _hab hsum ha hb _hb9 hd hE h4 _h8 hin hact
    have hok := List.all_eq_true.mp nmList_ok e he
    exact checkN_sound hok μ hsum ha hb hd hE h4 hin hact
  apply PT.walkE_all nm_walk hP q hq
  rcases hl with h | h <;> simp [h]

/-- Family theorem, label `normalized_phi_children` (code 2) of `CKLaneG1.OppTransition.tree`. -/
theorem normalized_family : ∀ q ∈ OppTransition.tree.leaves, q.2 = 2 →
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
      1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
      1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
      4 * μ.meanEntropy ≤ μ.b - μ.a → μ.b - μ.a ≤ 8 * μ.meanEntropy →
      InExy (OppTransition.root.ofPath q.1) μ.a μ.b μ.meanEntropy → PsiActive μ →
      μ.gap ≤ μ.cost :=
  fun q hq hl => nm_leafSem q hq (Or.inl hl)

/-- Family theorem, label `prior_collar` (code 3) of `CKLaneG1.OppTransition.tree`. -/
theorem collar_family : ∀ q ∈ OppTransition.tree.leaves, q.2 = 3 →
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
      1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
      1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
      4 * μ.meanEntropy ≤ μ.b - μ.a → μ.b - μ.a ≤ 8 * μ.meanEntropy →
      InExy (OppTransition.root.ofPath q.1) μ.a μ.b μ.meanEntropy → PsiActive μ →
      μ.gap ≤ μ.cost :=
  fun q hq hl => nm_leafSem q hq (Or.inr hl)

end CKLaneN1c

end


