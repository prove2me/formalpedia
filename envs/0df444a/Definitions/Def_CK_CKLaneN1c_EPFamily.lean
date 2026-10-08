-- Prove2me | Definitions.Def_CK_CKLaneN1c_EPFamily
-- name    : CK_CKLaneN1c_EPFamily
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T20:13:12.345533+00:00
-- url     : https://prove2.me/theorems/2bd1501c-3b19-4c69-9afd-9cc6f32aea65
-- title:
--   Courtade–Kumar proof module `CKLaneN1c.EPFamily` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1c.EPFamily` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1c.EPFamily` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1c.EPFamily (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1c/EPFamily.lean)

import Definitions.Def_CK_CKLaneN1c_EPShard_S00
import Definitions.Def_CK_CKLaneN1c_EPShard_S01
import Definitions.Def_CK_CKLaneN1c_EPShard_S02
import Definitions.Def_CK_CKLaneN1c_EPShard_S03
import Definitions.Def_CK_CKLaneN1c_EPShard_S04
import Definitions.Def_CK_CKLaneN1c_EPShard_S05
import Definitions.Def_CK_CKLaneN1c_EPShard_S06
import Definitions.Def_CK_CKLaneN1c_EPShard_S07
import Definitions.Def_CK_CKLaneN1c_EPShard_S08
import Definitions.Def_CK_CKLaneN1c_EPShard_S09
import Definitions.Def_CK_CKLaneN1c_EPShard_S10
import Definitions.Def_CK_CKLaneN1c_EPShard_S11
import Definitions.Def_CK_CKLaneN1c_EPShard_S12
import Definitions.Def_CK_CKLaneN1c_EPShard_S13
import Definitions.Def_CK_CKLaneN1c_EPShard_S14
import Definitions.Def_CK_CKLaneN1c_EPShard_S15
import Definitions.Def_CK_CKLaneN1c_EPShard_S16
import Definitions.Def_CK_CKLaneN1c_LeafSem
import Definitions.Def_CK_CKLaneG1_CoverKit3

-- ===== source module CKLaneN1c.EPFamily =====
section

/-!
# Lane N1c-c: the transition `endpoint` family (1,687 archived leaves)

`epList` concatenates the 17 fleet shards (`EPShard.S00`–`S16`, archive DFS order); each shard proves
`checkEP` on all of its entries by `decide +kernel`.  `ep_walk` checks (kernel) that the entry paths
are exactly the `endpoint` (label 1) leaves of the archived tree `CKLaneG1.OppTransition.tree`, in order.
-/

set_option autoImplicit false

namespace CKLaneN1c

open GeneralCK CKLaneN1 CKLaneG1

/-- The 1,687 archived `endpoint` leaves with their witnesses, in archive (DFS) order. -/
def epList : List (List ℕ × ℚ × ℚ × ℚ) :=
    EPShard.epL00 ++
    EPShard.epL01 ++
    EPShard.epL02 ++
    EPShard.epL03 ++
    EPShard.epL04 ++
    EPShard.epL05 ++
    EPShard.epL06 ++
    EPShard.epL07 ++
    EPShard.epL08 ++
    EPShard.epL09 ++
    EPShard.epL10 ++
    EPShard.epL11 ++
    EPShard.epL12 ++
    EPShard.epL13 ++
    EPShard.epL14 ++
    EPShard.epL15 ++
    EPShard.epL16

theorem epList_ok : epList.all
    (fun e => checkEP (OppTransition.root.ofPath e.1) e.2.1 e.2.2.1 e.2.2.2) = true := by
  simp only [epList, List.all_append, EPShard.epL00_ok, EPShard.epL01_ok, EPShard.epL02_ok, EPShard.epL03_ok, EPShard.epL04_ok, EPShard.epL05_ok, EPShard.epL06_ok, EPShard.epL07_ok, EPShard.epL08_ok, EPShard.epL09_ok, EPShard.epL10_ok, EPShard.epL11_ok, EPShard.epL12_ok, EPShard.epL13_ok, EPShard.epL14_ok, EPShard.epL15_ok, EPShard.epL16_ok, Bool.and_self]

theorem epList_length : epList.length = 1687 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ep_walk : PT.walkE (fun l => l != 1) OppTransition.tree [] epList = some [] := by
  decide +kernel

/-- Every archived `endpoint` leaf satisfies the in-row statement on its whole leaf image. -/
theorem endpoint_leafSem : ∀ q ∈ OppTransition.tree.leaves, q.2 = 1 → LeafSem q.1 := by
  intro q hq hl
  have hP : ∀ e ∈ epList, LeafSem e.1 := by
    intro e he k μ _hab hsum ha hb _hb9 hd _hE _h4 _h8 hin hact
    have hok := List.all_eq_true.mp epList_ok e he
    exact checkEP_sound hok μ hsum ha hb (by linarith) hin hact
  exact PT.walkE_all ep_walk hP q hq (by simp [hl])

/-- Family theorem, label `endpoint` (code 1) of `CKLaneG1.OppTransition.tree`: for every archived
`endpoint` leaf and every law in its exact image `InExy` satisfying the `SR_Transition` hypotheses and
strict psi-activity, `gap ≤ cost`. -/
theorem endpoint_family : ∀ q ∈ OppTransition.tree.leaves, q.2 = 1 →
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
      1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
      1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
      4 * μ.meanEntropy ≤ μ.b - μ.a → μ.b - μ.a ≤ 8 * μ.meanEntropy →
      InExy (OppTransition.root.ofPath q.1) μ.a μ.b μ.meanEntropy → PsiActive μ →
      μ.gap ≤ μ.cost :=
  endpoint_leafSem

end CKLaneN1c

end


