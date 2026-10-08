-- Prove2me | Definitions.Def_CK_CKLaneA2_SlotDiagonal5_q02
-- name    : CK_CKLaneA2_SlotDiagonal5_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T08:26:08.723875+00:00
-- url     : https://prove2.me/theorems/e2c22e0e-802d-4ab7-9b17-46ac5e915118
-- title:
--   Courtade–Kumar proof module `CKLaneA2.SlotDiagonal5 (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA2.SlotDiagonal5 (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA2.SlotDiagonal5 (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA2.SlotDiagonal5 (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA2/SlotDiagonal5 (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneA2_SlotDiagonal5_q01

namespace CKLaneA2.Diag5
open CKLaneA.Cell CKLaneA2
def n383 : Tree := .sr (1 / 20 : ℚ) n384 n437
theorem n383_ok : treeOK (59 / 160 : ℚ) (37 / 100 : ℚ) (0 : ℚ) (1 / 10 : ℚ) n383 = true :=
  treeOK_sr (by decide +kernel) n384_ok n437_ok
def n313 : Tree := .su (59 / 160 : ℚ) n314 n383
theorem n313_ok : treeOK (147 / 400 : ℚ) (37 / 100 : ℚ) (0 : ℚ) (1 / 10 : ℚ) n313 = true :=
  treeOK_su (by decide +kernel) n314_ok n383_ok
def n193 : Tree := .su (147 / 400 : ℚ) n194 n313
theorem n193_ok : treeOK (73 / 200 : ℚ) (37 / 100 : ℚ) (0 : ℚ) (1 / 10 : ℚ) n193 = true :=
  treeOK_su (by decide +kernel) n194_ok n313_ok
def n1 : Tree := .su (73 / 200 : ℚ) n2 n193
theorem n1_ok : treeOK (9 / 25 : ℚ) (37 / 100 : ℚ) (0 : ℚ) (1 / 10 : ℚ) n1 = true :=
  treeOK_su (by decide +kernel) n2_ok n193_ok

theorem slotTree_ok : treeOK (9 / 25 : ℚ) (37 / 100 : ℚ) (0 : ℚ) (1 / 10 : ℚ) n1 = true := n1_ok

end CKLaneA2.Diag5

namespace CKLaneA2.Slots
open GeneralCK GeneralCK.Correction GeneralCK.Correction.Complement CKLaneA.Cell

/-- strict owner on `[9/25, 37/100] × (0, 1/10]` -/
theorem diagonal5_actual : ∀ ⦃u rho : ℝ⦄, u ∈ Set.Icc (9 / 25 : ℝ) (37 / 100) →
    rho ∈ Set.Ioc (0 : ℝ) (1 / 10) → ActualRatioMinorsPositive u rho := by
  intro u rho hu hr
  exact actual_of_tree Diag5.slotTree_ok (by push_cast; linarith [hu.1])
    (by push_cast; linarith [hu.2]) (by push_cast; linarith [hr.1]) (by push_cast; linarith [hr.2])
    (by linarith [hu.1]) (by linarith [hu.2]) hr.1 (by linarith [hr.2])

end CKLaneA2.Slots


