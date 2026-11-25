-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFlagGrassPush
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFlagGrassPush
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T08:41:28.567955+00:00
-- url     : https://prove2.me/theorems/ac6f694f-9991-58e3-b66e-cb415a4e5d43
-- title:
--   Statements Flag Grass Push
-- statement:
--   Definitions and structural lemmas for Statements Flag Grass Push, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/StatementsFlagGrassPush.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FlagIndices_InstFintypeFlIdx
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_PermFinTwoUniv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FA_line_154de880dd8a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Jint_line_8a43ca352fca

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
noncomputable section
def FlagGrassPush.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N j : ℕ) (cf : ℚ),
    IsIntersectionSystem II → 2 ≤ N → 1 ≤ j → j ≤ N - 1 →
    -hFl Ψ N II (FA Ψ N j cf) *
        geomDeg (grassIdeal (Fintype.card Ψ) j (N - j))
          (GroundTheory.Heights₂.Heights.fsMulti (plBlocks (Fintype.card Ψ) j (N - j))) (dimN Ψ N j) =
      (Jint Ψ N j cf : ℝ) *
        II (Fin (Fintype.card Ψ)) (plBlocks (Fintype.card Ψ) j (N - j)) (grassIdeal (Fintype.card Ψ) j (N - j))
          (dimN Ψ N j + 1) (fun _ => GroundTheory.Heights₂.Heights.fsMulti (plBlocks (Fintype.card Ψ) j (N - j)))
example (cf : ℚ) : Nonempty Unit ∧ 2 ≤ 2 ∧ 1 ≤ 1 ∧ 1 ≤ 2 - 1 ∧ dimN Unit 2 1 = 1 ∧
    FA Unit 2 1 cf = C cf * X ((), 1) ^ 2 ∧ Jint Unit 2 1 cf = -cf ∧ Fintype.card (PlIdx 1 (2 - 1)) = 2 := by
  refine ⟨⟨()⟩, le_rfl, le_rfl, le_rfl, rfl, FA_line cf, Jint_line cf, ?_⟩
  decide
end
end GroundTheory.Heights₂.Heights.LowerBoundFree


