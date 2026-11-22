-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntLam
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntLam
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:46:48.561691+00:00
-- url     : https://prove2.me/theorems/9652318d-32ff-4f5e-b910-c2e403d38460
-- title:
--   Cnt Lam
-- statement:
--   Definitions and structural lemmas for Cnt Lam, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CntLam.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)
def qk_v {n : ℕ} (mu : Fin n → ℤ) : Fin n → ℝ := fun i => (i.1 : ℝ) - (mu i : ℝ)
def vandermondeDenominator (n : ℕ) : ℝ := ∏ j ∈ range n, ∏ i ∈ range j, ((j : ℝ) - (i : ℝ))
def qk_add {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) : Fin n → ℤ := fun a => if a ∈ s then mu a + 1 else mu a
end Formalism.InvariantFactorPaths.ColumnFamilies


