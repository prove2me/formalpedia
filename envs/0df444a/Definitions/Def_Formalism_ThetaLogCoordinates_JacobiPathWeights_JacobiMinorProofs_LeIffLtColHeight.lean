-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:27.704563+00:00
-- url     : https://prove2.me/theorems/44fb9c6c-8d58-4cb8-a8bc-269386a2e2d3
-- title:
--   Le Iff Lt Col Height
-- statement:
--   Definitions and structural lemmas for Le Iff Lt Col Height, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LeIffLtColHeight.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace Paths
end Paths
open Paths
namespace Paths
end Paths
namespace Paths
def chg {n : ℕ} (μ : ℕ → Fin n → ℤ) (c : ℤ) (N : ℕ) (i : ℕ) : Prop :=
  colHeight (μ (i + 1)) c ≠ colHeight (μ i) c ∨ N ≤ i
instance {n : ℕ} (μ : ℕ → Fin n → ℤ) (c : ℤ) (N : ℕ) : DecidablePred (chg μ c N) := fun i => by
  unfold chg; infer_instance
end Paths
namespace Paths
end Paths
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


