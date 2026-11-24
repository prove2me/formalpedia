-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Smooth
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Smooth
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:52:18.93166+00:00
-- url     : https://prove2.me/theorems/add34828-5db2-4de6-ad51-fd27e9f0b30a
-- title:
--   Smooth
-- statement:
--   Definitions and structural lemmas for Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section smoothAt
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
end smoothAt
section slice
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}
end slice
end PI.UnitaryGroupMassFormula.UsCost


