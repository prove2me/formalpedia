-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_GramStep
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_GramStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:19.006259+00:00
-- url     : https://prove2.me/theorems/ba6f1eba-c6c8-4a8c-b193-3ba359305e39
-- title:
--   Gram Step
-- statement:
--   Definitions and structural lemmas for Gram Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/GramStep.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
namespace PI.UD
def SVDStep : Prop :=
  ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), g.det ≠ 0 →
    ∃ (w v : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ),
      wᴴ * w = 1 ∧ vᴴ * v = 1 ∧ g = w * diagonal d * v
def GramStep : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), G.PosDef →
    ∃ C : Matrix (Fin n) (Fin n) ℂ, Cᴴ * C = G ∧ C.det ≠ 0
end PI.UD


