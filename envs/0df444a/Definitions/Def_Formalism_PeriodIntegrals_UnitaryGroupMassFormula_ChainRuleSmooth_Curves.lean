-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:48.651485+00:00
-- url     : https://prove2.me/theorems/b33f55c7-5820-41a3-94f9-92cc2ad24509
-- title:
--   Curves
-- statement:
--   Definitions and structural lemmas for Curves, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate Nat ContDiff
noncomputable section
namespace CCRuleCW
open Formalism.FourierDecayAlt
section sup
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
def curve : Bool × B.Mat k r → B.Mat k r → ℝ → B.Mat k r
  | (true, X), g, t => NormedSpace.exp (-((t : ℂ) • X)) * g
  | (false, X), g, t => g * NormedSpace.exp ((t : ℂ) • X)
def dir : Bool × B.Mat k r → B.Mat k r → B.Mat k r
  | (true, X), g => -(X * g)
  | (false, X), g => g * X
def act {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Bool × B.Mat k r → (B.Mat k r → E) → B.Mat k r → E
  | (true, X), f => B.LdV X f
  | (false, X), f => Formalism.REAL.RdV X f
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end sup
end CCRuleCW


