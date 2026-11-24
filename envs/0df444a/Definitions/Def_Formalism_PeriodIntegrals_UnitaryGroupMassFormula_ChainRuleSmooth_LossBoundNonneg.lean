-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:12:36.688545+00:00
-- url     : https://prove2.me/theorems/0b125c5d-97d6-4f04-a642-97f891c18653
-- title:
--   Loss Bound Nonneg
-- statement:
--   Definitions and structural lemmas for Loss Bound Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
namespace CCRuleCW
open Formalism.FourierDecayAlt
def splits {α : Type*} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => (splits xs).map (fun p => (x :: p.1, p.2)) ++ (splits xs).map (fun p => (p.1, x :: p.2))
section sup
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def apO (ops : List (Bool × B.Mat k r)) (f : B.Mat k r → E) : B.Mat k r → E :=
  ops.foldl (fun f o => act o f) f
def LieW (ops : List (Bool × B.Mat k r)) : Prop := ∀ o ∈ ops, B.inLie k r o.2
def opsW (u v : List (B.Mat k r)) : List (Bool × B.Mat k r) :=
  v.reverse.map (fun X => (false, X)) ++ u.reverse.map (fun X => (true, X))
def Good (D : ℕ) (Q : B.Mat k r → ℂ) : Prop :=
  ContDiff ℝ ∞ Q ∧ ∀ ops : List (Bool × B.Mat k r), LieW ops →
    ∃ C, ∀ g ∈ B.GV k r, ‖apO ops Q g‖ ≤ C * B.gN g ^ D
end sup
end CCRuleCW


