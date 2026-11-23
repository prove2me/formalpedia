-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:50.842014+00:00
-- url     : https://prove2.me/theorems/3b57e348-94ec-4129-b1f2-bd6e1cbe4411
-- title:
--   Second Countable Local
-- statement:
--   Definitions and structural lemmas for Second Countable Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SecondCountableLocal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
namespace GlobalTheory.RootExSource
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ}
def linPart (n : Type) [DecidableEq n] (p : ℕ) (g : GL (n' ⊕ Fin (c + 1)) k) :
    Matrix {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
  Matrix.of fun a b => if b.1.1 = a.1.1 then g.val b.1.2 a.1.2 else 0
end GlobalTheory.RootExSource


