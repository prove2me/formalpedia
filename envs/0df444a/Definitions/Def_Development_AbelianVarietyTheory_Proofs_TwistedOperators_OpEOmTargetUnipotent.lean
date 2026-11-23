-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:54.184599+00:00
-- url     : https://prove2.me/theorems/16bf0b04-48e8-49d6-9b3c-fb53a908d3be
-- title:
--   Op EOm Target Unipotent
-- statement:
--   Definitions and structural lemmas for Op EOm Target Unipotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OpEOmTargetUnipotent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
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
namespace GlobalTheory.RootEx.TargetUnip
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
variable {n' : Type*} [Fintype n'] [DecidableEq n']
open Classical in

def linPart (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) :
    Matrix {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
  Matrix.of fun a b => if a.1.2 = b.1.2 then h a.1.1 b.1.1 else 0
end GlobalTheory.RootEx.TargetUnip


