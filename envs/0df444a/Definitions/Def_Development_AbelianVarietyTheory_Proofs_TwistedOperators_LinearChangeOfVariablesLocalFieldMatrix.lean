-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:12.137853+00:00
-- url     : https://prove2.me/theorems/2bb2a56c-d608-4c7b-83f3-a814cd0c1579
-- title:
--   Linear Change Of Variables Local Field Matrix
-- statement:
--   Definitions and structural lemmas for Linear Change Of Variables Local Field Matrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LinearChangeOfVariablesLocalFieldMatrix.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker
namespace GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  (ν : Measure k) [ν.IsAddHaarMeasure]
end GlobalTheory.SplitWeil


