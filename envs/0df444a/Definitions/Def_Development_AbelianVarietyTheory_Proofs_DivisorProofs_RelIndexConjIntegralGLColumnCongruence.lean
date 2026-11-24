-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruence
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:50.352829+00:00
-- url     : https://prove2.me/theorems/2f45a38a-c8a6-4668-899c-ece27428c179
-- title:
--   Rel Index Conj Integral GLColumn Congruence
-- statement:
--   Definitions and structural lemmas for Rel Index Conj Integral GLColumn Congruence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLColumnCongruence.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.IndexCol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]
end GlobalTheory.IndexCol


