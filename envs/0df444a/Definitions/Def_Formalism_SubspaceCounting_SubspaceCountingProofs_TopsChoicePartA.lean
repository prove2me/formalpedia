-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
-- name    : Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:13:08.539811+00:00
-- url     : https://prove2.me/theorems/cbf59533-de10-49e0-8ee6-0cf81914d31b
-- title:
--   Tops Choice Part A
-- statement:
--   Definitions and structural lemmas for Tops Choice Part A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
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
namespace Formalism.G0
namespace TopsConditionalProbabilityWindows
open Classical in

def P (U : Finset ℕ) (δ : ℝ) (A : Finset ℕ → Prop) : ℝ :=
  ∑ t ∈ U.powerset, if A t then δ ^ t.card * (1 - δ) ^ (U.card - t.card) else 0
end TopsConditionalProbabilityWindows
end Formalism.G0


