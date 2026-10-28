-- Prove2me | Definitions.Def_OAIQ035K058
-- name    : OAIQ035K058
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:11:45.425067+00:00
-- url     : https://prove2.me/theorems/4f557cc7-768e-4119-b4f7-cd3a30429fb6
-- title:
--   Definitions bundle OAIQ035K058 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 2 definitions and 1 theorem. The definitions and types are `OAI.MetricKMedian.RoundingProgram.SignedRound.partialInput`, `OAI.MetricKMedian.RoundingProgram.SignedRound.partialInputs`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Preparation_RepresentativeProgram`, `KMedian_Rounding_SignedRoundProgram`.
--
--   **Imports.** It imports the bundles `OAIQ035K002`, `OAIQ035K006`, `OAIQ035K017`, `OAIQ035K047` and `OAIQ035K051` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ035K063`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K006
import Definitions.Def_OAIQ035K017
import Definitions.Def_OAIQ035K047
import Definitions.Def_OAIQ035K051

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RepresentativeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalRepresentatives.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram

 theorem any_view {n : ℕ} (U : Finset (Fin n)) : (setView U).any id=decide U.Nonempty := by
  apply Bool.eq_iff_iff.mpr
  simp only [setView,List.any_eq_true,List.mem_ofFn,id_eq,decide_eq_true_eq]
  constructor
  · rintro ⟨b,⟨i,rfl⟩,hi⟩; exact ⟨i,of_decide_eq_true hi⟩
  · rintro ⟨i,hi⟩; exact ⟨_,⟨i,rfl⟩,decide_eq_true hi⟩

end MetricKMedian.Preparation.RationalRepresentatives.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
namespace SignedRound

def partialInput (x : Input true) (i : Fin (SparseSignedPartial.run x.β x.p x.n).length) : Input true :=
  ⟨x.n,x.β,(SparseSignedPartial.run x.β x.p x.n).states[i.val],x.positive,
    (SparseSignedPartial.run_invariants _ _ x.feasible _ i).1⟩
def partialInputs (x : Input true) : List (Input true) := List.ofFn (partialInput x)

end SignedRound
end MetricKMedian.RoundingProgram
end

end OAI
end


