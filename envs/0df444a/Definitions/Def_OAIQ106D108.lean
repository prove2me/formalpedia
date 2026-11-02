-- Prove2me | Definitions.Def_OAIQ106D108
-- name    : OAIQ106D108
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:05:38.023496+00:00
-- url     : https://prove2.me/theorems/a8a8d850-c3a5-41cc-bb46-c961ba9ad932
-- title:
--   Definitions bundle OAIQ106D108 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 564 declarations of OpenAI's Lean: 564 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow8467`, `OAI.MUB6.Certificate.GramRows.rawRow8468`, `OAI.MUB6.Certificate.GramRows.rawRow8469`, `OAI.MUB6.Certificate.GramRows.rawRow8470`, `OAI.MUB6.Certificate.GramRows.rawRow8471`, `OAI.MUB6.Certificate.GramRows.rawRow8472`, `OAI.MUB6.Certificate.GramRows.rawRow8473`, `OAI.MUB6.Certificate.GramRows.rawRow8474`, `OAI.MUB6.Certificate.GramRows.rawRow8475`, `OAI.MUB6.Certificate.GramRows.rawRow8476`, `OAI.MUB6.Certificate.GramRows.rawRow8477`, `OAI.MUB6.Certificate.GramRows.rawRow8478`, `OAI.MUB6.Certificate.GramRows.rawRow8479`, `OAI.MUB6.Certificate.GramRows.rawRow8480`, `OAI.MUB6.Certificate.GramRows.rawRow8481`, `OAI.MUB6.Certificate.GramRows.rawRow8482`, `OAI.MUB6.Certificate.GramRows.rawRow8483`, `OAI.MUB6.Certificate.GramRows.rawRow8484`, `OAI.MUB6.Certificate.GramRows.rawRow852`, `OAI.MUB6.Certificate.GramRows.rawRow862`, `OAI.MUB6.Certificate.GramRows.rawRow866`, `OAI.MUB6.Certificate.GramRows.rawRow87`, `OAI.MUB6.Certificate.GramRows.rawRow8750`, `OAI.MUB6.Certificate.GramRows.rawRow8751`, `OAI.MUB6.Certificate.GramRows.rawRow8752`, `OAI.MUB6.Certificate.GramRows.rawRow8753`, `OAI.MUB6.Certificate.GramRows.rawRow8754`, `OAI.MUB6.Certificate.GramRows.rawRow8755`, `OAI.MUB6.Certificate.GramRows.rawRow8756`, `OAI.MUB6.Certificate.GramRows.rawRow876`, `OAI.MUB6.Certificate.GramRows.rawRow8793`, `OAI.MUB6.Certificate.GramRows.rawRow8794`, `OAI.MUB6.Certificate.GramRows.rawRow8795`, `OAI.MUB6.Certificate.GramRows.rawRow8796`, `OAI.MUB6.Certificate.GramRows.rawRow8797`, `OAI.MUB6.Certificate.GramRows.rawRow8798`, `OAI.MUB6.Certificate.GramRows.rawRow8799`, `OAI.MUB6.Certificate.GramRows.rawRow880`, `OAI.MUB6.Certificate.GramRows.rawRow8800`, `OAI.MUB6.Certificate.GramRows.rawRow8825` and 524 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Certificate_CompareMerge`, `MutuallyUnbiased_Certificate_Integer`, `MutuallyUnbiased_Certificate_IntegerMerge`, `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block100`, `MutuallyUnbiased_GramRows_Block101`, `MutuallyUnbiased_GramRows_Block23`, `MutuallyUnbiased_GramRows_Block24`, `MutuallyUnbiased_GramRows_Block25`, `MutuallyUnbiased_GramRows_Block27`, `MutuallyUnbiased_GramRows_Block90`, `MutuallyUnbiased_GramRows_Block92`, `MutuallyUnbiased_GramRows_Block93`, `MutuallyUnbiased_GramRows_Block94`, `MutuallyUnbiased_GramRows_Block95`, `MutuallyUnbiased_GramRows_Block96`, `MutuallyUnbiased_GramRows_Block97`, `MutuallyUnbiased_GramRows_Block98`, `MutuallyUnbiased_GramRows_Block99`, `MutuallyUnbiased_MixedData_Source8`, `MutuallyUnbiased_MixedMerge_Block0`, `MutuallyUnbiased_MixedMerge_Block3`, `MutuallyUnbiased_MixedMerge_Block31`, `MutuallyUnbiased_MixedMerge_Block32`, `MutuallyUnbiased_MixedMerge_Block33`, `MutuallyUnbiased_MixedMerge_Block34`, `MutuallyUnbiased_MixedMerge_Block35`, `MutuallyUnbiased_MixedSemantics_Values15`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D186`; the proofs of `OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_15`, `OAI.MUB6.Certificate.GramAssembly.Block1.rows_eval`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_10`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_22`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_26`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_5`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_8`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_9`, `OAI.MUB6.Certificate.GramAssembly.Block3.rows_eval` and `OAI.MUB6.Certificate.GramAssembly.Block4.rows_eval`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D001
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Integer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer coefficient checking after denominator clearing. The arithmetic
checker uses only integer operations; its interpretation remains over arbitrary
real moment vectors. -/
namespace MUB6.Certificate.Integer

open scoped BigOperators

namespace Combination

variable {ι κ η : Type*}

noncomputable def eval (rows : κ → Sparse ι) (x : ι → ℝ) : Combination κ → ℝ
  | .leaf k => Sparse.eval (rows k) x
  | .add a b => eval rows x a + eval rows x b
  | .scale q a => (q : ℝ) * eval rows x a

end Combination
end MUB6.Certificate.Integer

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

def mergeFuel [LinearOrder ι] : ℕ → Sparse ι → Sparse ι → Sparse ι
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a, [] => a
  | fuel + 1, a :: as, b :: bs =>
      if a.1 < b.1 then a :: mergeFuel fuel as (b :: bs)
      else if a.1 = b.1 then
        if a.2 + b.2 = 0 then mergeFuel fuel as bs
        else (a.1, a.2 + b.2) :: mergeFuel fuel as bs
      else b :: mergeFuel fuel (a :: as) bs

def merge [LinearOrder ι] (a b : Sparse ι) : Sparse ι :=
  mergeFuel (a.length + b.length) a b

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_CompareMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse collection needs only a computable comparison, not order axioms.
The comparison changes the representation but never its real evaluation. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*} [DecidableEq ι]

def mergeByFuel (less : ι → ι → Bool) : ℕ → Sparse ι → Sparse ι → Sparse ι
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a, [] => a
  | fuel + 1, a :: as, b :: bs =>
      if less a.1 b.1 then a :: mergeByFuel less fuel as (b :: bs)
      else if a.1 = b.1 then
        if a.2 + b.2 = 0 then mergeByFuel less fuel as bs
        else (a.1, a.2 + b.2) :: mergeByFuel less fuel as bs
      else b :: mergeByFuel less fuel (a :: as) bs

def mergeBy (less : ι → ι → Bool) (a b : Sparse ι) : Sparse ι :=
  mergeByFuel less (a.length + b.length) a b

def mergePairs (less : ι → ι → Bool) : List (Sparse ι) → List (Sparse ι)
  | [] => []
  | [a] => [a]
  | a :: b :: rest => mergeBy less a b :: mergePairs less rest

def collectLevels (less : ι → ι → Bool) : ℕ → List (Sparse ι) → Sparse ι
  | 0, vs => vs.flatten
  | _ + 1, [] => []
  | _ + 1, [a] => a
  | fuel + 1, a :: b :: rest => collectLevels less fuel (mergePairs less (a :: b :: rest))

def collectBalanced (less : ι → ι → Bool) (v : Sparse ι) : Sparse ι :=
  collectLevels less v.length (v.map fun p => [p])

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow87 : Integer.Sparse Key := [(key2633, -2), (key2643, 1), (key2643, 1), (key2617, 2), (key2655, -1), (key2655, -1), (key2620, -1), (key2620, -1), (key2643, 1), (key2643, 1), (key2707, 2), (key2739, -1), (key2739, -1), (key2672, -2), (key2749, 1), (key2749, 1), (key2675, 1), (key2675, 1), (key2730, -1), (key2730, -1), (key2810, -2), (key2899, 1), (key2899, 1), (key2787, 2), (key2906, -1), (key2906, -1), (key2797, -1), (key2797, -1), (key2833, 1), (key2833, 1), (key2952, 1), (key2952, 1), (key2978, -1), (key2978, -1), (key2940, -1), (key2940, -1), (key2985, 1), (key2985, 1), (key2945, 1), (key2945, 1), (key2962, -1), (key2962, -1)]

def rawRow94 : Integer.Sparse Key := [(key2672, -2), (key2675, 1), (key2675, 1), (key2707, 2), (key2739, -1), (key2739, -1), (key2730, -1), (key2730, -1), (key2749, 1), (key2749, 1), (key2617, 2), (key2620, -1), (key2620, -1), (key2810, -2), (key2833, 1), (key2833, 1), (key2952, 1), (key2952, 1), (key2962, -1), (key2962, -1), (key2633, -2), (key2643, 1), (key2643, 1), (key2707, 2), (key2730, -1), (key2730, -1), (key2978, -1), (key2978, -1), (key2985, 1), (key2985, 1), (key2650, 1), (key2650, 1), (key2655, -1), (key2655, -1), (key2739, -1), (key2739, -1), (key2749, 1), (key2749, 1), (key2899, 1), (key2899, 1), (key2906, -1), (key2906, -1)]

def rawRow97 : Integer.Sparse Key := [(key2707, -2), (key2730, 1), (key2730, 1), (key2672, 2), (key2749, -1), (key2749, -1), (key2675, -1), (key2675, -1), (key2739, 1), (key2739, 1), (key2810, 2), (key2833, -1), (key2833, -1), (key2617, -2), (key2962, 1), (key2962, 1), (key2620, 1), (key2620, 1), (key2833, -1), (key2833, -1), (key2707, -2), (key2978, 1), (key2978, 1), (key2633, 2), (key2985, -1), (key2985, -1), (key2643, -1), (key2643, -1), (key2730, 1), (key2730, 1), (key2739, 1), (key2739, 1), (key2899, -1), (key2899, -1), (key2650, -1), (key2650, -1), (key2906, 1), (key2906, 1), (key2655, 1), (key2655, 1), (key2749, -1), (key2749, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9728 : Integer.Sparse Key := [(key3030, 1), (key2885, 1), (key3026, 1), (key2732, 1), (key2870, 1), (key2726, 1), (key3030, 1), (key2885, 1), (key3023, 1), (key2644, 1), (key2860, 1), (key2640, 1), (key3026, 1), (key2732, 1), (key3023, 1), (key2644, 1), (key2706, 1), (key2632, 1), (key2870, 1), (key2726, 1), (key2860, 1), (key2640, 1), (key2706, 1), (key2632, 1), (key2927, -2), (key2923, -2), (key2758, -2), (key2927, -2), (key2920, -2), (key2660, -2), (key2923, -2), (key2758, -2), (key2920, -2), (key2660, -2), (key2753, -2), (key2658, -2)]

def rawRow9729 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2640, 1), (key2640, 1), (key2660, 1), (key2660, 1), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2758, 1), (key2758, 1), (key2794, 1), (key2794, 1), (key2829, 1), (key2829, 1), (key2927, 1), (key2927, 1), (key3010, 1), (key3010, 1), (key3017, 1), (key3017, 1), (key3030, 1), (key3030, 1), (key2621, -2), (key2644, -2), (key2644, -2), (key2676, -2), (key2732, -2), (key2732, -2), (key2798, -2), (key2798, -2), (key2835, -2), (key2835, -2), (key2885, -2), (key2885, -2)]

def rawRow9730 : Integer.Sparse Key := [(key2646, 1), (key2653, 1), (key2612, 1), (key2653, 1), (key2616, 1), (key2640, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2829, 1), (key2927, 1), (key2794, 1), (key2927, 1), (key2794, 1), (key2829, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3030, 1), (key3010, 1), (key3017, 1), (key2644, -2), (key2621, -2), (key2644, -2), (key2732, -2), (key2676, -2), (key2732, -2), (key2835, -2), (key2885, -2), (key2798, -2), (key2885, -2), (key2798, -2), (key2835, -2)]

def rawRow9731 : Integer.Sparse Key := [(key2653, 1), (key2646, 1), (key2653, 1), (key2612, 1), (key2640, 1), (key2616, 1), (key2758, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2927, 1), (key2829, 1), (key2927, 1), (key2794, 1), (key2829, 1), (key2794, 1), (key3030, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3017, 1), (key3010, 1), (key2644, -2), (key2644, -2), (key2621, -2), (key2732, -2), (key2732, -2), (key2676, -2), (key2885, -2), (key2835, -2), (key2885, -2), (key2798, -2), (key2835, -2), (key2798, -2)]

def rawRow9732 : Integer.Sparse Key := [(key2667, 1), (key2667, 1), (key2735, 1), (key2735, 1), (key2747, 1), (key2747, 1), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2640, 1), (key2640, 1), (key2726, 1), (key2726, 1), (key3030, 1), (key3030, 1), (key2660, 1), (key2660, 1), (key2758, 1), (key2758, 1), (key2927, 1), (key2927, 1), (key2676, -2), (key2798, -2), (key2798, -2), (key2621, -2), (key2835, -2), (key2835, -2), (key2644, -2), (key2644, -2), (key2732, -2), (key2732, -2), (key2885, -2), (key2885, -2)]

def rawRow9733 : Integer.Sparse Key := [(key2735, 1), (key2747, 1), (key2667, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2927, 1), (key2660, 1), (key2758, 1), (key2798, -2), (key2676, -2), (key2798, -2), (key2835, -2), (key2621, -2), (key2835, -2), (key2732, -2), (key2885, -2), (key2644, -2), (key2885, -2), (key2644, -2), (key2732, -2)]

def rawRow9734 : Integer.Sparse Key := [(key2747, 1), (key2735, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2667, 1), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key3030, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2640, 1), (key2927, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2758, 1), (key2660, 1), (key2798, -2), (key2798, -2), (key2676, -2), (key2835, -2), (key2835, -2), (key2621, -2), (key2885, -2), (key2732, -2), (key2885, -2), (key2644, -2), (key2732, -2), (key2644, -2)]

def rawRow9735 : Integer.Sparse Key := [(key2936, 1), (key2943, 1), (key2948, 1), (key2998, 1), (key2960, 1), (key3000, 1), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1), (key2612, 1), (key2653, 1), (key2667, 1), (key2943, 1), (key2747, 1), (key2960, 1), (key2616, 1), (key2640, 1), (key2671, 1), (key2726, 1), (key2794, 1), (key2829, 1), (key2732, -2), (key2835, -2), (key2885, -2), (key2644, -2), (key2798, -2), (key2885, -2), (key2621, -2), (key2644, -2), (key2676, -2), (key2732, -2), (key2798, -2), (key2835, -2)]

def rawRow9736 : Integer.Sparse Key := [(key2943, 1), (key2936, 1), (key2998, 1), (key2948, 1), (key3000, 1), (key2960, 1), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1), (key2653, 1), (key2612, 1), (key2943, 1), (key2667, 1), (key2960, 1), (key2747, 1), (key2640, 1), (key2616, 1), (key2726, 1), (key2671, 1), (key2829, 1), (key2794, 1), (key2732, -2), (key2885, -2), (key2835, -2), (key2644, -2), (key2885, -2), (key2798, -2), (key2644, -2), (key2621, -2), (key2732, -2), (key2676, -2), (key2835, -2), (key2798, -2)]

def rawRow9737 : Integer.Sparse Key := [(key2948, 1), (key2960, 1), (key2936, 1), (key3000, 1), (key2943, 1), (key2998, 1), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2667, 1), (key2747, 1), (key2612, 1), (key2960, 1), (key2653, 1), (key2943, 1), (key2671, 1), (key2794, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2835, -2), (key2732, -2), (key2885, -2), (key2798, -2), (key2644, -2), (key2885, -2), (key2676, -2), (key2798, -2), (key2621, -2), (key2835, -2), (key2644, -2), (key2732, -2)]

def rawRow9738 : Integer.Sparse Key := [(key2960, 1), (key2948, 1), (key3000, 1), (key2936, 1), (key2998, 1), (key2943, 1), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1), (key2747, 1), (key2667, 1), (key2960, 1), (key2612, 1), (key2943, 1), (key2653, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2726, 1), (key2640, 1), (key2835, -2), (key2885, -2), (key2732, -2), (key2798, -2), (key2885, -2), (key2644, -2), (key2798, -2), (key2676, -2), (key2835, -2), (key2621, -2), (key2732, -2), (key2644, -2)]

def rawRow9739 : Integer.Sparse Key := [(key2998, 1), (key3000, 1), (key2943, 1), (key2960, 1), (key2936, 1), (key2948, 1), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1), (key2943, 1), (key2960, 1), (key2653, 1), (key2747, 1), (key2612, 1), (key2667, 1), (key2726, 1), (key2829, 1), (key2640, 1), (key2794, 1), (key2616, 1), (key2671, 1), (key2885, -2), (key2732, -2), (key2835, -2), (key2885, -2), (key2644, -2), (key2798, -2), (key2732, -2), (key2835, -2), (key2644, -2), (key2798, -2), (key2621, -2), (key2676, -2)]

def rawRow9740 : Integer.Sparse Key := [(key3000, 1), (key2998, 1), (key2960, 1), (key2943, 1), (key2948, 1), (key2936, 1), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1), (key2960, 1), (key2943, 1), (key2747, 1), (key2653, 1), (key2667, 1), (key2612, 1), (key2829, 1), (key2726, 1), (key2794, 1), (key2640, 1), (key2671, 1), (key2616, 1), (key2885, -2), (key2835, -2), (key2732, -2), (key2885, -2), (key2798, -2), (key2644, -2), (key2835, -2), (key2732, -2), (key2798, -2), (key2644, -2), (key2676, -2), (key2621, -2)]

def rawRow9765 : Integer.Sparse Key := [(key2770, 6), (key2770, 6), (key2773, 6), (key2932, 6), (key2601, -6), (key2890, -6), (key2911, -6), (key2911, -6)]

def rawRow9766 : Integer.Sparse Key := [(key2770, 6), (key2773, 6), (key2770, 6), (key2932, 6), (key2601, -6), (key2911, -6), (key2890, -6), (key2911, -6)]

def rawRow9767 : Integer.Sparse Key := [(key2773, 6), (key2770, 6), (key2770, 6), (key2932, 6), (key2601, -6), (key2911, -6), (key2911, -6), (key2890, -6)]

def rawRow9768 : Integer.Sparse Key := [(key2770, 6), (key2770, 6), (key2932, 6), (key2773, 6), (key2890, -6), (key2601, -6), (key2911, -6), (key2911, -6)]

def rawRow9769 : Integer.Sparse Key := [(key2770, 6), (key2932, 6), (key2770, 6), (key2773, 6), (key2890, -6), (key2911, -6), (key2601, -6), (key2911, -6)]

def rawRow9770 : Integer.Sparse Key := [(key2932, 6), (key2770, 6), (key2770, 6), (key2773, 6), (key2890, -6), (key2911, -6), (key2911, -6), (key2601, -6)]

def rawRow9771 : Integer.Sparse Key := [(key2770, 6), (key2773, 6), (key2932, 6), (key2770, 6), (key2911, -6), (key2601, -6), (key2890, -6), (key2911, -6)]

def rawRow9772 : Integer.Sparse Key := [(key2773, 6), (key2770, 6), (key2932, 6), (key2770, 6), (key2911, -6), (key2601, -6), (key2911, -6), (key2890, -6)]

def rawRow9773 : Integer.Sparse Key := [(key2770, 6), (key2932, 6), (key2773, 6), (key2770, 6), (key2911, -6), (key2890, -6), (key2601, -6), (key2911, -6)]

def rawRow9774 : Integer.Sparse Key := [(key2932, 6), (key2770, 6), (key2773, 6), (key2770, 6), (key2911, -6), (key2890, -6), (key2911, -6), (key2601, -6)]

def rawRow9775 : Integer.Sparse Key := [(key2773, 6), (key2932, 6), (key2770, 6), (key2770, 6), (key2911, -6), (key2911, -6), (key2601, -6), (key2890, -6)]

def rawRow9776 : Integer.Sparse Key := [(key2932, 6), (key2773, 6), (key2770, 6), (key2770, 6), (key2911, -6), (key2911, -6), (key2890, -6), (key2601, -6)]

def rawRow9777 : Integer.Sparse Key := [(key2847, 6), (key2847, 6), (key2890, 6), (key2969, 6), (key2594, -6), (key2773, -6), (key2881, -6), (key2881, -6)]

def rawRow9778 : Integer.Sparse Key := [(key2847, 6), (key2890, 6), (key2847, 6), (key2969, 6), (key2594, -6), (key2881, -6), (key2773, -6), (key2881, -6)]

def rawRow9779 : Integer.Sparse Key := [(key2890, 6), (key2847, 6), (key2847, 6), (key2969, 6), (key2594, -6), (key2881, -6), (key2881, -6), (key2773, -6)]

def rawRow9780 : Integer.Sparse Key := [(key2847, 6), (key2847, 6), (key2969, 6), (key2890, 6), (key2773, -6), (key2594, -6), (key2881, -6), (key2881, -6)]

def rawRow9781 : Integer.Sparse Key := [(key2847, 6), (key2969, 6), (key2847, 6), (key2890, 6), (key2773, -6), (key2881, -6), (key2594, -6), (key2881, -6)]

def rawRow9782 : Integer.Sparse Key := [(key2969, 6), (key2847, 6), (key2847, 6), (key2890, 6), (key2773, -6), (key2881, -6), (key2881, -6), (key2594, -6)]

def rawRow9783 : Integer.Sparse Key := [(key2847, 6), (key2890, 6), (key2969, 6), (key2847, 6), (key2881, -6), (key2594, -6), (key2773, -6), (key2881, -6)]

def rawRow9784 : Integer.Sparse Key := [(key2890, 6), (key2847, 6), (key2969, 6), (key2847, 6), (key2881, -6), (key2594, -6), (key2881, -6), (key2773, -6)]

def rawRow9785 : Integer.Sparse Key := [(key2847, 6), (key2969, 6), (key2890, 6), (key2847, 6), (key2881, -6), (key2773, -6), (key2594, -6), (key2881, -6)]

def rawRow9786 : Integer.Sparse Key := [(key2969, 6), (key2847, 6), (key2890, 6), (key2847, 6), (key2881, -6), (key2773, -6), (key2881, -6), (key2594, -6)]

def rawRow9787 : Integer.Sparse Key := [(key2890, 6), (key2969, 6), (key2847, 6), (key2847, 6), (key2881, -6), (key2881, -6), (key2594, -6), (key2773, -6)]

def rawRow9788 : Integer.Sparse Key := [(key2969, 6), (key2890, 6), (key2847, 6), (key2847, 6), (key2881, -6), (key2881, -6), (key2773, -6), (key2594, -6)]

def rawRow9789 : Integer.Sparse Key := [(key2402, 6), (key2402, 6), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -6), (key2926, -6)]

def rawRow9790 : Integer.Sparse Key := [(key2402, 6), (key2408, 6), (key2402, 6), (key2439, 6), (key2605, -6), (key2926, -6), (key2917, -6), (key2926, -6)]

def rawRow9791 : Integer.Sparse Key := [(key2408, 6), (key2402, 6), (key2402, 6), (key2439, 6), (key2605, -6), (key2926, -6), (key2926, -6), (key2917, -6)]

def rawRow9792 : Integer.Sparse Key := [(key2402, 6), (key2402, 6), (key2439, 6), (key2408, 6), (key2917, -6), (key2605, -6), (key2926, -6), (key2926, -6)]

def rawRow9793 : Integer.Sparse Key := [(key2402, 6), (key2439, 6), (key2402, 6), (key2408, 6), (key2917, -6), (key2926, -6), (key2605, -6), (key2926, -6)]

def rawRow9794 : Integer.Sparse Key := [(key2439, 6), (key2402, 6), (key2402, 6), (key2408, 6), (key2917, -6), (key2926, -6), (key2926, -6), (key2605, -6)]

def rawRow9795 : Integer.Sparse Key := [(key2402, 6), (key2408, 6), (key2439, 6), (key2402, 6), (key2926, -6), (key2605, -6), (key2917, -6), (key2926, -6)]

def rawRow9796 : Integer.Sparse Key := [(key2408, 6), (key2402, 6), (key2439, 6), (key2402, 6), (key2926, -6), (key2605, -6), (key2926, -6), (key2917, -6)]

def rawRow9797 : Integer.Sparse Key := [(key2402, 6), (key2439, 6), (key2408, 6), (key2402, 6), (key2926, -6), (key2917, -6), (key2605, -6), (key2926, -6)]

def rawRow9798 : Integer.Sparse Key := [(key2439, 6), (key2402, 6), (key2408, 6), (key2402, 6), (key2926, -6), (key2917, -6), (key2926, -6), (key2605, -6)]

def rawRow9799 : Integer.Sparse Key := [(key2408, 6), (key2439, 6), (key2402, 6), (key2402, 6), (key2926, -6), (key2926, -6), (key2605, -6), (key2917, -6)]

def rawRow9800 : Integer.Sparse Key := [(key2439, 6), (key2408, 6), (key2402, 6), (key2402, 6), (key2926, -6), (key2926, -6), (key2917, -6), (key2605, -6)]

def rawRow9801 : Integer.Sparse Key := [(key2468, 6), (key2468, 6), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -6), (key2884, -6)]

def rawRow9802 : Integer.Sparse Key := [(key2468, 6), (key2481, 6), (key2468, 6), (key2505, 6), (key2596, -6), (key2884, -6), (key2775, -6), (key2884, -6)]

def rawRow9803 : Integer.Sparse Key := [(key2481, 6), (key2468, 6), (key2468, 6), (key2505, 6), (key2596, -6), (key2884, -6), (key2884, -6), (key2775, -6)]

def rawRow9804 : Integer.Sparse Key := [(key2468, 6), (key2468, 6), (key2505, 6), (key2481, 6), (key2775, -6), (key2596, -6), (key2884, -6), (key2884, -6)]

def rawRow9805 : Integer.Sparse Key := [(key2468, 6), (key2505, 6), (key2468, 6), (key2481, 6), (key2775, -6), (key2884, -6), (key2596, -6), (key2884, -6)]

def rawRow9806 : Integer.Sparse Key := [(key2505, 6), (key2468, 6), (key2468, 6), (key2481, 6), (key2775, -6), (key2884, -6), (key2884, -6), (key2596, -6)]

def rawRow9807 : Integer.Sparse Key := [(key2468, 6), (key2481, 6), (key2505, 6), (key2468, 6), (key2884, -6), (key2596, -6), (key2775, -6), (key2884, -6)]

def rawRow9808 : Integer.Sparse Key := [(key2481, 6), (key2468, 6), (key2505, 6), (key2468, 6), (key2884, -6), (key2596, -6), (key2884, -6), (key2775, -6)]

def rawRow9809 : Integer.Sparse Key := [(key2468, 6), (key2505, 6), (key2481, 6), (key2468, 6), (key2884, -6), (key2775, -6), (key2596, -6), (key2884, -6)]

def rawRow9810 : Integer.Sparse Key := [(key2505, 6), (key2468, 6), (key2481, 6), (key2468, 6), (key2884, -6), (key2775, -6), (key2884, -6), (key2596, -6)]

def rawRow9811 : Integer.Sparse Key := [(key2481, 6), (key2505, 6), (key2468, 6), (key2468, 6), (key2884, -6), (key2884, -6), (key2596, -6), (key2775, -6)]

def rawRow9812 : Integer.Sparse Key := [(key2505, 6), (key2481, 6), (key2468, 6), (key2468, 6), (key2884, -6), (key2884, -6), (key2775, -6), (key2596, -6)]

def rawRow9837 : Integer.Sparse Key := [(key1033, 6), (key1033, 6), (key1041, 6), (key1076, 6), (key1019, -6), (key1127, -6), (key1199, -6), (key1199, -6)]

def rawRow9838 : Integer.Sparse Key := [(key1033, 6), (key1041, 6), (key1033, 6), (key1076, 6), (key1019, -6), (key1199, -6), (key1127, -6), (key1199, -6)]

def rawRow9839 : Integer.Sparse Key := [(key1041, 6), (key1033, 6), (key1033, 6), (key1076, 6), (key1019, -6), (key1199, -6), (key1199, -6), (key1127, -6)]

def rawRow9840 : Integer.Sparse Key := [(key1033, 6), (key1033, 6), (key1076, 6), (key1041, 6), (key1127, -6), (key1019, -6), (key1199, -6), (key1199, -6)]

def rawRow9841 : Integer.Sparse Key := [(key1033, 6), (key1076, 6), (key1033, 6), (key1041, 6), (key1127, -6), (key1199, -6), (key1019, -6), (key1199, -6)]

def rawRow9842 : Integer.Sparse Key := [(key1076, 6), (key1033, 6), (key1033, 6), (key1041, 6), (key1127, -6), (key1199, -6), (key1199, -6), (key1019, -6)]

def rawRow9843 : Integer.Sparse Key := [(key1033, 6), (key1041, 6), (key1076, 6), (key1033, 6), (key1199, -6), (key1019, -6), (key1127, -6), (key1199, -6)]

def rawRow9844 : Integer.Sparse Key := [(key1041, 6), (key1033, 6), (key1076, 6), (key1033, 6), (key1199, -6), (key1019, -6), (key1199, -6), (key1127, -6)]

def rawRow9845 : Integer.Sparse Key := [(key1033, 6), (key1076, 6), (key1041, 6), (key1033, 6), (key1199, -6), (key1127, -6), (key1019, -6), (key1199, -6)]

def rawRow9846 : Integer.Sparse Key := [(key1076, 6), (key1033, 6), (key1041, 6), (key1033, 6), (key1199, -6), (key1127, -6), (key1199, -6), (key1019, -6)]

def rawRow9847 : Integer.Sparse Key := [(key1041, 6), (key1076, 6), (key1033, 6), (key1033, 6), (key1199, -6), (key1199, -6), (key1019, -6), (key1127, -6)]

def rawRow9848 : Integer.Sparse Key := [(key1076, 6), (key1041, 6), (key1033, 6), (key1033, 6), (key1199, -6), (key1199, -6), (key1127, -6), (key1019, -6)]

def rawRow9849 : Integer.Sparse Key := [(key1111, 6), (key1111, 6), (key1127, 6), (key1155, 6), (key1006, -6), (key1041, -6), (key1193, -6), (key1193, -6)]

def rawRow9850 : Integer.Sparse Key := [(key1111, 6), (key1127, 6), (key1111, 6), (key1155, 6), (key1006, -6), (key1193, -6), (key1041, -6), (key1193, -6)]

def rawRow9851 : Integer.Sparse Key := [(key1127, 6), (key1111, 6), (key1111, 6), (key1155, 6), (key1006, -6), (key1193, -6), (key1193, -6), (key1041, -6)]

def rawRow9852 : Integer.Sparse Key := [(key1111, 6), (key1111, 6), (key1155, 6), (key1127, 6), (key1041, -6), (key1006, -6), (key1193, -6), (key1193, -6)]

def rawRow9853 : Integer.Sparse Key := [(key1111, 6), (key1155, 6), (key1111, 6), (key1127, 6), (key1041, -6), (key1193, -6), (key1006, -6), (key1193, -6)]

def rawRow9854 : Integer.Sparse Key := [(key1155, 6), (key1111, 6), (key1111, 6), (key1127, 6), (key1041, -6), (key1193, -6), (key1193, -6), (key1006, -6)]

def rawRow9855 : Integer.Sparse Key := [(key1111, 6), (key1127, 6), (key1155, 6), (key1111, 6), (key1193, -6), (key1006, -6), (key1041, -6), (key1193, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9856 : Integer.Sparse Key := [(key1127, 6), (key1111, 6), (key1155, 6), (key1111, 6), (key1193, -6), (key1006, -6), (key1193, -6), (key1041, -6)]

def rawRow9857 : Integer.Sparse Key := [(key1111, 6), (key1155, 6), (key1127, 6), (key1111, 6), (key1193, -6), (key1041, -6), (key1006, -6), (key1193, -6)]

def rawRow9858 : Integer.Sparse Key := [(key1155, 6), (key1111, 6), (key1127, 6), (key1111, 6), (key1193, -6), (key1041, -6), (key1193, -6), (key1006, -6)]

def rawRow9859 : Integer.Sparse Key := [(key1127, 6), (key1155, 6), (key1111, 6), (key1111, 6), (key1193, -6), (key1193, -6), (key1006, -6), (key1041, -6)]

def rawRow9860 : Integer.Sparse Key := [(key1155, 6), (key1127, 6), (key1111, 6), (key1111, 6), (key1193, -6), (key1193, -6), (key1041, -6), (key1006, -6)]

def rawRow9861 : Integer.Sparse Key := [(key2770, -6), (key2770, -6), (key2773, -6), (key2932, -6), (key2591, 2), (key2591, 2), (key2594, 2), (key2847, 2), (key2847, 2), (key2878, 2), (key2878, 2), (key2881, 2), (key2881, 2), (key2969, 2), (key2990, 2), (key2990, 2)]

def rawRow9862 : Integer.Sparse Key := [(key2770, -6), (key2773, -6), (key2770, -6), (key2932, -6), (key2591, 2), (key2594, 2), (key2591, 2), (key2878, 2), (key2881, 2), (key2847, 2), (key2881, 2), (key2847, 2), (key2878, 2), (key2990, 2), (key2969, 2), (key2990, 2)]

def rawRow9863 : Integer.Sparse Key := [(key2773, -6), (key2770, -6), (key2770, -6), (key2932, -6), (key2594, 2), (key2591, 2), (key2591, 2), (key2881, 2), (key2878, 2), (key2881, 2), (key2847, 2), (key2878, 2), (key2847, 2), (key2990, 2), (key2990, 2), (key2969, 2)]

def rawRow9864 : Integer.Sparse Key := [(key2770, -6), (key2770, -6), (key2932, -6), (key2773, -6), (key2847, 2), (key2847, 2), (key2969, 2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key2990, 2), (key2990, 2), (key2594, 2), (key2881, 2), (key2881, 2)]

def rawRow9865 : Integer.Sparse Key := [(key2770, -6), (key2932, -6), (key2770, -6), (key2773, -6), (key2847, 2), (key2969, 2), (key2847, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2881, 2), (key2594, 2), (key2881, 2)]

def rawRow9866 : Integer.Sparse Key := [(key2932, -6), (key2770, -6), (key2770, -6), (key2773, -6), (key2969, 2), (key2847, 2), (key2847, 2), (key2990, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2881, 2), (key2881, 2), (key2594, 2)]

def rawRow9867 : Integer.Sparse Key := [(key2770, -6), (key2773, -6), (key2932, -6), (key2770, -6), (key2878, 2), (key2881, 2), (key2990, 2), (key2591, 2), (key2594, 2), (key2847, 2), (key2881, 2), (key2969, 2), (key2990, 2), (key2591, 2), (key2847, 2), (key2878, 2)]

def rawRow9868 : Integer.Sparse Key := [(key2773, -6), (key2770, -6), (key2932, -6), (key2770, -6), (key2881, 2), (key2878, 2), (key2990, 2), (key2594, 2), (key2591, 2), (key2881, 2), (key2847, 2), (key2990, 2), (key2969, 2), (key2591, 2), (key2878, 2), (key2847, 2)]

def rawRow9869 : Integer.Sparse Key := [(key2770, -6), (key2932, -6), (key2773, -6), (key2770, -6), (key2878, 2), (key2990, 2), (key2881, 2), (key2847, 2), (key2969, 2), (key2591, 2), (key2990, 2), (key2594, 2), (key2881, 2), (key2847, 2), (key2591, 2), (key2878, 2)]

def rawRow9870 : Integer.Sparse Key := [(key2932, -6), (key2770, -6), (key2773, -6), (key2770, -6), (key2990, 2), (key2878, 2), (key2881, 2), (key2969, 2), (key2847, 2), (key2990, 2), (key2591, 2), (key2881, 2), (key2594, 2), (key2847, 2), (key2878, 2), (key2591, 2)]

def rawRow9871 : Integer.Sparse Key := [(key2773, -6), (key2932, -6), (key2770, -6), (key2770, -6), (key2881, 2), (key2990, 2), (key2878, 2), (key2881, 2), (key2990, 2), (key2594, 2), (key2969, 2), (key2591, 2), (key2847, 2), (key2878, 2), (key2591, 2), (key2847, 2)]

def rawRow9872 : Integer.Sparse Key := [(key2932, -6), (key2773, -6), (key2770, -6), (key2770, -6), (key2990, 2), (key2881, 2), (key2878, 2), (key2990, 2), (key2881, 2), (key2969, 2), (key2594, 2), (key2847, 2), (key2591, 2), (key2878, 2), (key2847, 2), (key2591, 2)]

def rawRow9873 : Integer.Sparse Key := [(key2847, -6), (key2847, -6), (key2890, -6), (key2969, -6), (key2591, 2), (key2591, 2), (key2601, 2), (key2770, 2), (key2770, 2), (key2878, 2), (key2878, 2), (key2911, 2), (key2911, 2), (key2932, 2), (key2990, 2), (key2990, 2)]

def rawRow9874 : Integer.Sparse Key := [(key2847, -6), (key2890, -6), (key2847, -6), (key2969, -6), (key2591, 2), (key2601, 2), (key2591, 2), (key2878, 2), (key2911, 2), (key2770, 2), (key2911, 2), (key2770, 2), (key2878, 2), (key2990, 2), (key2932, 2), (key2990, 2)]

def rawRow9875 : Integer.Sparse Key := [(key2890, -6), (key2847, -6), (key2847, -6), (key2969, -6), (key2601, 2), (key2591, 2), (key2591, 2), (key2911, 2), (key2878, 2), (key2911, 2), (key2770, 2), (key2878, 2), (key2770, 2), (key2990, 2), (key2990, 2), (key2932, 2)]

def rawRow9876 : Integer.Sparse Key := [(key2847, -6), (key2847, -6), (key2969, -6), (key2890, -6), (key2770, 2), (key2770, 2), (key2932, 2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key2990, 2), (key2990, 2), (key2601, 2), (key2911, 2), (key2911, 2)]

def rawRow9877 : Integer.Sparse Key := [(key2847, -6), (key2969, -6), (key2847, -6), (key2890, -6), (key2770, 2), (key2932, 2), (key2770, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2911, 2), (key2601, 2), (key2911, 2)]

def rawRow9878 : Integer.Sparse Key := [(key2969, -6), (key2847, -6), (key2847, -6), (key2890, -6), (key2932, 2), (key2770, 2), (key2770, 2), (key2990, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2911, 2), (key2911, 2), (key2601, 2)]

def rawRow9879 : Integer.Sparse Key := [(key2847, -6), (key2890, -6), (key2969, -6), (key2847, -6), (key2878, 2), (key2911, 2), (key2990, 2), (key2591, 2), (key2601, 2), (key2770, 2), (key2911, 2), (key2932, 2), (key2990, 2), (key2591, 2), (key2770, 2), (key2878, 2)]

def rawRow9880 : Integer.Sparse Key := [(key2890, -6), (key2847, -6), (key2969, -6), (key2847, -6), (key2911, 2), (key2878, 2), (key2990, 2), (key2601, 2), (key2591, 2), (key2911, 2), (key2770, 2), (key2990, 2), (key2932, 2), (key2591, 2), (key2878, 2), (key2770, 2)]

def rawRow9881 : Integer.Sparse Key := [(key2847, -6), (key2969, -6), (key2890, -6), (key2847, -6), (key2878, 2), (key2990, 2), (key2911, 2), (key2770, 2), (key2932, 2), (key2591, 2), (key2990, 2), (key2601, 2), (key2911, 2), (key2770, 2), (key2591, 2), (key2878, 2)]

def rawRow9882 : Integer.Sparse Key := [(key2969, -6), (key2847, -6), (key2890, -6), (key2847, -6), (key2990, 2), (key2878, 2), (key2911, 2), (key2932, 2), (key2770, 2), (key2990, 2), (key2591, 2), (key2911, 2), (key2601, 2), (key2770, 2), (key2878, 2), (key2591, 2)]

def rawRow9883 : Integer.Sparse Key := [(key2890, -6), (key2969, -6), (key2847, -6), (key2847, -6), (key2911, 2), (key2990, 2), (key2878, 2), (key2911, 2), (key2990, 2), (key2601, 2), (key2932, 2), (key2591, 2), (key2770, 2), (key2878, 2), (key2591, 2), (key2770, 2)]

def rawRow9884 : Integer.Sparse Key := [(key2969, -6), (key2890, -6), (key2847, -6), (key2847, -6), (key2990, 2), (key2911, 2), (key2878, 2), (key2990, 2), (key2911, 2), (key2932, 2), (key2601, 2), (key2770, 2), (key2591, 2), (key2878, 2), (key2770, 2), (key2591, 2)]

def rawRow9885 : Integer.Sparse Key := [(key2670, -6), (key2785, -6), (key2793, -6), (key2793, -6), (key2615, 6), (key2808, 6), (key2828, 6), (key2828, 6)]

def rawRow9886 : Integer.Sparse Key := [(key2670, -6), (key2793, -6), (key2785, -6), (key2793, -6), (key2615, 6), (key2828, 6), (key2808, 6), (key2828, 6)]

def rawRow9887 : Integer.Sparse Key := [(key2670, -6), (key2793, -6), (key2793, -6), (key2785, -6), (key2615, 6), (key2828, 6), (key2828, 6), (key2808, 6)]

def rawRow9888 : Integer.Sparse Key := [(key2785, -6), (key2670, -6), (key2793, -6), (key2793, -6), (key2808, 6), (key2615, 6), (key2828, 6), (key2828, 6)]

def rawRow9889 : Integer.Sparse Key := [(key2785, -6), (key2793, -6), (key2670, -6), (key2793, -6), (key2808, 6), (key2828, 6), (key2615, 6), (key2828, 6)]

def rawRow9890 : Integer.Sparse Key := [(key2785, -6), (key2793, -6), (key2793, -6), (key2670, -6), (key2808, 6), (key2828, 6), (key2828, 6), (key2615, 6)]

def rawRow9891 : Integer.Sparse Key := [(key2793, -6), (key2670, -6), (key2785, -6), (key2793, -6), (key2828, 6), (key2615, 6), (key2808, 6), (key2828, 6)]

def rawRow9892 : Integer.Sparse Key := [(key2793, -6), (key2670, -6), (key2793, -6), (key2785, -6), (key2828, 6), (key2615, 6), (key2828, 6), (key2808, 6)]

def rawRow9893 : Integer.Sparse Key := [(key2793, -6), (key2785, -6), (key2670, -6), (key2793, -6), (key2828, 6), (key2808, 6), (key2615, 6), (key2828, 6)]

def rawRow9894 : Integer.Sparse Key := [(key2793, -6), (key2785, -6), (key2793, -6), (key2670, -6), (key2828, 6), (key2808, 6), (key2828, 6), (key2615, 6)]

def rawRow9895 : Integer.Sparse Key := [(key2793, -6), (key2793, -6), (key2670, -6), (key2785, -6), (key2828, 6), (key2828, 6), (key2615, 6), (key2808, 6)]

def rawRow9896 : Integer.Sparse Key := [(key2793, -6), (key2793, -6), (key2785, -6), (key2670, -6), (key2828, 6), (key2828, 6), (key2808, 6), (key2615, 6)]

def rawRow9897 : Integer.Sparse Key := [(key2705, -6), (key2808, -6), (key2859, -6), (key2859, -6), (key2631, 6), (key2785, 6), (key2869, 6), (key2869, 6)]

def rawRow9898 : Integer.Sparse Key := [(key2705, -6), (key2859, -6), (key2808, -6), (key2859, -6), (key2631, 6), (key2869, 6), (key2785, 6), (key2869, 6)]

def rawRow9899 : Integer.Sparse Key := [(key2705, -6), (key2859, -6), (key2859, -6), (key2808, -6), (key2631, 6), (key2869, 6), (key2869, 6), (key2785, 6)]

def rawRow9900 : Integer.Sparse Key := [(key2808, -6), (key2705, -6), (key2859, -6), (key2859, -6), (key2785, 6), (key2631, 6), (key2869, 6), (key2869, 6)]

def rawRow9901 : Integer.Sparse Key := [(key2808, -6), (key2859, -6), (key2705, -6), (key2859, -6), (key2785, 6), (key2869, 6), (key2631, 6), (key2869, 6)]

def rawRow9902 : Integer.Sparse Key := [(key2808, -6), (key2859, -6), (key2859, -6), (key2705, -6), (key2785, 6), (key2869, 6), (key2869, 6), (key2631, 6)]

def rawRow9903 : Integer.Sparse Key := [(key2859, -6), (key2705, -6), (key2808, -6), (key2859, -6), (key2869, 6), (key2631, 6), (key2785, 6), (key2869, 6)]

def rawRow9904 : Integer.Sparse Key := [(key2859, -6), (key2705, -6), (key2859, -6), (key2808, -6), (key2869, 6), (key2631, 6), (key2869, 6), (key2785, 6)]

def rawRow9905 : Integer.Sparse Key := [(key2859, -6), (key2808, -6), (key2705, -6), (key2859, -6), (key2869, 6), (key2785, 6), (key2631, 6), (key2869, 6)]

def rawRow9906 : Integer.Sparse Key := [(key2859, -6), (key2808, -6), (key2859, -6), (key2705, -6), (key2869, 6), (key2785, 6), (key2869, 6), (key2631, 6)]

def rawRow9907 : Integer.Sparse Key := [(key2859, -6), (key2859, -6), (key2705, -6), (key2808, -6), (key2869, 6), (key2869, 6), (key2631, 6), (key2785, 6)]

def rawRow9908 : Integer.Sparse Key := [(key2859, -6), (key2859, -6), (key2808, -6), (key2705, -6), (key2869, 6), (key2869, 6), (key2785, 6), (key2631, 6)]

def rawRow9909 : Integer.Sparse Key := [(key2617, -2), (key2620, -2), (key2620, -2), (key2810, -2), (key2833, -2), (key2833, -2), (key2952, -2), (key2952, -2), (key2962, -2), (key2962, -2), (key2964, -2), (key2964, -2), (key2633, 2), (key2643, 2), (key2643, 2), (key2707, 2), (key2730, 2), (key2730, 2), (key2978, 2), (key2978, 2), (key2985, 2), (key2985, 2), (key2994, 2), (key2994, 2)]

def rawRow9910 : Integer.Sparse Key := [(key2620, -2), (key2617, -2), (key2620, -2), (key2833, -2), (key2810, -2), (key2833, -2), (key2962, -2), (key2964, -2), (key2952, -2), (key2964, -2), (key2952, -2), (key2962, -2), (key2643, 2), (key2633, 2), (key2643, 2), (key2730, 2), (key2707, 2), (key2730, 2), (key2985, 2), (key2994, 2), (key2978, 2), (key2994, 2), (key2978, 2), (key2985, 2)]

def rawRow9911 : Integer.Sparse Key := [(key2620, -2), (key2620, -2), (key2617, -2), (key2833, -2), (key2833, -2), (key2810, -2), (key2964, -2), (key2962, -2), (key2964, -2), (key2952, -2), (key2962, -2), (key2952, -2), (key2643, 2), (key2643, 2), (key2633, 2), (key2730, 2), (key2730, 2), (key2707, 2), (key2994, 2), (key2985, 2), (key2994, 2), (key2978, 2), (key2985, 2), (key2978, 2)]

def rawRow9912 : Integer.Sparse Key := [(key2810, -2), (key2833, -2), (key2833, -2), (key2617, -2), (key2962, -2), (key2962, -2), (key2620, -2), (key2620, -2), (key2833, -2), (key2833, -2), (key2964, -2), (key2964, -2), (key2707, 2), (key2978, 2), (key2978, 2), (key2633, 2), (key2985, 2), (key2985, 2), (key2643, 2), (key2643, 2), (key2730, 2), (key2730, 2), (key2994, 2), (key2994, 2)]

def rawRow9913 : Integer.Sparse Key := [(key2833, -2), (key2810, -2), (key2833, -2), (key2962, -2), (key2617, -2), (key2962, -2), (key2833, -2), (key2964, -2), (key2620, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2978, 2), (key2707, 2), (key2978, 2), (key2985, 2), (key2633, 2), (key2985, 2), (key2730, 2), (key2994, 2), (key2643, 2), (key2994, 2), (key2643, 2), (key2730, 2)]

def rawRow9914 : Integer.Sparse Key := [(key2833, -2), (key2833, -2), (key2810, -2), (key2962, -2), (key2962, -2), (key2617, -2), (key2964, -2), (key2833, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2620, -2), (key2978, 2), (key2978, 2), (key2707, 2), (key2985, 2), (key2985, 2), (key2633, 2), (key2994, 2), (key2730, 2), (key2994, 2), (key2643, 2), (key2730, 2), (key2643, 2)]

def rawRow9915 : Integer.Sparse Key := [(key2952, -2), (key2962, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2964, -2), (key2617, -2), (key2620, -2), (key2810, -2), (key2833, -2), (key2952, -2), (key2962, -2), (key2730, 2), (key2985, 2), (key2994, 2), (key2643, 2), (key2978, 2), (key2994, 2), (key2633, 2), (key2643, 2), (key2707, 2), (key2730, 2), (key2978, 2), (key2985, 2)]

def rawRow9916 : Integer.Sparse Key := [(key2952, -2), (key2964, -2), (key2962, -2), (key2620, -2), (key2964, -2), (key2833, -2), (key2620, -2), (key2617, -2), (key2833, -2), (key2810, -2), (key2962, -2), (key2952, -2), (key2730, 2), (key2994, 2), (key2985, 2), (key2643, 2), (key2994, 2), (key2978, 2), (key2643, 2), (key2633, 2), (key2730, 2), (key2707, 2), (key2985, 2), (key2978, 2)]

def rawRow9917 : Integer.Sparse Key := [(key2962, -2), (key2952, -2), (key2964, -2), (key2833, -2), (key2620, -2), (key2964, -2), (key2810, -2), (key2833, -2), (key2617, -2), (key2962, -2), (key2620, -2), (key2833, -2), (key2985, 2), (key2730, 2), (key2994, 2), (key2978, 2), (key2643, 2), (key2994, 2), (key2707, 2), (key2978, 2), (key2633, 2), (key2985, 2), (key2643, 2), (key2730, 2)]

def rawRow9918 : Integer.Sparse Key := [(key2962, -2), (key2964, -2), (key2952, -2), (key2833, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2810, -2), (key2962, -2), (key2617, -2), (key2833, -2), (key2620, -2), (key2985, 2), (key2994, 2), (key2730, 2), (key2978, 2), (key2994, 2), (key2643, 2), (key2978, 2), (key2707, 2), (key2985, 2), (key2633, 2), (key2730, 2), (key2643, 2)]

def rawRow9919 : Integer.Sparse Key := [(key2964, -2), (key2952, -2), (key2962, -2), (key2964, -2), (key2620, -2), (key2833, -2), (key2952, -2), (key2962, -2), (key2620, -2), (key2833, -2), (key2617, -2), (key2810, -2), (key2994, 2), (key2730, 2), (key2985, 2), (key2994, 2), (key2643, 2), (key2978, 2), (key2730, 2), (key2985, 2), (key2643, 2), (key2978, 2), (key2633, 2), (key2707, 2)]

def rawRow9920 : Integer.Sparse Key := [(key2964, -2), (key2962, -2), (key2952, -2), (key2964, -2), (key2833, -2), (key2620, -2), (key2962, -2), (key2952, -2), (key2833, -2), (key2620, -2), (key2810, -2), (key2617, -2), (key2994, 2), (key2985, 2), (key2730, 2), (key2994, 2), (key2978, 2), (key2643, 2), (key2985, 2), (key2730, 2), (key2978, 2), (key2643, 2), (key2707, 2), (key2633, 2)]

def rawRow9921 : Integer.Sparse Key := [(key2633, -2), (key2643, -2), (key2643, -2), (key2707, -2), (key2978, -2), (key2978, -2), (key2730, -2), (key2730, -2), (key2985, -2), (key2985, -2), (key2994, -2), (key2994, -2), (key2617, 2), (key2655, 2), (key2655, 2), (key2672, 2), (key2749, 2), (key2749, 2), (key2945, 2), (key2945, 2), (key2962, 2), (key2962, 2), (key3004, 2), (key3004, 2)]

def rawRow9922 : Integer.Sparse Key := [(key2643, -2), (key2633, -2), (key2643, -2), (key2978, -2), (key2707, -2), (key2978, -2), (key2985, -2), (key2994, -2), (key2730, -2), (key2994, -2), (key2730, -2), (key2985, -2), (key2655, 2), (key2617, 2), (key2655, 2), (key2749, 2), (key2672, 2), (key2749, 2), (key2962, 2), (key3004, 2), (key2945, 2), (key3004, 2), (key2945, 2), (key2962, 2)]

def rawRow9923 : Integer.Sparse Key := [(key2643, -2), (key2643, -2), (key2633, -2), (key2978, -2), (key2978, -2), (key2707, -2), (key2994, -2), (key2985, -2), (key2994, -2), (key2730, -2), (key2985, -2), (key2730, -2), (key2655, 2), (key2655, 2), (key2617, 2), (key2749, 2), (key2749, 2), (key2672, 2), (key3004, 2), (key2962, 2), (key3004, 2), (key2945, 2), (key2962, 2), (key2945, 2)]

def rawRow9924 : Integer.Sparse Key := [(key2707, -2), (key2730, -2), (key2730, -2), (key2633, -2), (key2985, -2), (key2985, -2), (key2643, -2), (key2643, -2), (key2978, -2), (key2978, -2), (key2994, -2), (key2994, -2), (key2672, 2), (key2749, 2), (key2749, 2), (key2617, 2), (key2962, 2), (key2962, 2), (key2655, 2), (key2655, 2), (key2749, 2), (key2749, 2), (key3004, 2), (key3004, 2)]

def rawRow9925 : Integer.Sparse Key := [(key2730, -2), (key2707, -2), (key2730, -2), (key2985, -2), (key2633, -2), (key2985, -2), (key2978, -2), (key2994, -2), (key2643, -2), (key2994, -2), (key2643, -2), (key2978, -2), (key2749, 2), (key2672, 2), (key2749, 2), (key2962, 2), (key2617, 2), (key2962, 2), (key2749, 2), (key3004, 2), (key2655, 2), (key3004, 2), (key2655, 2), (key2749, 2)]

def rawRow9926 : Integer.Sparse Key := [(key2730, -2), (key2730, -2), (key2707, -2), (key2985, -2), (key2985, -2), (key2633, -2), (key2994, -2), (key2978, -2), (key2994, -2), (key2643, -2), (key2978, -2), (key2643, -2), (key2749, 2), (key2749, 2), (key2672, 2), (key2962, 2), (key2962, 2), (key2617, 2), (key3004, 2), (key2749, 2), (key3004, 2), (key2655, 2), (key2749, 2), (key2655, 2)]

def rawRow9927 : Integer.Sparse Key := [(key2978, -2), (key2985, -2), (key2994, -2), (key2643, -2), (key2730, -2), (key2994, -2), (key2633, -2), (key2643, -2), (key2707, -2), (key2978, -2), (key2730, -2), (key2985, -2), (key2945, 2), (key2962, 2), (key3004, 2), (key2655, 2), (key2749, 2), (key3004, 2), (key2617, 2), (key2655, 2), (key2672, 2), (key2749, 2), (key2945, 2), (key2962, 2)]

def rawRow9928 : Integer.Sparse Key := [(key2978, -2), (key2994, -2), (key2985, -2), (key2643, -2), (key2994, -2), (key2730, -2), (key2643, -2), (key2633, -2), (key2978, -2), (key2707, -2), (key2985, -2), (key2730, -2), (key2945, 2), (key3004, 2), (key2962, 2), (key2655, 2), (key3004, 2), (key2749, 2), (key2655, 2), (key2617, 2), (key2749, 2), (key2672, 2), (key2962, 2), (key2945, 2)]

def rawRow9929 : Integer.Sparse Key := [(key2985, -2), (key2978, -2), (key2994, -2), (key2730, -2), (key2643, -2), (key2994, -2), (key2707, -2), (key2730, -2), (key2633, -2), (key2985, -2), (key2643, -2), (key2978, -2), (key2962, 2), (key2945, 2), (key3004, 2), (key2749, 2), (key2655, 2), (key3004, 2), (key2672, 2), (key2749, 2), (key2617, 2), (key2962, 2), (key2655, 2), (key2749, 2)]

def rawRow9930 : Integer.Sparse Key := [(key2985, -2), (key2994, -2), (key2978, -2), (key2730, -2), (key2994, -2), (key2643, -2), (key2730, -2), (key2707, -2), (key2985, -2), (key2633, -2), (key2978, -2), (key2643, -2), (key2962, 2), (key3004, 2), (key2945, 2), (key2749, 2), (key3004, 2), (key2655, 2), (key2749, 2), (key2672, 2), (key2962, 2), (key2617, 2), (key2749, 2), (key2655, 2)]

def rawRow9931 : Integer.Sparse Key := [(key2994, -2), (key2978, -2), (key2985, -2), (key2994, -2), (key2643, -2), (key2730, -2), (key2978, -2), (key2985, -2), (key2643, -2), (key2730, -2), (key2633, -2), (key2707, -2), (key3004, 2), (key2945, 2), (key2962, 2), (key3004, 2), (key2655, 2), (key2749, 2), (key2945, 2), (key2962, 2), (key2655, 2), (key2749, 2), (key2617, 2), (key2672, 2)]

def rawRow9932 : Integer.Sparse Key := [(key2994, -2), (key2985, -2), (key2978, -2), (key2994, -2), (key2730, -2), (key2643, -2), (key2985, -2), (key2978, -2), (key2730, -2), (key2643, -2), (key2707, -2), (key2633, -2), (key3004, 2), (key2962, 2), (key2945, 2), (key3004, 2), (key2749, 2), (key2655, 2), (key2962, 2), (key2945, 2), (key2749, 2), (key2655, 2), (key2672, 2), (key2617, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow852 : Integer.Sparse Key := [(key1382, -6), (key1415, 2), (key1415, 2), (key1415, 2), (key1287, 6), (key1564, -2), (key1564, -2), (key1564, -2), (key1307, -2), (key1307, -2), (key1307, -2), (key1537, 2), (key1537, 2), (key1537, 2)]

def rawRow862 : Integer.Sparse Key := [(key2610, -2), (key2610, -2), (key2610, -2), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2665, 2), (key2665, 2), (key2665, 2), (key2780, -1), (key2780, -1), (key2780, -1), (key2780, -1), (key2780, -1), (key2780, -1), (key2700, -1), (key2700, -1), (key2700, -1), (key2700, -1), (key2700, -1), (key2700, -1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow866 : Integer.Sparse Key := [(key2665, -2), (key2665, -2), (key2665, -2), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2700, 1), (key2610, 2), (key2610, 2), (key2610, 2), (key2803, -1), (key2803, -1), (key2803, -1), (key2803, -1), (key2803, -1), (key2803, -1), (key2626, -1), (key2626, -1), (key2626, -1), (key2626, -1), (key2626, -1), (key2626, -1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1), (key2780, 1)]

def rawRow876 : Integer.Sparse Key := [(key995, -2), (key995, -2), (key995, -2), (key1011, 6), (key1030, 2), (key1030, 2), (key1030, 2), (key1119, -2), (key1119, -2), (key1119, -2), (key1067, -6), (key1146, 2), (key1146, 2), (key1146, 2)]

def rawRow880 : Integer.Sparse Key := [(key1030, -2), (key1030, -2), (key1030, -2), (key1067, 6), (key995, 2), (key995, 2), (key995, 2), (key1146, -2), (key1146, -2), (key1146, -2), (key1011, -6), (key1119, 2), (key1119, 2), (key1119, 2)]

def rawRow890 : Integer.Sparse Key := [(key2606, -6), (key2622, 2), (key2622, 2), (key2622, 2), (key2661, 6), (key2696, -2), (key2696, -2), (key2696, -2), (key2776, -2), (key2776, -2), (key2776, -2), (key2799, 2), (key2799, 2), (key2799, 2)]

def rawRow894 : Integer.Sparse Key := [(key2661, -6), (key2696, 2), (key2696, 2), (key2696, 2), (key2606, 6), (key2799, -2), (key2799, -2), (key2799, -2), (key2622, -2), (key2622, -2), (key2622, -2), (key2696, 2), (key2696, 2), (key2696, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow910 : Integer.Sparse Key := [(key1303, -2), (key1791, -2), (key1791, -2), (key1296, 1), (key1296, 1), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1330, 2), (key1818, 2), (key1818, 2), (key1316, -1), (key1316, -1), (key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1346, -1), (key1346, -1), (key1660, -1), (key1660, -1), (key1842, -1), (key1842, -1), (key1340, 1), (key1340, 1), (key1458, 1), (key1458, 1), (key1840, 1), (key1840, 1)]

def rawRow911 : Integer.Sparse Key := [(key1791, -2), (key1303, -2), (key1791, -2), (key1573, 1), (key1788, 1), (key1296, 1), (key1788, 1), (key1296, 1), (key1573, 1), (key1818, 2), (key1330, 2), (key1818, 2), (key1424, -1), (key1813, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1660, -1), (key1842, -1), (key1346, -1), (key1842, -1), (key1346, -1), (key1660, -1), (key1458, 1), (key1840, 1), (key1340, 1), (key1840, 1), (key1340, 1), (key1458, 1)]

def rawRow912 : Integer.Sparse Key := [(key1791, -2), (key1791, -2), (key1303, -2), (key1788, 1), (key1573, 1), (key1788, 1), (key1296, 1), (key1573, 1), (key1296, 1), (key1818, 2), (key1818, 2), (key1330, 2), (key1813, -1), (key1424, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1316, -1), (key1842, -1), (key1660, -1), (key1842, -1), (key1346, -1), (key1660, -1), (key1346, -1), (key1840, 1), (key1458, 1), (key1840, 1), (key1340, 1), (key1458, 1), (key1340, 1)]

def rawRow925 : Integer.Sparse Key := [(key1330, -2), (key1818, -2), (key1818, -2), (key1346, 1), (key1346, 1), (key1660, 1), (key1660, 1), (key1842, 1), (key1842, 1), (key1303, 2), (key1791, 2), (key1791, 2), (key1340, -1), (key1340, -1), (key1458, -1), (key1458, -1), (key1840, -1), (key1840, -1), (key1296, -1), (key1296, -1), (key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1316, 1), (key1316, 1), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1)]

def rawRow926 : Integer.Sparse Key := [(key1818, -2), (key1330, -2), (key1818, -2), (key1660, 1), (key1842, 1), (key1346, 1), (key1842, 1), (key1346, 1), (key1660, 1), (key1791, 2), (key1303, 2), (key1791, 2), (key1458, -1), (key1840, -1), (key1340, -1), (key1840, -1), (key1340, -1), (key1458, -1), (key1573, -1), (key1788, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1573, -1), (key1424, 1), (key1813, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1424, 1)]

def rawRow927 : Integer.Sparse Key := [(key1818, -2), (key1818, -2), (key1330, -2), (key1842, 1), (key1660, 1), (key1842, 1), (key1346, 1), (key1660, 1), (key1346, 1), (key1791, 2), (key1791, 2), (key1303, 2), (key1840, -1), (key1458, -1), (key1840, -1), (key1340, -1), (key1458, -1), (key1340, -1), (key1788, -1), (key1573, -1), (key1788, -1), (key1296, -1), (key1573, -1), (key1296, -1), (key1813, 1), (key1424, 1), (key1813, 1), (key1316, 1), (key1424, 1), (key1316, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow970 : Integer.Sparse Key := [(key1557, -2), (key1557, -2), (key1900, -2), (key1394, 1), (key1394, 1), (key1549, 1), (key1549, 1), (key1897, 1), (key1897, 1), (key1594, 2), (key1594, 2), (key1912, 2), (key1299, -1), (key1299, -1), (key1576, -1), (key1576, -1), (key1904, -1), (key1904, -1), (key1445, -1), (key1445, -1), (key1634, -1), (key1634, -1), (key1927, -1), (key1927, -1), (key1327, 1), (key1327, 1), (key1625, 1), (key1625, 1), (key1921, 1), (key1921, 1)]

def rawRow971 : Integer.Sparse Key := [(key1557, -2), (key1900, -2), (key1557, -2), (key1549, 1), (key1897, 1), (key1394, 1), (key1897, 1), (key1394, 1), (key1549, 1), (key1594, 2), (key1912, 2), (key1594, 2), (key1576, -1), (key1904, -1), (key1299, -1), (key1904, -1), (key1299, -1), (key1576, -1), (key1634, -1), (key1927, -1), (key1445, -1), (key1927, -1), (key1445, -1), (key1634, -1), (key1625, 1), (key1921, 1), (key1327, 1), (key1921, 1), (key1327, 1), (key1625, 1)]

def rawRow972 : Integer.Sparse Key := [(key1900, -2), (key1557, -2), (key1557, -2), (key1897, 1), (key1549, 1), (key1897, 1), (key1394, 1), (key1549, 1), (key1394, 1), (key1912, 2), (key1594, 2), (key1594, 2), (key1904, -1), (key1576, -1), (key1904, -1), (key1299, -1), (key1576, -1), (key1299, -1), (key1927, -1), (key1634, -1), (key1927, -1), (key1445, -1), (key1634, -1), (key1445, -1), (key1921, 1), (key1625, 1), (key1921, 1), (key1327, 1), (key1625, 1), (key1327, 1)]

def rawRow985 : Integer.Sparse Key := [(key1594, -2), (key1594, -2), (key1912, -2), (key1445, 1), (key1445, 1), (key1634, 1), (key1634, 1), (key1927, 1), (key1927, 1), (key1557, 2), (key1557, 2), (key1900, 2), (key1327, -1), (key1327, -1), (key1625, -1), (key1625, -1), (key1921, -1), (key1921, -1), (key1394, -1), (key1394, -1), (key1549, -1), (key1549, -1), (key1897, -1), (key1897, -1), (key1299, 1), (key1299, 1), (key1576, 1), (key1576, 1), (key1904, 1), (key1904, 1)]

def rawRow986 : Integer.Sparse Key := [(key1594, -2), (key1912, -2), (key1594, -2), (key1634, 1), (key1927, 1), (key1445, 1), (key1927, 1), (key1445, 1), (key1634, 1), (key1557, 2), (key1900, 2), (key1557, 2), (key1625, -1), (key1921, -1), (key1327, -1), (key1921, -1), (key1327, -1), (key1625, -1), (key1549, -1), (key1897, -1), (key1394, -1), (key1897, -1), (key1394, -1), (key1549, -1), (key1576, 1), (key1904, 1), (key1299, 1), (key1904, 1), (key1299, 1), (key1576, 1)]

def rawRow987 : Integer.Sparse Key := [(key1912, -2), (key1594, -2), (key1594, -2), (key1927, 1), (key1634, 1), (key1927, 1), (key1445, 1), (key1634, 1), (key1445, 1), (key1900, 2), (key1557, 2), (key1557, 2), (key1921, -1), (key1625, -1), (key1921, -1), (key1327, -1), (key1625, -1), (key1327, -1), (key1897, -1), (key1549, -1), (key1897, -1), (key1394, -1), (key1549, -1), (key1394, -1), (key1904, 1), (key1576, 1), (key1904, 1), (key1299, 1), (key1576, 1), (key1299, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8467 : Integer.Sparse Key := [(key3007, 1), (key3009, 1), (key3011, 1), (key3022, 1), (key3016, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2752, 1), (key2919, 1), (key2757, 1), (key2922, 1), (key2614, 1), (key2638, 1), (key2669, 1), (key2792, 1), (key2724, 1), (key2827, 1), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1), (key2724, -2), (key2827, -2), (key2868, -2), (key2638, -2), (key2792, -2), (key2858, -2), (key2614, -2), (key2630, -2), (key2669, -2), (key2704, -2), (key2784, -2), (key2807, -2)]

def rawRow8468 : Integer.Sparse Key := [(key3009, 1), (key3007, 1), (key3022, 1), (key3011, 1), (key3025, 1), (key3016, 1), (key2659, 1), (key2657, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2757, 1), (key2638, 1), (key2614, 1), (key2792, 1), (key2669, 1), (key2827, 1), (key2724, 1), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1), (key2724, -2), (key2868, -2), (key2827, -2), (key2638, -2), (key2858, -2), (key2792, -2), (key2630, -2), (key2614, -2), (key2704, -2), (key2669, -2), (key2807, -2), (key2784, -2)]

def rawRow8469 : Integer.Sparse Key := [(key3011, 1), (key3016, 1), (key3007, 1), (key3025, 1), (key3009, 1), (key3022, 1), (key2752, 1), (key2757, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2669, 1), (key2724, 1), (key2614, 1), (key2827, 1), (key2638, 1), (key2792, 1), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2827, -2), (key2724, -2), (key2868, -2), (key2792, -2), (key2638, -2), (key2858, -2), (key2669, -2), (key2784, -2), (key2614, -2), (key2807, -2), (key2630, -2), (key2704, -2)]

def rawRow8470 : Integer.Sparse Key := [(key3016, 1), (key3011, 1), (key3025, 1), (key3007, 1), (key3022, 1), (key3009, 1), (key2757, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2919, 1), (key2659, 1), (key2724, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2792, 1), (key2638, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1), (key2827, -2), (key2868, -2), (key2724, -2), (key2792, -2), (key2858, -2), (key2638, -2), (key2784, -2), (key2669, -2), (key2807, -2), (key2614, -2), (key2704, -2), (key2630, -2)]

def rawRow8471 : Integer.Sparse Key := [(key3022, 1), (key3025, 1), (key3009, 1), (key3016, 1), (key3007, 1), (key3011, 1), (key2919, 1), (key2922, 1), (key2659, 1), (key2757, 1), (key2657, 1), (key2752, 1), (key2792, 1), (key2827, 1), (key2638, 1), (key2724, 1), (key2614, 1), (key2669, 1), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1), (key2868, -2), (key2724, -2), (key2827, -2), (key2858, -2), (key2638, -2), (key2792, -2), (key2704, -2), (key2807, -2), (key2630, -2), (key2784, -2), (key2614, -2), (key2669, -2)]

def rawRow8472 : Integer.Sparse Key := [(key3025, 1), (key3022, 1), (key3016, 1), (key3009, 1), (key3011, 1), (key3007, 1), (key2922, 1), (key2919, 1), (key2757, 1), (key2659, 1), (key2752, 1), (key2657, 1), (key2827, 1), (key2792, 1), (key2724, 1), (key2638, 1), (key2669, 1), (key2614, 1), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1), (key2868, -2), (key2827, -2), (key2724, -2), (key2858, -2), (key2792, -2), (key2638, -2), (key2807, -2), (key2704, -2), (key2784, -2), (key2630, -2), (key2669, -2), (key2614, -2)]

def rawRow8473 : Integer.Sparse Key := [(key2614, 1), (key2614, 1), (key2630, 1), (key2630, 1), (key2638, 1), (key2638, 1), (key2669, 1), (key2669, 1), (key2784, 1), (key2784, 1), (key2792, 1), (key2792, 1), (key2704, 1), (key2704, 1), (key2807, 1), (key2807, 1), (key2858, 1), (key2858, 1), (key2724, 1), (key2724, 1), (key2827, 1), (key2827, 1), (key2868, 1), (key2868, 1), (key2608, -2), (key2624, -2), (key2624, -2), (key2663, -2), (key2698, -2), (key2698, -2), (key2778, -2), (key2778, -2), (key2801, -2), (key2801, -2), (key2851, -2), (key2851, -2)]

def rawRow8474 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2614, 1), (key2638, 1), (key2614, 1), (key2630, 1), (key2784, 1), (key2792, 1), (key2669, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2807, 1), (key2858, 1), (key2704, 1), (key2858, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2868, 1), (key2724, 1), (key2868, 1), (key2724, 1), (key2827, 1), (key2624, -2), (key2608, -2), (key2624, -2), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2851, -2), (key2778, -2), (key2801, -2)]

def rawRow8475 : Integer.Sparse Key := [(key2638, 1), (key2630, 1), (key2638, 1), (key2614, 1), (key2630, 1), (key2614, 1), (key2792, 1), (key2784, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2669, 1), (key2858, 1), (key2807, 1), (key2858, 1), (key2704, 1), (key2807, 1), (key2704, 1), (key2868, 1), (key2827, 1), (key2868, 1), (key2724, 1), (key2827, 1), (key2724, 1), (key2624, -2), (key2624, -2), (key2608, -2), (key2698, -2), (key2698, -2), (key2663, -2), (key2851, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2801, -2), (key2778, -2)]

def rawRow8476 : Integer.Sparse Key := [(key2669, 1), (key2669, 1), (key2704, 1), (key2704, 1), (key2724, 1), (key2724, 1), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1), (key2630, 1), (key2630, 1), (key2784, 1), (key2784, 1), (key2868, 1), (key2868, 1), (key2638, 1), (key2638, 1), (key2792, 1), (key2792, 1), (key2858, 1), (key2858, 1), (key2663, -2), (key2698, -2), (key2698, -2), (key2608, -2), (key2801, -2), (key2801, -2), (key2624, -2), (key2624, -2), (key2698, -2), (key2698, -2), (key2851, -2), (key2851, -2)]

def rawRow8477 : Integer.Sparse Key := [(key2704, 1), (key2724, 1), (key2669, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2784, 1), (key2868, 1), (key2630, 1), (key2868, 1), (key2630, 1), (key2784, 1), (key2792, 1), (key2858, 1), (key2638, 1), (key2858, 1), (key2638, 1), (key2792, 1), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, -2), (key2608, -2), (key2801, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2851, -2), (key2624, -2), (key2698, -2)]

def rawRow8478 : Integer.Sparse Key := [(key2724, 1), (key2704, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key2669, 1), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1), (key2868, 1), (key2784, 1), (key2868, 1), (key2630, 1), (key2784, 1), (key2630, 1), (key2858, 1), (key2792, 1), (key2858, 1), (key2638, 1), (key2792, 1), (key2638, 1), (key2698, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2801, -2), (key2608, -2), (key2851, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2624, -2)]

def rawRow8479 : Integer.Sparse Key := [(key2784, 1), (key2792, 1), (key2807, 1), (key2858, 1), (key2827, 1), (key2868, 1), (key2630, 1), (key2638, 1), (key2704, 1), (key2858, 1), (key2724, 1), (key2868, 1), (key2614, 1), (key2638, 1), (key2669, 1), (key2792, 1), (key2724, 1), (key2827, 1), (key2614, 1), (key2630, 1), (key2669, 1), (key2784, 1), (key2704, 1), (key2807, 1), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2851, -2), (key2608, -2), (key2624, -2), (key2663, -2), (key2698, -2), (key2778, -2), (key2801, -2)]

def rawRow8480 : Integer.Sparse Key := [(key2792, 1), (key2784, 1), (key2858, 1), (key2807, 1), (key2868, 1), (key2827, 1), (key2638, 1), (key2630, 1), (key2858, 1), (key2704, 1), (key2868, 1), (key2724, 1), (key2638, 1), (key2614, 1), (key2792, 1), (key2669, 1), (key2827, 1), (key2724, 1), (key2630, 1), (key2614, 1), (key2784, 1), (key2669, 1), (key2807, 1), (key2704, 1), (key2778, -2), (key2851, -2), (key2801, -2), (key2624, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2608, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2778, -2)]

def rawRow8481 : Integer.Sparse Key := [(key2807, 1), (key2827, 1), (key2784, 1), (key2868, 1), (key2792, 1), (key2858, 1), (key2704, 1), (key2724, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2858, 1), (key2669, 1), (key2724, 1), (key2614, 1), (key2827, 1), (key2638, 1), (key2792, 1), (key2669, 1), (key2704, 1), (key2614, 1), (key2807, 1), (key2630, 1), (key2784, 1), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2851, -2), (key2663, -2), (key2698, -2), (key2608, -2), (key2801, -2), (key2624, -2), (key2698, -2)]

def rawRow8482 : Integer.Sparse Key := [(key2827, 1), (key2807, 1), (key2868, 1), (key2784, 1), (key2858, 1), (key2792, 1), (key2724, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2858, 1), (key2638, 1), (key2724, 1), (key2669, 1), (key2827, 1), (key2614, 1), (key2792, 1), (key2638, 1), (key2704, 1), (key2669, 1), (key2807, 1), (key2614, 1), (key2784, 1), (key2630, 1), (key2801, -2), (key2851, -2), (key2778, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2608, -2), (key2698, -2), (key2624, -2)]

def rawRow8483 : Integer.Sparse Key := [(key2858, 1), (key2868, 1), (key2792, 1), (key2827, 1), (key2784, 1), (key2807, 1), (key2858, 1), (key2868, 1), (key2638, 1), (key2724, 1), (key2630, 1), (key2704, 1), (key2792, 1), (key2827, 1), (key2638, 1), (key2724, 1), (key2614, 1), (key2669, 1), (key2784, 1), (key2807, 1), (key2630, 1), (key2704, 1), (key2614, 1), (key2669, 1), (key2851, -2), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2778, -2), (key2801, -2), (key2624, -2), (key2698, -2), (key2608, -2), (key2663, -2)]

def rawRow8484 : Integer.Sparse Key := [(key2868, 1), (key2858, 1), (key2827, 1), (key2792, 1), (key2807, 1), (key2784, 1), (key2868, 1), (key2858, 1), (key2724, 1), (key2638, 1), (key2704, 1), (key2630, 1), (key2827, 1), (key2792, 1), (key2724, 1), (key2638, 1), (key2669, 1), (key2614, 1), (key2807, 1), (key2784, 1), (key2704, 1), (key2630, 1), (key2669, 1), (key2614, 1), (key2851, -2), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2801, -2), (key2778, -2), (key2698, -2), (key2624, -2), (key2663, -2), (key2608, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8750 : Integer.Sparse Key := [(key2356, 6), (key2353, 6), (key2356, 6), (key2356, 6), (key2527, -6), (key2527, -6), (key2558, -6), (key2527, -6)]

def rawRow8751 : Integer.Sparse Key := [(key2356, 6), (key2356, 6), (key2353, 6), (key2356, 6), (key2527, -6), (key2558, -6), (key2527, -6), (key2527, -6)]

def rawRow8752 : Integer.Sparse Key := [(key2356, 6), (key2356, 6), (key2356, 6), (key2353, 6), (key2558, -6), (key2527, -6), (key2527, -6), (key2527, -6)]

def rawRow8753 : Integer.Sparse Key := [(key2527, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2353, -6), (key2448, -6), (key2448, -6), (key2448, -6)]

def rawRow8754 : Integer.Sparse Key := [(key2527, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2448, -6), (key2353, -6), (key2448, -6), (key2448, -6)]

def rawRow8755 : Integer.Sparse Key := [(key2527, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2448, -6), (key2448, -6), (key2353, -6), (key2448, -6)]

def rawRow8756 : Integer.Sparse Key := [(key2558, 6), (key2527, 6), (key2527, 6), (key2527, 6), (key2448, -6), (key2448, -6), (key2448, -6), (key2353, -6)]

def rawRow8793 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2376, -2), (key2370, -2), (key2376, -2), (key2370, -2), (key2388, -2), (key2376, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2388, -2), (key2398, 2), (key2404, 2), (key2404, 2), (key2398, 2), (key2404, 2), (key2398, 2), (key2435, 2), (key2404, 2), (key2435, 2), (key2404, 2), (key2404, 2), (key2435, 2)]

def rawRow8794 : Integer.Sparse Key := [(key2376, -2), (key2370, -2), (key2376, -2), (key2376, -2), (key2370, -2), (key2388, -2), (key2370, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2388, -2), (key2376, -2), (key2404, 2), (key2398, 2), (key2404, 2), (key2404, 2), (key2398, 2), (key2435, 2), (key2398, 2), (key2435, 2), (key2404, 2), (key2404, 2), (key2435, 2), (key2404, 2)]

def rawRow8795 : Integer.Sparse Key := [(key2376, -2), (key2376, -2), (key2370, -2), (key2388, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2370, -2), (key2370, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2404, 2), (key2404, 2), (key2398, 2), (key2435, 2), (key2435, 2), (key2404, 2), (key2404, 2), (key2398, 2), (key2398, 2), (key2435, 2), (key2404, 2), (key2404, 2)]

def rawRow8796 : Integer.Sparse Key := [(key2388, -2), (key2388, -2), (key2388, -2), (key2376, -2), (key2376, -2), (key2376, -2), (key2376, -2), (key2376, -2), (key2376, -2), (key2370, -2), (key2370, -2), (key2370, -2), (key2435, 2), (key2435, 2), (key2435, 2), (key2404, 2), (key2404, 2), (key2404, 2), (key2404, 2), (key2404, 2), (key2404, 2), (key2398, 2), (key2398, 2), (key2398, 2)]

def rawRow8797 : Integer.Sparse Key := [(key3005, -2), (key3005, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key3019, -2), (key3019, -2), (key3019, -2), (key3019, -2), (key3028, -2), (key3028, -2), (key3028, -2), (key2604, 2), (key2604, 2), (key2604, 2), (key2916, 2), (key2916, 2), (key2916, 2), (key2916, 2), (key2916, 2), (key2916, 2), (key2925, 2), (key2925, 2), (key2925, 2)]

def rawRow8798 : Integer.Sparse Key := [(key3019, -2), (key3019, -2), (key3028, -2), (key3005, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key3028, -2), (key3028, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key2916, 2), (key2916, 2), (key2925, 2), (key2604, 2), (key2604, 2), (key2916, 2), (key2916, 2), (key2925, 2), (key2925, 2), (key2604, 2), (key2916, 2), (key2916, 2)]

def rawRow8799 : Integer.Sparse Key := [(key3019, -2), (key3028, -2), (key3019, -2), (key3019, -2), (key3028, -2), (key3005, -2), (key3028, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key3005, -2), (key3019, -2), (key2916, 2), (key2925, 2), (key2916, 2), (key2916, 2), (key2925, 2), (key2604, 2), (key2925, 2), (key2604, 2), (key2916, 2), (key2916, 2), (key2604, 2), (key2916, 2)]

def rawRow8800 : Integer.Sparse Key := [(key3028, -2), (key3019, -2), (key3019, -2), (key3028, -2), (key3019, -2), (key3028, -2), (key3005, -2), (key3019, -2), (key3005, -2), (key3019, -2), (key3019, -2), (key3005, -2), (key2925, 2), (key2916, 2), (key2916, 2), (key2925, 2), (key2916, 2), (key2925, 2), (key2604, 2), (key2916, 2), (key2604, 2), (key2916, 2), (key2916, 2), (key2604, 2)]

def rawRow8825 : Integer.Sparse Key := [(key2354, 6), (key2358, 6), (key2358, 6), (key2358, 6), (key2529, -6), (key2529, -6), (key2529, -6), (key2559, -6)]

def rawRow8826 : Integer.Sparse Key := [(key2358, 6), (key2354, 6), (key2358, 6), (key2358, 6), (key2529, -6), (key2529, -6), (key2559, -6), (key2529, -6)]

def rawRow8827 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2354, 6), (key2358, 6), (key2529, -6), (key2559, -6), (key2529, -6), (key2529, -6)]

def rawRow8828 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2358, 6), (key2354, 6), (key2559, -6), (key2529, -6), (key2529, -6), (key2529, -6)]

def rawRow8829 : Integer.Sparse Key := [(key2514, 6), (key2514, 6), (key2514, 6), (key2559, 6), (key2354, -6), (key2449, -6), (key2449, -6), (key2449, -6)]

def rawRow8830 : Integer.Sparse Key := [(key2514, 6), (key2514, 6), (key2559, 6), (key2514, 6), (key2449, -6), (key2354, -6), (key2449, -6), (key2449, -6)]

def rawRow8831 : Integer.Sparse Key := [(key2514, 6), (key2559, 6), (key2514, 6), (key2514, 6), (key2449, -6), (key2449, -6), (key2354, -6), (key2449, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8836 : Integer.Sparse Key := [(key2359, 6), (key2359, 6), (key2359, 6), (key2353, 6), (key2578, -6), (key2566, -6), (key2566, -6), (key2566, -6)]

def rawRow8837 : Integer.Sparse Key := [(key2566, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2353, -6), (key2448, -6), (key2448, -6), (key2448, -6)]

def rawRow8838 : Integer.Sparse Key := [(key2566, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2448, -6), (key2353, -6), (key2448, -6), (key2448, -6)]

def rawRow8839 : Integer.Sparse Key := [(key2566, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2448, -6), (key2448, -6), (key2353, -6), (key2448, -6)]

def rawRow8840 : Integer.Sparse Key := [(key2578, 6), (key2566, 6), (key2566, 6), (key2566, 6), (key2448, -6), (key2448, -6), (key2448, -6), (key2353, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9017 : Integer.Sparse Key := [(key2006, 6), (key2007, 6), (key2007, 6), (key2007, 6), (key2340, -6), (key2340, -6), (key2340, -6), (key2349, -6)]

def rawRow9018 : Integer.Sparse Key := [(key2007, 6), (key2006, 6), (key2007, 6), (key2007, 6), (key2340, -6), (key2340, -6), (key2349, -6), (key2340, -6)]

def rawRow9019 : Integer.Sparse Key := [(key2007, 6), (key2007, 6), (key2006, 6), (key2007, 6), (key2340, -6), (key2349, -6), (key2340, -6), (key2340, -6)]

def rawRow9020 : Integer.Sparse Key := [(key2007, 6), (key2007, 6), (key2007, 6), (key2006, 6), (key2349, -6), (key2340, -6), (key2340, -6), (key2340, -6)]

def rawRow9033 : Integer.Sparse Key := [(key1998, 6), (key2000, 6), (key2000, 6), (key2000, 6), (key2340, -6), (key2340, -6), (key2340, -6), (key2349, -6)]

def rawRow9034 : Integer.Sparse Key := [(key2000, 6), (key1998, 6), (key2000, 6), (key2000, 6), (key2340, -6), (key2340, -6), (key2349, -6), (key2340, -6)]

def rawRow9035 : Integer.Sparse Key := [(key2000, 6), (key2000, 6), (key1998, 6), (key2000, 6), (key2340, -6), (key2349, -6), (key2340, -6), (key2340, -6)]

def rawRow9036 : Integer.Sparse Key := [(key2000, 6), (key2000, 6), (key2000, 6), (key1998, 6), (key2349, -6), (key2340, -6), (key2340, -6), (key2340, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9109 : Integer.Sparse Key := [(key993, -2), (key1001, -2), (key1001, -2), (key993, -2), (key1001, -2), (key993, -2), (key1015, -2), (key1001, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key1015, -2), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1071, 2)]

def rawRow9110 : Integer.Sparse Key := [(key1001, -2), (key993, -2), (key1001, -2), (key1001, -2), (key993, -2), (key1015, -2), (key993, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key1015, -2), (key1001, -2), (key1036, 2), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1071, 2), (key1036, 2)]

def rawRow9111 : Integer.Sparse Key := [(key1001, -2), (key1001, -2), (key993, -2), (key1015, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key993, -2), (key993, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1036, 2)]

def rawRow9112 : Integer.Sparse Key := [(key1015, -2), (key1015, -2), (key1015, -2), (key1001, -2), (key1001, -2), (key1001, -2), (key1001, -2), (key1001, -2), (key1001, -2), (key993, -2), (key993, -2), (key993, -2), (key1071, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1028, 2)]

def rawRow9141 : Integer.Sparse Key := [(key972, 6), (key977, 6), (key977, 6), (key977, 6), (key1181, -6), (key1181, -6), (key1181, -6), (key1218, -6)]

def rawRow9142 : Integer.Sparse Key := [(key977, 6), (key972, 6), (key977, 6), (key977, 6), (key1181, -6), (key1181, -6), (key1218, -6), (key1181, -6)]

def rawRow9143 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key972, 6), (key977, 6), (key1181, -6), (key1218, -6), (key1181, -6), (key1181, -6)]

def rawRow9144 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key977, 6), (key972, 6), (key1218, -6), (key1181, -6), (key1181, -6), (key1181, -6)]

def rawRow9145 : Integer.Sparse Key := [(key1162, 6), (key1162, 6), (key1162, 6), (key1218, 6), (key972, -6), (key1086, -6), (key1086, -6), (key1086, -6)]

def rawRow9146 : Integer.Sparse Key := [(key1162, 6), (key1162, 6), (key1218, 6), (key1162, 6), (key1086, -6), (key972, -6), (key1086, -6), (key1086, -6)]

def rawRow9147 : Integer.Sparse Key := [(key1162, 6), (key1218, 6), (key1162, 6), (key1162, 6), (key1086, -6), (key1086, -6), (key972, -6), (key1086, -6)]

def rawRow9148 : Integer.Sparse Key := [(key1218, 6), (key1162, 6), (key1162, 6), (key1162, 6), (key1086, -6), (key1086, -6), (key1086, -6), (key972, -6)]

def rawRow9149 : Integer.Sparse Key := [(key971, 6), (key979, 6), (key979, 6), (key979, 6), (key1228, -6), (key1228, -6), (key1228, -6), (key1245, -6)]

def rawRow9150 : Integer.Sparse Key := [(key979, 6), (key971, 6), (key979, 6), (key979, 6), (key1228, -6), (key1228, -6), (key1245, -6), (key1228, -6)]

def rawRow9151 : Integer.Sparse Key := [(key979, 6), (key979, 6), (key971, 6), (key979, 6), (key1228, -6), (key1245, -6), (key1228, -6), (key1228, -6)]

def rawRow9152 : Integer.Sparse Key := [(key979, 6), (key979, 6), (key979, 6), (key971, 6), (key1245, -6), (key1228, -6), (key1228, -6), (key1228, -6)]

def rawRow9153 : Integer.Sparse Key := [(key1164, 6), (key1164, 6), (key1164, 6), (key1245, 6), (key971, -6), (key1085, -6), (key1085, -6), (key1085, -6)]

def rawRow9154 : Integer.Sparse Key := [(key1164, 6), (key1164, 6), (key1245, 6), (key1164, 6), (key1085, -6), (key971, -6), (key1085, -6), (key1085, -6)]

def rawRow9155 : Integer.Sparse Key := [(key1164, 6), (key1245, 6), (key1164, 6), (key1164, 6), (key1085, -6), (key1085, -6), (key971, -6), (key1085, -6)]

def rawRow9156 : Integer.Sparse Key := [(key1245, 6), (key1164, 6), (key1164, 6), (key1164, 6), (key1085, -6), (key1085, -6), (key1085, -6), (key971, -6)]

def rawRow9165 : Integer.Sparse Key := [(key1, 6), (key7, 6), (key7, 6), (key7, 6), (key193, -6), (key193, -6), (key193, -6), (key202, -6)]

def rawRow9166 : Integer.Sparse Key := [(key7, 6), (key1, 6), (key7, 6), (key7, 6), (key193, -6), (key193, -6), (key202, -6), (key193, -6)]

def rawRow9167 : Integer.Sparse Key := [(key7, 6), (key7, 6), (key1, 6), (key7, 6), (key193, -6), (key202, -6), (key193, -6), (key193, -6)]

def rawRow9168 : Integer.Sparse Key := [(key7, 6), (key7, 6), (key7, 6), (key1, 6), (key202, -6), (key193, -6), (key193, -6), (key193, -6)]

def rawRow9169 : Integer.Sparse Key := [(key193, 6), (key193, 6), (key193, 6), (key202, 6), (key1, -6), (key84, -6), (key84, -6), (key84, -6)]

def rawRow9170 : Integer.Sparse Key := [(key193, 6), (key193, 6), (key202, 6), (key193, 6), (key84, -6), (key1, -6), (key84, -6), (key84, -6)]

def rawRow9171 : Integer.Sparse Key := [(key193, 6), (key202, 6), (key193, 6), (key193, 6), (key84, -6), (key84, -6), (key1, -6), (key84, -6)]

def rawRow9172 : Integer.Sparse Key := [(key202, 6), (key193, 6), (key193, 6), (key193, 6), (key84, -6), (key84, -6), (key84, -6), (key1, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9317 : Integer.Sparse Key := [(key2354, 6), (key2358, 6), (key2358, 6), (key2358, 6), (key2514, -6), (key2514, -6), (key2514, -6), (key2559, -6)]

def rawRow9318 : Integer.Sparse Key := [(key2358, 6), (key2354, 6), (key2358, 6), (key2358, 6), (key2514, -6), (key2514, -6), (key2559, -6), (key2514, -6)]

def rawRow9319 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2354, 6), (key2358, 6), (key2514, -6), (key2559, -6), (key2514, -6), (key2514, -6)]

def rawRow9320 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2358, 6), (key2354, 6), (key2559, -6), (key2514, -6), (key2514, -6), (key2514, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9349 : Integer.Sparse Key := [(key972, 6), (key977, 6), (key977, 6), (key977, 6), (key1162, -6), (key1162, -6), (key1162, -6), (key1218, -6)]

def rawRow9350 : Integer.Sparse Key := [(key977, 6), (key972, 6), (key977, 6), (key977, 6), (key1162, -6), (key1162, -6), (key1218, -6), (key1162, -6)]

def rawRow9351 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key972, 6), (key977, 6), (key1162, -6), (key1218, -6), (key1162, -6), (key1162, -6)]

def rawRow9352 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key977, 6), (key972, 6), (key1218, -6), (key1162, -6), (key1162, -6), (key1162, -6)]

def rawRow9453 : Integer.Sparse Key := [(key2369, 6), (key2369, 6), (key2369, 6), (key2384, 6), (key2431, -6), (key2497, -6), (key2497, -6), (key2497, -6)]

def rawRow9454 : Integer.Sparse Key := [(key2369, 6), (key2369, 6), (key2384, 6), (key2369, 6), (key2497, -6), (key2431, -6), (key2497, -6), (key2497, -6)]

def rawRow9455 : Integer.Sparse Key := [(key2369, 6), (key2384, 6), (key2369, 6), (key2369, 6), (key2497, -6), (key2497, -6), (key2431, -6), (key2497, -6)]

def rawRow9456 : Integer.Sparse Key := [(key2384, 6), (key2369, 6), (key2369, 6), (key2369, 6), (key2497, -6), (key2497, -6), (key2497, -6), (key2431, -6)]

def rawRow9457 : Integer.Sparse Key := [(key2397, 6), (key2397, 6), (key2397, 6), (key2431, 6), (key2384, -6), (key2474, -6), (key2474, -6), (key2474, -6)]

def rawRow9458 : Integer.Sparse Key := [(key2397, 6), (key2397, 6), (key2431, 6), (key2397, 6), (key2474, -6), (key2384, -6), (key2474, -6), (key2474, -6)]

def rawRow9459 : Integer.Sparse Key := [(key2397, 6), (key2431, 6), (key2397, 6), (key2397, 6), (key2474, -6), (key2474, -6), (key2384, -6), (key2474, -6)]

def rawRow9460 : Integer.Sparse Key := [(key2431, 6), (key2397, 6), (key2397, 6), (key2397, 6), (key2474, -6), (key2474, -6), (key2474, -6), (key2384, -6)]

def rawRow9461 : Integer.Sparse Key := [(key2372, 6), (key2372, 6), (key2372, 6), (key2385, 6), (key2432, -6), (key2498, -6), (key2498, -6), (key2498, -6)]

def rawRow9462 : Integer.Sparse Key := [(key2372, 6), (key2372, 6), (key2385, 6), (key2372, 6), (key2498, -6), (key2432, -6), (key2498, -6), (key2498, -6)]

def rawRow9463 : Integer.Sparse Key := [(key2372, 6), (key2385, 6), (key2372, 6), (key2372, 6), (key2498, -6), (key2498, -6), (key2432, -6), (key2498, -6)]

def rawRow9464 : Integer.Sparse Key := [(key2385, 6), (key2372, 6), (key2372, 6), (key2372, 6), (key2498, -6), (key2498, -6), (key2498, -6), (key2432, -6)]

def rawRow9465 : Integer.Sparse Key := [(key2400, 6), (key2400, 6), (key2400, 6), (key2432, 6), (key2385, -6), (key2475, -6), (key2475, -6), (key2475, -6)]

def rawRow9466 : Integer.Sparse Key := [(key2400, 6), (key2400, 6), (key2432, 6), (key2400, 6), (key2475, -6), (key2385, -6), (key2475, -6), (key2475, -6)]

def rawRow9467 : Integer.Sparse Key := [(key2400, 6), (key2432, 6), (key2400, 6), (key2400, 6), (key2475, -6), (key2475, -6), (key2385, -6), (key2475, -6)]

def rawRow9468 : Integer.Sparse Key := [(key2432, 6), (key2400, 6), (key2400, 6), (key2400, 6), (key2475, -6), (key2475, -6), (key2475, -6), (key2385, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9477 : Integer.Sparse Key := [(key995, 6), (key995, 6), (key995, 6), (key1011, 6), (key1067, -6), (key1146, -6), (key1146, -6), (key1146, -6)]

def rawRow9478 : Integer.Sparse Key := [(key995, 6), (key995, 6), (key1011, 6), (key995, 6), (key1146, -6), (key1067, -6), (key1146, -6), (key1146, -6)]

def rawRow9479 : Integer.Sparse Key := [(key995, 6), (key1011, 6), (key995, 6), (key995, 6), (key1146, -6), (key1146, -6), (key1067, -6), (key1146, -6)]

def rawRow9480 : Integer.Sparse Key := [(key1011, 6), (key995, 6), (key995, 6), (key995, 6), (key1146, -6), (key1146, -6), (key1146, -6), (key1067, -6)]

def rawRow9481 : Integer.Sparse Key := [(key1030, 6), (key1030, 6), (key1030, 6), (key1067, 6), (key1011, -6), (key1119, -6), (key1119, -6), (key1119, -6)]

def rawRow9482 : Integer.Sparse Key := [(key1030, 6), (key1030, 6), (key1067, 6), (key1030, 6), (key1119, -6), (key1011, -6), (key1119, -6), (key1119, -6)]

def rawRow9483 : Integer.Sparse Key := [(key1030, 6), (key1067, 6), (key1030, 6), (key1030, 6), (key1119, -6), (key1119, -6), (key1011, -6), (key1119, -6)]

def rawRow9484 : Integer.Sparse Key := [(key1067, 6), (key1030, 6), (key1030, 6), (key1030, 6), (key1119, -6), (key1119, -6), (key1119, -6), (key1011, -6)]

def rawRow9493 : Integer.Sparse Key := [(key2606, -6), (key2622, -6), (key2622, -6), (key2622, -6), (key2661, 6), (key2696, 6), (key2696, 6), (key2696, 6)]

def rawRow9494 : Integer.Sparse Key := [(key2622, -6), (key2606, -6), (key2622, -6), (key2622, -6), (key2696, 6), (key2661, 6), (key2696, 6), (key2696, 6)]

def rawRow9495 : Integer.Sparse Key := [(key2622, -6), (key2622, -6), (key2606, -6), (key2622, -6), (key2696, 6), (key2696, 6), (key2661, 6), (key2696, 6)]

def rawRow9496 : Integer.Sparse Key := [(key2622, -6), (key2622, -6), (key2622, -6), (key2606, -6), (key2696, 6), (key2696, 6), (key2696, 6), (key2661, 6)]

def rawRow9497 : Integer.Sparse Key := [(key2661, -6), (key2696, -6), (key2696, -6), (key2696, -6), (key2606, 6), (key2799, 6), (key2799, 6), (key2799, 6)]

def rawRow9498 : Integer.Sparse Key := [(key2696, -6), (key2661, -6), (key2696, -6), (key2696, -6), (key2799, 6), (key2606, 6), (key2799, 6), (key2799, 6)]

def rawRow9499 : Integer.Sparse Key := [(key2696, -6), (key2696, -6), (key2661, -6), (key2696, -6), (key2799, 6), (key2799, 6), (key2606, 6), (key2799, 6)]

def rawRow9500 : Integer.Sparse Key := [(key2696, -6), (key2696, -6), (key2696, -6), (key2661, -6), (key2799, 6), (key2799, 6), (key2799, 6), (key2606, 6)]

def rawRow9501 : Integer.Sparse Key := [(key2592, 2), (key2595, 2), (key2595, 2), (key2848, 2), (key2882, 2), (key2882, 2), (key2970, 2), (key2970, 2), (key2991, 2), (key2991, 2), (key2993, 2), (key2993, 2), (key2602, -2), (key2602, -2), (key2603, -2), (key2891, -2), (key2891, -2), (key2912, -2), (key2912, -2), (key2914, -2), (key2914, -2), (key2996, -2), (key3003, -2), (key3003, -2)]

def rawRow9502 : Integer.Sparse Key := [(key2595, 2), (key2592, 2), (key2595, 2), (key2882, 2), (key2848, 2), (key2882, 2), (key2991, 2), (key2993, 2), (key2970, 2), (key2993, 2), (key2970, 2), (key2991, 2), (key2602, -2), (key2603, -2), (key2602, -2), (key2912, -2), (key2914, -2), (key2891, -2), (key2914, -2), (key2891, -2), (key2912, -2), (key3003, -2), (key2996, -2), (key3003, -2)]

def rawRow9503 : Integer.Sparse Key := [(key2595, 2), (key2595, 2), (key2592, 2), (key2882, 2), (key2882, 2), (key2848, 2), (key2993, 2), (key2991, 2), (key2993, 2), (key2970, 2), (key2991, 2), (key2970, 2), (key2603, -2), (key2602, -2), (key2602, -2), (key2914, -2), (key2912, -2), (key2914, -2), (key2891, -2), (key2912, -2), (key2891, -2), (key3003, -2), (key3003, -2), (key2996, -2)]

def rawRow9504 : Integer.Sparse Key := [(key2848, 2), (key2970, 2), (key2970, 2), (key2592, 2), (key2991, 2), (key2991, 2), (key2595, 2), (key2595, 2), (key2882, 2), (key2882, 2), (key2993, 2), (key2993, 2), (key2891, -2), (key2891, -2), (key2996, -2), (key2602, -2), (key2602, -2), (key2912, -2), (key2912, -2), (key3003, -2), (key3003, -2), (key2603, -2), (key2914, -2), (key2914, -2)]

def rawRow9505 : Integer.Sparse Key := [(key2970, 2), (key2848, 2), (key2970, 2), (key2991, 2), (key2592, 2), (key2991, 2), (key2882, 2), (key2993, 2), (key2595, 2), (key2993, 2), (key2595, 2), (key2882, 2), (key2891, -2), (key2996, -2), (key2891, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2914, -2), (key2603, -2), (key2914, -2)]

def rawRow9506 : Integer.Sparse Key := [(key2970, 2), (key2970, 2), (key2848, 2), (key2991, 2), (key2991, 2), (key2592, 2), (key2993, 2), (key2882, 2), (key2993, 2), (key2595, 2), (key2882, 2), (key2595, 2), (key2996, -2), (key2891, -2), (key2891, -2), (key3003, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2602, -2), (key2914, -2), (key2914, -2), (key2603, -2)]

def rawRow9507 : Integer.Sparse Key := [(key2882, 2), (key2991, 2), (key2993, 2), (key2595, 2), (key2970, 2), (key2993, 2), (key2592, 2), (key2595, 2), (key2848, 2), (key2882, 2), (key2970, 2), (key2991, 2), (key2912, -2), (key2914, -2), (key3003, -2), (key2602, -2), (key2603, -2), (key2891, -2), (key2914, -2), (key2996, -2), (key3003, -2), (key2602, -2), (key2891, -2), (key2912, -2)]

def rawRow9508 : Integer.Sparse Key := [(key2882, 2), (key2993, 2), (key2991, 2), (key2595, 2), (key2993, 2), (key2970, 2), (key2595, 2), (key2592, 2), (key2882, 2), (key2848, 2), (key2991, 2), (key2970, 2), (key2914, -2), (key2912, -2), (key3003, -2), (key2603, -2), (key2602, -2), (key2914, -2), (key2891, -2), (key3003, -2), (key2996, -2), (key2602, -2), (key2912, -2), (key2891, -2)]

def rawRow9509 : Integer.Sparse Key := [(key2991, 2), (key2882, 2), (key2993, 2), (key2970, 2), (key2595, 2), (key2993, 2), (key2848, 2), (key2970, 2), (key2592, 2), (key2991, 2), (key2595, 2), (key2882, 2), (key2912, -2), (key3003, -2), (key2914, -2), (key2891, -2), (key2996, -2), (key2602, -2), (key3003, -2), (key2603, -2), (key2914, -2), (key2891, -2), (key2602, -2), (key2912, -2)]

def rawRow9510 : Integer.Sparse Key := [(key2991, 2), (key2993, 2), (key2882, 2), (key2970, 2), (key2993, 2), (key2595, 2), (key2970, 2), (key2848, 2), (key2991, 2), (key2592, 2), (key2882, 2), (key2595, 2), (key3003, -2), (key2912, -2), (key2914, -2), (key2996, -2), (key2891, -2), (key3003, -2), (key2602, -2), (key2914, -2), (key2603, -2), (key2891, -2), (key2912, -2), (key2602, -2)]

def rawRow9511 : Integer.Sparse Key := [(key2993, 2), (key2882, 2), (key2991, 2), (key2993, 2), (key2595, 2), (key2970, 2), (key2882, 2), (key2991, 2), (key2595, 2), (key2970, 2), (key2592, 2), (key2848, 2), (key2914, -2), (key3003, -2), (key2912, -2), (key2914, -2), (key3003, -2), (key2603, -2), (key2996, -2), (key2602, -2), (key2891, -2), (key2912, -2), (key2602, -2), (key2891, -2)]

def rawRow9512 : Integer.Sparse Key := [(key2993, 2), (key2991, 2), (key2882, 2), (key2993, 2), (key2970, 2), (key2595, 2), (key2991, 2), (key2882, 2), (key2970, 2), (key2595, 2), (key2848, 2), (key2592, 2), (key3003, -2), (key2914, -2), (key2912, -2), (key3003, -2), (key2914, -2), (key2996, -2), (key2603, -2), (key2891, -2), (key2602, -2), (key2912, -2), (key2891, -2), (key2602, -2)]

def rawRow9513 : Integer.Sparse Key := [(key2379, 2), (key2393, 2), (key2393, 2), (key2771, 2), (key2912, 2), (key2912, 2), (key2933, 2), (key2933, 2), (key2991, 2), (key2991, 2), (key3003, 2), (key3003, 2), (key2595, -2), (key2595, -2), (key2603, -2), (key2774, -2), (key2774, -2), (key2882, -2), (key2882, -2), (key2914, -2), (key2914, -2), (key2934, -2), (key2993, -2), (key2993, -2)]

def rawRow9514 : Integer.Sparse Key := [(key2393, 2), (key2379, 2), (key2393, 2), (key2912, 2), (key2771, 2), (key2912, 2), (key2991, 2), (key3003, 2), (key2933, 2), (key3003, 2), (key2933, 2), (key2991, 2), (key2595, -2), (key2603, -2), (key2595, -2), (key2882, -2), (key2914, -2), (key2774, -2), (key2914, -2), (key2774, -2), (key2882, -2), (key2993, -2), (key2934, -2), (key2993, -2)]

def rawRow9515 : Integer.Sparse Key := [(key2393, 2), (key2393, 2), (key2379, 2), (key2912, 2), (key2912, 2), (key2771, 2), (key3003, 2), (key2991, 2), (key3003, 2), (key2933, 2), (key2991, 2), (key2933, 2), (key2603, -2), (key2595, -2), (key2595, -2), (key2914, -2), (key2882, -2), (key2914, -2), (key2774, -2), (key2882, -2), (key2774, -2), (key2993, -2), (key2993, -2), (key2934, -2)]

def rawRow9516 : Integer.Sparse Key := [(key2407, 2), (key2441, 2), (key2441, 2), (key2592, 2), (key2991, 2), (key2991, 2), (key2602, 2), (key2602, 2), (key2912, 2), (key2912, 2), (key3003, 2), (key3003, 2), (key2774, -2), (key2774, -2), (key2934, -2), (key2595, -2), (key2595, -2), (key2882, -2), (key2882, -2), (key2993, -2), (key2993, -2), (key2603, -2), (key2914, -2), (key2914, -2)]

def rawRow9517 : Integer.Sparse Key := [(key2441, 2), (key2407, 2), (key2441, 2), (key2991, 2), (key2592, 2), (key2991, 2), (key2912, 2), (key3003, 2), (key2602, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key2774, -2), (key2934, -2), (key2774, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2914, -2), (key2603, -2), (key2914, -2)]

def rawRow9518 : Integer.Sparse Key := [(key2441, 2), (key2441, 2), (key2407, 2), (key2991, 2), (key2991, 2), (key2592, 2), (key3003, 2), (key2912, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key2602, 2), (key2934, -2), (key2774, -2), (key2774, -2), (key2993, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2595, -2), (key2914, -2), (key2914, -2), (key2603, -2)]

def rawRow9519 : Integer.Sparse Key := [(key2544, 2), (key2555, 2), (key2565, 2), (key2393, 2), (key2441, 2), (key2565, 2), (key2379, 2), (key2393, 2), (key2771, 2), (key2912, 2), (key2933, 2), (key2991, 2), (key2882, -2), (key2914, -2), (key2993, -2), (key2595, -2), (key2603, -2), (key2774, -2), (key2914, -2), (key2934, -2), (key2993, -2), (key2595, -2), (key2774, -2), (key2882, -2)]

def rawRow9520 : Integer.Sparse Key := [(key2544, 2), (key2565, 2), (key2555, 2), (key2393, 2), (key2565, 2), (key2441, 2), (key2393, 2), (key2379, 2), (key2912, 2), (key2771, 2), (key2991, 2), (key2933, 2), (key2914, -2), (key2882, -2), (key2993, -2), (key2603, -2), (key2595, -2), (key2914, -2), (key2774, -2), (key2993, -2), (key2934, -2), (key2595, -2), (key2882, -2), (key2774, -2)]

def rawRow9521 : Integer.Sparse Key := [(key2555, 2), (key2544, 2), (key2565, 2), (key2441, 2), (key2393, 2), (key2565, 2), (key2407, 2), (key2441, 2), (key2592, 2), (key2991, 2), (key2602, 2), (key2912, 2), (key2882, -2), (key2993, -2), (key2914, -2), (key2774, -2), (key2934, -2), (key2595, -2), (key2993, -2), (key2603, -2), (key2914, -2), (key2774, -2), (key2595, -2), (key2882, -2)]

def rawRow9522 : Integer.Sparse Key := [(key2555, 2), (key2565, 2), (key2544, 2), (key2441, 2), (key2565, 2), (key2393, 2), (key2441, 2), (key2407, 2), (key2991, 2), (key2592, 2), (key2912, 2), (key2602, 2), (key2993, -2), (key2882, -2), (key2914, -2), (key2934, -2), (key2774, -2), (key2993, -2), (key2595, -2), (key2914, -2), (key2603, -2), (key2774, -2), (key2882, -2), (key2595, -2)]

def rawRow9523 : Integer.Sparse Key := [(key2565, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2393, 2), (key2441, 2), (key2544, 2), (key2555, 2), (key2393, 2), (key2441, 2), (key2379, 2), (key2771, 2), (key2914, -2), (key2993, -2), (key2882, -2), (key2914, -2), (key2993, -2), (key2603, -2), (key2934, -2), (key2595, -2), (key2774, -2), (key2882, -2), (key2595, -2), (key2774, -2)]

def rawRow9524 : Integer.Sparse Key := [(key2565, 2), (key2555, 2), (key2544, 2), (key2565, 2), (key2441, 2), (key2393, 2), (key2555, 2), (key2544, 2), (key2441, 2), (key2393, 2), (key2407, 2), (key2592, 2), (key2993, -2), (key2914, -2), (key2882, -2), (key2993, -2), (key2914, -2), (key2934, -2), (key2603, -2), (key2774, -2), (key2595, -2), (key2882, -2), (key2774, -2), (key2595, -2)]

def rawRow9597 : Integer.Sparse Key := [(key2402, -6), (key2402, -6), (key2408, -6), (key2439, -6), (key2591, 2), (key2591, 2), (key2596, 2), (key2847, 2), (key2847, 2), (key2878, 2), (key2878, 2), (key2884, 2), (key2884, 2), (key3020, 2), (key3029, 2), (key3029, 2)]

def rawRow9598 : Integer.Sparse Key := [(key2402, -6), (key2408, -6), (key2402, -6), (key2439, -6), (key2591, 2), (key2596, 2), (key2591, 2), (key2878, 2), (key2884, 2), (key2847, 2), (key2884, 2), (key2847, 2), (key2878, 2), (key3029, 2), (key3020, 2), (key3029, 2)]

def rawRow9599 : Integer.Sparse Key := [(key2408, -6), (key2402, -6), (key2402, -6), (key2439, -6), (key2596, 2), (key2591, 2), (key2591, 2), (key2884, 2), (key2878, 2), (key2884, 2), (key2847, 2), (key2878, 2), (key2847, 2), (key3029, 2), (key3029, 2), (key3020, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9600 : Integer.Sparse Key := [(key2402, -6), (key2402, -6), (key2439, -6), (key2408, -6), (key2847, 2), (key2847, 2), (key3020, 2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key3029, 2), (key3029, 2), (key2596, 2), (key2884, 2), (key2884, 2)]

def rawRow9601 : Integer.Sparse Key := [(key2402, -6), (key2439, -6), (key2402, -6), (key2408, -6), (key2847, 2), (key3020, 2), (key2847, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2884, 2), (key2596, 2), (key2884, 2)]

def rawRow9602 : Integer.Sparse Key := [(key2439, -6), (key2402, -6), (key2402, -6), (key2408, -6), (key3020, 2), (key2847, 2), (key2847, 2), (key3029, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2884, 2), (key2884, 2), (key2596, 2)]

def rawRow9603 : Integer.Sparse Key := [(key2402, -6), (key2408, -6), (key2439, -6), (key2402, -6), (key2878, 2), (key2884, 2), (key3029, 2), (key2591, 2), (key2596, 2), (key2847, 2), (key2884, 2), (key3020, 2), (key3029, 2), (key2591, 2), (key2847, 2), (key2878, 2)]

def rawRow9604 : Integer.Sparse Key := [(key2408, -6), (key2402, -6), (key2439, -6), (key2402, -6), (key2884, 2), (key2878, 2), (key3029, 2), (key2596, 2), (key2591, 2), (key2884, 2), (key2847, 2), (key3029, 2), (key3020, 2), (key2591, 2), (key2878, 2), (key2847, 2)]

def rawRow9605 : Integer.Sparse Key := [(key2402, -6), (key2439, -6), (key2408, -6), (key2402, -6), (key2878, 2), (key3029, 2), (key2884, 2), (key2847, 2), (key3020, 2), (key2591, 2), (key3029, 2), (key2596, 2), (key2884, 2), (key2847, 2), (key2591, 2), (key2878, 2)]

def rawRow9606 : Integer.Sparse Key := [(key2439, -6), (key2402, -6), (key2408, -6), (key2402, -6), (key3029, 2), (key2878, 2), (key2884, 2), (key3020, 2), (key2847, 2), (key3029, 2), (key2591, 2), (key2884, 2), (key2596, 2), (key2847, 2), (key2878, 2), (key2591, 2)]

def rawRow9607 : Integer.Sparse Key := [(key2408, -6), (key2439, -6), (key2402, -6), (key2402, -6), (key2884, 2), (key3029, 2), (key2878, 2), (key2884, 2), (key3029, 2), (key2596, 2), (key3020, 2), (key2591, 2), (key2847, 2), (key2878, 2), (key2591, 2), (key2847, 2)]

def rawRow9608 : Integer.Sparse Key := [(key2439, -6), (key2408, -6), (key2402, -6), (key2402, -6), (key3029, 2), (key2884, 2), (key2878, 2), (key3029, 2), (key2884, 2), (key3020, 2), (key2596, 2), (key2847, 2), (key2591, 2), (key2878, 2), (key2847, 2), (key2591, 2)]

def rawRow9609 : Integer.Sparse Key := [(key2468, -6), (key2468, -6), (key2481, -6), (key2505, -6), (key2374, 2), (key2374, 2), (key2391, 2), (key2770, 2), (key2770, 2), (key2878, 2), (key2878, 2), (key2926, 2), (key2926, 2), (key3006, 2), (key3029, 2), (key3029, 2)]

def rawRow9610 : Integer.Sparse Key := [(key2468, -6), (key2481, -6), (key2468, -6), (key2505, -6), (key2374, 2), (key2391, 2), (key2374, 2), (key2878, 2), (key2926, 2), (key2770, 2), (key2926, 2), (key2770, 2), (key2878, 2), (key3029, 2), (key3006, 2), (key3029, 2)]

def rawRow9611 : Integer.Sparse Key := [(key2481, -6), (key2468, -6), (key2468, -6), (key2505, -6), (key2391, 2), (key2374, 2), (key2374, 2), (key2926, 2), (key2878, 2), (key2926, 2), (key2770, 2), (key2878, 2), (key2770, 2), (key3029, 2), (key3029, 2), (key3006, 2)]

def rawRow9612 : Integer.Sparse Key := [(key2468, -6), (key2468, -6), (key2505, -6), (key2481, -6), (key2402, 2), (key2402, 2), (key2439, 2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key3029, 2), (key3029, 2), (key2605, 2), (key2926, 2), (key2926, 2)]

def rawRow9613 : Integer.Sparse Key := [(key2468, -6), (key2505, -6), (key2468, -6), (key2481, -6), (key2402, 2), (key2439, 2), (key2402, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2926, 2), (key2605, 2), (key2926, 2)]

def rawRow9614 : Integer.Sparse Key := [(key2505, -6), (key2468, -6), (key2468, -6), (key2481, -6), (key2439, 2), (key2402, 2), (key2402, 2), (key3029, 2), (key2878, 2), (key3029, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2926, 2), (key2926, 2), (key2605, 2)]

def rawRow9615 : Integer.Sparse Key := [(key2468, -6), (key2481, -6), (key2505, -6), (key2468, -6), (key2535, 2), (key2542, 2), (key2553, 2), (key2374, 2), (key2391, 2), (key2402, 2), (key2542, 2), (key2439, 2), (key2553, 2), (key2591, 2), (key2770, 2), (key2878, 2)]

def rawRow9616 : Integer.Sparse Key := [(key2481, -6), (key2468, -6), (key2505, -6), (key2468, -6), (key2542, 2), (key2535, 2), (key2553, 2), (key2391, 2), (key2374, 2), (key2542, 2), (key2402, 2), (key2553, 2), (key2439, 2), (key2591, 2), (key2878, 2), (key2770, 2)]

def rawRow9617 : Integer.Sparse Key := [(key2468, -6), (key2505, -6), (key2481, -6), (key2468, -6), (key2535, 2), (key2553, 2), (key2542, 2), (key2402, 2), (key2439, 2), (key2374, 2), (key2553, 2), (key2391, 2), (key2542, 2), (key2770, 2), (key2591, 2), (key2878, 2)]

def rawRow9618 : Integer.Sparse Key := [(key2505, -6), (key2468, -6), (key2481, -6), (key2468, -6), (key2553, 2), (key2535, 2), (key2542, 2), (key2439, 2), (key2402, 2), (key2553, 2), (key2374, 2), (key2542, 2), (key2391, 2), (key2770, 2), (key2878, 2), (key2591, 2)]

def rawRow9619 : Integer.Sparse Key := [(key2481, -6), (key2505, -6), (key2468, -6), (key2468, -6), (key2542, 2), (key2553, 2), (key2535, 2), (key2542, 2), (key2553, 2), (key2391, 2), (key2439, 2), (key2374, 2), (key2402, 2), (key2878, 2), (key2591, 2), (key2770, 2)]

def rawRow9620 : Integer.Sparse Key := [(key2505, -6), (key2481, -6), (key2468, -6), (key2468, -6), (key2553, 2), (key2542, 2), (key2535, 2), (key2553, 2), (key2542, 2), (key2439, 2), (key2391, 2), (key2402, 2), (key2374, 2), (key2878, 2), (key2770, 2), (key2591, 2)]

def rawRow9621 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2809, -2), (key2809, -2), (key2829, -2), (key2829, -2), (key2835, -2), (key2835, -2), (key3012, -2), (key3017, -2), (key3017, -2), (key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2644, 1), (key2644, 1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2732, 1), (key2732, 1), (key2860, 1), (key2860, 1), (key2870, 1), (key2870, 1), (key2885, 1), (key2885, 1), (key3023, 1), (key3023, 1), (key3026, 1), (key3026, 1), (key3030, 1), (key3030, 1)]

def rawRow9622 : Integer.Sparse Key := [(key2612, -2), (key2618, -2), (key2616, -2), (key2829, -2), (key2835, -2), (key2809, -2), (key2835, -2), (key2809, -2), (key2829, -2), (key3017, -2), (key3012, -2), (key3017, -2), (key2640, 1), (key2644, 1), (key2632, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2870, 1), (key2885, 1), (key2860, 1), (key2885, 1), (key2860, 1), (key2870, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3030, 1), (key3023, 1), (key3026, 1)]

def rawRow9623 : Integer.Sparse Key := [(key2618, -2), (key2612, -2), (key2616, -2), (key2835, -2), (key2829, -2), (key2835, -2), (key2809, -2), (key2829, -2), (key2809, -2), (key3017, -2), (key3017, -2), (key3012, -2), (key2644, 1), (key2640, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2632, 1), (key2732, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2706, 1), (key2885, 1), (key2870, 1), (key2885, 1), (key2860, 1), (key2870, 1), (key2860, 1), (key3030, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3026, 1), (key3023, 1)]

def rawRow9624 : Integer.Sparse Key := [(key2805, -2), (key2805, -2), (key2831, -2), (key2612, -2), (key2616, -2), (key2829, -2), (key2829, -2), (key3017, -2), (key3017, -2), (key2621, -2), (key2835, -2), (key2835, -2), (key2706, 1), (key2706, 1), (key2860, 1), (key2860, 1), (key3023, 1), (key3023, 1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1), (key2640, 1), (key2640, 1), (key2726, 1), (key2726, 1), (key3030, 1), (key3030, 1), (key2644, 1), (key2644, 1), (key2732, 1), (key2732, 1), (key2885, 1), (key2885, 1)]

def rawRow9625 : Integer.Sparse Key := [(key2805, -2), (key2831, -2), (key2805, -2), (key2948, -2), (key2960, -2), (key2612, -2), (key2960, -2), (key2616, -2), (key2829, -2), (key2835, -2), (key2621, -2), (key2835, -2), (key2860, 1), (key3023, 1), (key2706, 1), (key3023, 1), (key2706, 1), (key2860, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2885, 1), (key2644, 1), (key2732, 1)]

def rawRow9626 : Integer.Sparse Key := [(key2831, -2), (key2805, -2), (key2805, -2), (key2960, -2), (key2948, -2), (key2960, -2), (key2612, -2), (key2829, -2), (key2616, -2), (key2835, -2), (key2835, -2), (key2621, -2), (key3023, 1), (key2860, 1), (key3023, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key3030, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2640, 1), (key2885, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2732, 1), (key2644, 1)]

def rawRow9627 : Integer.Sparse Key := [(key2948, -2), (key2950, -2), (key2960, -2), (key2612, -2), (key2618, -2), (key2805, -2), (key2950, -2), (key2831, -2), (key2960, -2), (key2616, -2), (key2809, -2), (key2829, -2), (key2726, 1), (key2732, 1), (key2870, 1), (key2885, 1), (key3026, 1), (key3030, 1), (key2640, 1), (key2644, 1), (key2860, 1), (key2885, 1), (key3023, 1), (key3030, 1), (key2632, 1), (key2644, 1), (key2706, 1), (key2732, 1), (key3023, 1), (key3026, 1), (key2632, 1), (key2640, 1), (key2706, 1), (key2726, 1), (key2860, 1), (key2870, 1)]

def rawRow9628 : Integer.Sparse Key := [(key2950, -2), (key2948, -2), (key2960, -2), (key2618, -2), (key2612, -2), (key2950, -2), (key2805, -2), (key2960, -2), (key2831, -2), (key2616, -2), (key2829, -2), (key2809, -2), (key2732, 1), (key2726, 1), (key2885, 1), (key2870, 1), (key3030, 1), (key3026, 1), (key2644, 1), (key2640, 1), (key2885, 1), (key2860, 1), (key3030, 1), (key3023, 1), (key2644, 1), (key2632, 1), (key2732, 1), (key2706, 1), (key3026, 1), (key3023, 1), (key2640, 1), (key2632, 1), (key2726, 1), (key2706, 1), (key2870, 1), (key2860, 1)]

def rawRow9629 : Integer.Sparse Key := [(key2948, -2), (key2960, -2), (key2950, -2), (key2805, -2), (key2831, -2), (key2612, -2), (key2960, -2), (key2618, -2), (key2950, -2), (key2809, -2), (key2616, -2), (key2829, -2), (key2870, 1), (key3026, 1), (key2726, 1), (key3030, 1), (key2732, 1), (key2885, 1), (key2860, 1), (key3023, 1), (key2640, 1), (key3030, 1), (key2644, 1), (key2885, 1), (key2706, 1), (key3023, 1), (key2632, 1), (key3026, 1), (key2644, 1), (key2732, 1), (key2706, 1), (key2860, 1), (key2632, 1), (key2870, 1), (key2640, 1), (key2726, 1)]

def rawRow9630 : Integer.Sparse Key := [(key2960, -2), (key2948, -2), (key2950, -2), (key2831, -2), (key2805, -2), (key2960, -2), (key2612, -2), (key2950, -2), (key2618, -2), (key2809, -2), (key2829, -2), (key2616, -2), (key3026, 1), (key2870, 1), (key3030, 1), (key2726, 1), (key2885, 1), (key2732, 1), (key3023, 1), (key2860, 1), (key3030, 1), (key2640, 1), (key2885, 1), (key2644, 1), (key3023, 1), (key2706, 1), (key3026, 1), (key2632, 1), (key2732, 1), (key2644, 1), (key2860, 1), (key2706, 1), (key2870, 1), (key2632, 1), (key2726, 1), (key2640, 1)]

def rawRow9631 : Integer.Sparse Key := [(key2950, -2), (key2960, -2), (key2948, -2), (key2950, -2), (key2960, -2), (key2618, -2), (key2831, -2), (key2612, -2), (key2805, -2), (key2829, -2), (key2616, -2), (key2809, -2), (key2885, 1), (key3030, 1), (key2732, 1), (key3026, 1), (key2726, 1), (key2870, 1), (key2885, 1), (key3030, 1), (key2644, 1), (key3023, 1), (key2640, 1), (key2860, 1), (key2732, 1), (key3026, 1), (key2644, 1), (key3023, 1), (key2632, 1), (key2706, 1), (key2726, 1), (key2870, 1), (key2640, 1), (key2860, 1), (key2632, 1), (key2706, 1)]

def rawRow9632 : Integer.Sparse Key := [(key2960, -2), (key2950, -2), (key2948, -2), (key2960, -2), (key2950, -2), (key2831, -2), (key2618, -2), (key2805, -2), (key2612, -2), (key2829, -2), (key2809, -2), (key2616, -2), (key3030, 1), (key2885, 1), (key3026, 1), (key2732, 1), (key2870, 1), (key2726, 1), (key3030, 1), (key2885, 1), (key3023, 1), (key2644, 1), (key2860, 1), (key2640, 1), (key3026, 1), (key2732, 1), (key3023, 1), (key2644, 1), (key2706, 1), (key2632, 1), (key2870, 1), (key2726, 1), (key2860, 1), (key2640, 1), (key2706, 1), (key2632, 1)]

def rawRow9633 : Integer.Sparse Key := [(key2628, -2), (key2628, -2), (key2641, -2), (key2702, -2), (key2702, -2), (key2972, -2), (key2972, -2), (key2976, -2), (key2976, -2), (key2728, -2), (key2983, -2), (key2983, -2), (key2612, 1), (key2616, 1), (key2640, 1), (key2640, 1), (key2660, 1), (key2660, 1), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2758, 1), (key2758, 1), (key2794, 1), (key2794, 1), (key2829, 1), (key2829, 1), (key2927, 1), (key2927, 1), (key3010, 1), (key3010, 1), (key3017, 1), (key3017, 1), (key3030, 1), (key3030, 1)]

def rawRow9634 : Integer.Sparse Key := [(key2628, -2), (key2641, -2), (key2628, -2), (key2972, -2), (key2976, -2), (key2702, -2), (key2976, -2), (key2702, -2), (key2972, -2), (key2983, -2), (key2728, -2), (key2983, -2), (key2646, 1), (key2653, 1), (key2612, 1), (key2653, 1), (key2616, 1), (key2640, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2829, 1), (key2927, 1), (key2794, 1), (key2927, 1), (key2794, 1), (key2829, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3030, 1), (key3010, 1), (key3017, 1)]

def rawRow9635 : Integer.Sparse Key := [(key2641, -2), (key2628, -2), (key2628, -2), (key2976, -2), (key2972, -2), (key2976, -2), (key2702, -2), (key2972, -2), (key2702, -2), (key2983, -2), (key2983, -2), (key2728, -2), (key2653, 1), (key2646, 1), (key2653, 1), (key2612, 1), (key2640, 1), (key2616, 1), (key2758, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2927, 1), (key2829, 1), (key2927, 1), (key2794, 1), (key2829, 1), (key2794, 1), (key3030, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3017, 1), (key3010, 1)]

def rawRow9636 : Integer.Sparse Key := [(key2702, -2), (key2702, -2), (key2728, -2), (key2628, -2), (key2628, -2), (key2972, -2), (key2972, -2), (key2983, -2), (key2983, -2), (key2641, -2), (key2976, -2), (key2976, -2), (key2667, 1), (key2667, 1), (key2735, 1), (key2735, 1), (key2747, 1), (key2747, 1), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2640, 1), (key2640, 1), (key2726, 1), (key2726, 1), (key3030, 1), (key3030, 1), (key2660, 1), (key2660, 1), (key2758, 1), (key2758, 1), (key2927, 1), (key2927, 1)]

def rawRow9637 : Integer.Sparse Key := [(key2702, -2), (key2728, -2), (key2702, -2), (key2972, -2), (key2983, -2), (key2628, -2), (key2983, -2), (key2628, -2), (key2972, -2), (key2976, -2), (key2641, -2), (key2976, -2), (key2735, 1), (key2747, 1), (key2667, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2927, 1), (key2660, 1), (key2758, 1)]

def rawRow9638 : Integer.Sparse Key := [(key2728, -2), (key2702, -2), (key2702, -2), (key2983, -2), (key2972, -2), (key2983, -2), (key2628, -2), (key2972, -2), (key2628, -2), (key2976, -2), (key2976, -2), (key2641, -2), (key2747, 1), (key2735, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2667, 1), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key3030, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2640, 1), (key2927, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2758, 1), (key2660, 1)]

def rawRow9639 : Integer.Sparse Key := [(key2972, -2), (key2976, -2), (key2983, -2), (key2628, -2), (key2641, -2), (key2702, -2), (key2976, -2), (key2728, -2), (key2983, -2), (key2628, -2), (key2702, -2), (key2972, -2), (key2936, 1), (key2943, 1), (key2948, 1), (key2998, 1), (key2960, 1), (key3000, 1), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1), (key2612, 1), (key2653, 1), (key2667, 1), (key2943, 1), (key2747, 1), (key2960, 1), (key2616, 1), (key2640, 1), (key2671, 1), (key2726, 1), (key2794, 1), (key2829, 1)]

def rawRow9640 : Integer.Sparse Key := [(key2976, -2), (key2972, -2), (key2983, -2), (key2641, -2), (key2628, -2), (key2976, -2), (key2702, -2), (key2983, -2), (key2728, -2), (key2628, -2), (key2972, -2), (key2702, -2), (key2943, 1), (key2936, 1), (key2998, 1), (key2948, 1), (key3000, 1), (key2960, 1), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1), (key2653, 1), (key2612, 1), (key2943, 1), (key2667, 1), (key2960, 1), (key2747, 1), (key2640, 1), (key2616, 1), (key2726, 1), (key2671, 1), (key2829, 1), (key2794, 1)]

def rawRow9641 : Integer.Sparse Key := [(key2972, -2), (key2983, -2), (key2976, -2), (key2702, -2), (key2728, -2), (key2628, -2), (key2983, -2), (key2641, -2), (key2976, -2), (key2702, -2), (key2628, -2), (key2972, -2), (key2948, 1), (key2960, 1), (key2936, 1), (key3000, 1), (key2943, 1), (key2998, 1), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2667, 1), (key2747, 1), (key2612, 1), (key2960, 1), (key2653, 1), (key2943, 1), (key2671, 1), (key2794, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2726, 1)]

def rawRow9642 : Integer.Sparse Key := [(key2983, -2), (key2972, -2), (key2976, -2), (key2728, -2), (key2702, -2), (key2983, -2), (key2628, -2), (key2976, -2), (key2641, -2), (key2702, -2), (key2972, -2), (key2628, -2), (key2960, 1), (key2948, 1), (key3000, 1), (key2936, 1), (key2998, 1), (key2943, 1), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1), (key2747, 1), (key2667, 1), (key2960, 1), (key2612, 1), (key2943, 1), (key2653, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2726, 1), (key2640, 1)]

def rawRow9643 : Integer.Sparse Key := [(key2976, -2), (key2983, -2), (key2972, -2), (key2976, -2), (key2983, -2), (key2641, -2), (key2728, -2), (key2628, -2), (key2702, -2), (key2972, -2), (key2628, -2), (key2702, -2), (key2998, 1), (key3000, 1), (key2943, 1), (key2960, 1), (key2936, 1), (key2948, 1), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1), (key2943, 1), (key2960, 1), (key2653, 1), (key2747, 1), (key2612, 1), (key2667, 1), (key2726, 1), (key2829, 1), (key2640, 1), (key2794, 1), (key2616, 1), (key2671, 1)]

def rawRow9644 : Integer.Sparse Key := [(key2983, -2), (key2976, -2), (key2972, -2), (key2983, -2), (key2976, -2), (key2728, -2), (key2641, -2), (key2702, -2), (key2628, -2), (key2972, -2), (key2702, -2), (key2628, -2), (key3000, 1), (key2998, 1), (key2960, 1), (key2943, 1), (key2948, 1), (key2936, 1), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1), (key2960, 1), (key2943, 1), (key2747, 1), (key2653, 1), (key2667, 1), (key2612, 1), (key2829, 1), (key2726, 1), (key2794, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

def rawRow9669 : Integer.Sparse Key := [(key2667, -2), (key2667, -2), (key2673, -2), (key2702, -2), (key2702, -2), (key2735, -2), (key2735, -2), (key2737, -2), (key2737, -2), (key2728, -2), (key2747, -2), (key2747, -2), (key2612, 2), (key2616, 2), (key2621, 2), (key2809, 2), (key2809, 2), (key2829, 2), (key2829, 2), (key2835, 2), (key2835, 2), (key3012, 2), (key3017, 2), (key3017, 2)]

def rawRow9670 : Integer.Sparse Key := [(key2667, -2), (key2673, -2), (key2667, -2), (key2735, -2), (key2737, -2), (key2702, -2), (key2737, -2), (key2702, -2), (key2735, -2), (key2747, -2), (key2728, -2), (key2747, -2), (key2612, 2), (key2618, 2), (key2616, 2), (key2829, 2), (key2835, 2), (key2809, 2), (key2835, 2), (key2809, 2), (key2829, 2), (key3017, 2), (key3012, 2), (key3017, 2)]

def rawRow9671 : Integer.Sparse Key := [(key2673, -2), (key2667, -2), (key2667, -2), (key2737, -2), (key2735, -2), (key2737, -2), (key2702, -2), (key2735, -2), (key2702, -2), (key2747, -2), (key2747, -2), (key2728, -2), (key2618, 2), (key2612, 2), (key2616, 2), (key2835, 2), (key2829, 2), (key2835, 2), (key2809, 2), (key2829, 2), (key2809, 2), (key3017, 2), (key3017, 2), (key3012, 2)]

def rawRow9672 : Integer.Sparse Key := [(key2702, -2), (key2702, -2), (key2728, -2), (key2667, -2), (key2667, -2), (key2735, -2), (key2735, -2), (key2747, -2), (key2747, -2), (key2673, -2), (key2737, -2), (key2737, -2), (key2805, 2), (key2805, 2), (key2831, 2), (key2612, 2), (key2616, 2), (key2829, 2), (key2829, 2), (key3017, 2), (key3017, 2), (key2621, 2), (key2835, 2), (key2835, 2)]

def rawRow9673 : Integer.Sparse Key := [(key2702, -2), (key2728, -2), (key2702, -2), (key2735, -2), (key2747, -2), (key2667, -2), (key2747, -2), (key2667, -2), (key2735, -2), (key2737, -2), (key2673, -2), (key2737, -2), (key2805, 2), (key2831, 2), (key2805, 2), (key2948, 2), (key2960, 2), (key2612, 2), (key2960, 2), (key2616, 2), (key2829, 2), (key2835, 2), (key2621, 2), (key2835, 2)]

def rawRow9674 : Integer.Sparse Key := [(key2728, -2), (key2702, -2), (key2702, -2), (key2747, -2), (key2735, -2), (key2747, -2), (key2667, -2), (key2735, -2), (key2667, -2), (key2737, -2), (key2737, -2), (key2673, -2), (key2831, 2), (key2805, 2), (key2805, 2), (key2960, 2), (key2948, 2), (key2960, 2), (key2612, 2), (key2829, 2), (key2616, 2), (key2835, 2), (key2835, 2), (key2621, 2)]

def rawRow9675 : Integer.Sparse Key := [(key2735, -2), (key2737, -2), (key2747, -2), (key2667, -2), (key2673, -2), (key2702, -2), (key2737, -2), (key2728, -2), (key2747, -2), (key2667, -2), (key2702, -2), (key2735, -2), (key2948, 2), (key2950, 2), (key2960, 2), (key2612, 2), (key2618, 2), (key2805, 2), (key2950, 2), (key2831, 2), (key2960, 2), (key2616, 2), (key2809, 2), (key2829, 2)]

def rawRow9676 : Integer.Sparse Key := [(key2737, -2), (key2735, -2), (key2747, -2), (key2673, -2), (key2667, -2), (key2737, -2), (key2702, -2), (key2747, -2), (key2728, -2), (key2667, -2), (key2735, -2), (key2702, -2), (key2950, 2), (key2948, 2), (key2960, 2), (key2618, 2), (key2612, 2), (key2950, 2), (key2805, 2), (key2960, 2), (key2831, 2), (key2616, 2), (key2829, 2), (key2809, 2)]

def rawRow9677 : Integer.Sparse Key := [(key2735, -2), (key2747, -2), (key2737, -2), (key2702, -2), (key2728, -2), (key2667, -2), (key2747, -2), (key2673, -2), (key2737, -2), (key2702, -2), (key2667, -2), (key2735, -2), (key2948, 2), (key2960, 2), (key2950, 2), (key2805, 2), (key2831, 2), (key2612, 2), (key2960, 2), (key2618, 2), (key2950, 2), (key2809, 2), (key2616, 2), (key2829, 2)]

def rawRow9678 : Integer.Sparse Key := [(key2747, -2), (key2735, -2), (key2737, -2), (key2728, -2), (key2702, -2), (key2747, -2), (key2667, -2), (key2737, -2), (key2673, -2), (key2702, -2), (key2735, -2), (key2667, -2), (key2960, 2), (key2948, 2), (key2950, 2), (key2831, 2), (key2805, 2), (key2960, 2), (key2612, 2), (key2950, 2), (key2618, 2), (key2809, 2), (key2829, 2), (key2616, 2)]

def rawRow9679 : Integer.Sparse Key := [(key2737, -2), (key2747, -2), (key2735, -2), (key2737, -2), (key2747, -2), (key2673, -2), (key2728, -2), (key2667, -2), (key2702, -2), (key2735, -2), (key2667, -2), (key2702, -2), (key2950, 2), (key2960, 2), (key2948, 2), (key2950, 2), (key2960, 2), (key2618, 2), (key2831, 2), (key2612, 2), (key2805, 2), (key2829, 2), (key2616, 2), (key2809, 2)]

def rawRow9680 : Integer.Sparse Key := [(key2747, -2), (key2737, -2), (key2735, -2), (key2747, -2), (key2737, -2), (key2728, -2), (key2673, -2), (key2702, -2), (key2667, -2), (key2735, -2), (key2702, -2), (key2667, -2), (key2960, 2), (key2950, 2), (key2948, 2), (key2960, 2), (key2950, 2), (key2831, 2), (key2618, 2), (key2805, 2), (key2612, 2), (key2829, 2), (key2809, 2), (key2616, 2)]

def rawRow9681 : Integer.Sparse Key := [(key2782, -2), (key2782, -2), (key2795, -2), (key2805, -2), (key2805, -2), (key2893, -2), (key2893, -2), (key2897, -2), (key2897, -2), (key2831, -2), (key2904, -2), (key2904, -2), (key2628, 2), (key2628, 2), (key2641, 2), (key2702, 2), (key2702, 2), (key2972, 2), (key2972, 2), (key2976, 2), (key2976, 2), (key2728, 2), (key2983, 2), (key2983, 2)]

def rawRow9682 : Integer.Sparse Key := [(key2782, -2), (key2795, -2), (key2782, -2), (key2893, -2), (key2897, -2), (key2805, -2), (key2897, -2), (key2805, -2), (key2893, -2), (key2904, -2), (key2831, -2), (key2904, -2), (key2628, 2), (key2641, 2), (key2628, 2), (key2972, 2), (key2976, 2), (key2702, 2), (key2976, 2), (key2702, 2), (key2972, 2), (key2983, 2), (key2728, 2), (key2983, 2)]

def rawRow9683 : Integer.Sparse Key := [(key2795, -2), (key2782, -2), (key2782, -2), (key2897, -2), (key2893, -2), (key2897, -2), (key2805, -2), (key2893, -2), (key2805, -2), (key2904, -2), (key2904, -2), (key2831, -2), (key2641, 2), (key2628, 2), (key2628, 2), (key2976, 2), (key2972, 2), (key2976, 2), (key2702, 2), (key2972, 2), (key2702, 2), (key2983, 2), (key2983, 2), (key2728, 2)]

def rawRow9684 : Integer.Sparse Key := [(key2805, -2), (key2805, -2), (key2831, -2), (key2782, -2), (key2782, -2), (key2893, -2), (key2893, -2), (key2904, -2), (key2904, -2), (key2795, -2), (key2897, -2), (key2897, -2), (key2702, 2), (key2702, 2), (key2728, 2), (key2628, 2), (key2628, 2), (key2972, 2), (key2972, 2), (key2983, 2), (key2983, 2), (key2641, 2), (key2976, 2), (key2976, 2)]

def rawRow9685 : Integer.Sparse Key := [(key2805, -2), (key2831, -2), (key2805, -2), (key2893, -2), (key2904, -2), (key2782, -2), (key2904, -2), (key2782, -2), (key2893, -2), (key2897, -2), (key2795, -2), (key2897, -2), (key2702, 2), (key2728, 2), (key2702, 2), (key2972, 2), (key2983, 2), (key2628, 2), (key2983, 2), (key2628, 2), (key2972, 2), (key2976, 2), (key2641, 2), (key2976, 2)]

def rawRow9686 : Integer.Sparse Key := [(key2831, -2), (key2805, -2), (key2805, -2), (key2904, -2), (key2893, -2), (key2904, -2), (key2782, -2), (key2893, -2), (key2782, -2), (key2897, -2), (key2897, -2), (key2795, -2), (key2728, 2), (key2702, 2), (key2702, 2), (key2983, 2), (key2972, 2), (key2983, 2), (key2628, 2), (key2972, 2), (key2628, 2), (key2976, 2), (key2976, 2), (key2641, 2)]

def rawRow9687 : Integer.Sparse Key := [(key2893, -2), (key2897, -2), (key2904, -2), (key2782, -2), (key2795, -2), (key2805, -2), (key2897, -2), (key2831, -2), (key2904, -2), (key2782, -2), (key2805, -2), (key2893, -2), (key2972, 2), (key2976, 2), (key2983, 2), (key2628, 2), (key2641, 2), (key2702, 2), (key2976, 2), (key2728, 2), (key2983, 2), (key2628, 2), (key2702, 2), (key2972, 2)]

def rawRow9688 : Integer.Sparse Key := [(key2897, -2), (key2893, -2), (key2904, -2), (key2795, -2), (key2782, -2), (key2897, -2), (key2805, -2), (key2904, -2), (key2831, -2), (key2782, -2), (key2893, -2), (key2805, -2), (key2976, 2), (key2972, 2), (key2983, 2), (key2641, 2), (key2628, 2), (key2976, 2), (key2702, 2), (key2983, 2), (key2728, 2), (key2628, 2), (key2972, 2), (key2702, 2)]

def rawRow9689 : Integer.Sparse Key := [(key2893, -2), (key2904, -2), (key2897, -2), (key2805, -2), (key2831, -2), (key2782, -2), (key2904, -2), (key2795, -2), (key2897, -2), (key2805, -2), (key2782, -2), (key2893, -2), (key2972, 2), (key2983, 2), (key2976, 2), (key2702, 2), (key2728, 2), (key2628, 2), (key2983, 2), (key2641, 2), (key2976, 2), (key2702, 2), (key2628, 2), (key2972, 2)]

def rawRow9690 : Integer.Sparse Key := [(key2904, -2), (key2893, -2), (key2897, -2), (key2831, -2), (key2805, -2), (key2904, -2), (key2782, -2), (key2897, -2), (key2795, -2), (key2805, -2), (key2893, -2), (key2782, -2), (key2983, 2), (key2972, 2), (key2976, 2), (key2728, 2), (key2702, 2), (key2983, 2), (key2628, 2), (key2976, 2), (key2641, 2), (key2702, 2), (key2972, 2), (key2628, 2)]

def rawRow9691 : Integer.Sparse Key := [(key2897, -2), (key2904, -2), (key2893, -2), (key2897, -2), (key2904, -2), (key2795, -2), (key2831, -2), (key2782, -2), (key2805, -2), (key2893, -2), (key2782, -2), (key2805, -2), (key2976, 2), (key2983, 2), (key2972, 2), (key2976, 2), (key2983, 2), (key2641, 2), (key2728, 2), (key2628, 2), (key2702, 2), (key2972, 2), (key2628, 2), (key2702, 2)]

def rawRow9692 : Integer.Sparse Key := [(key2904, -2), (key2897, -2), (key2893, -2), (key2904, -2), (key2897, -2), (key2831, -2), (key2795, -2), (key2805, -2), (key2782, -2), (key2893, -2), (key2805, -2), (key2782, -2), (key2983, 2), (key2976, 2), (key2972, 2), (key2983, 2), (key2976, 2), (key2728, 2), (key2641, 2), (key2702, 2), (key2628, 2), (key2972, 2), (key2702, 2), (key2628, 2)]

def rawRow9717 : Integer.Sparse Key := [(key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2644, 1), (key2644, 1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2732, 1), (key2732, 1), (key2860, 1), (key2860, 1), (key2870, 1), (key2870, 1), (key2885, 1), (key2885, 1), (key3023, 1), (key3023, 1), (key3026, 1), (key3026, 1), (key3030, 1), (key3030, 1), (key2658, -2), (key2660, -2), (key2660, -2), (key2753, -2), (key2758, -2), (key2758, -2), (key2920, -2), (key2920, -2), (key2923, -2), (key2923, -2), (key2927, -2), (key2927, -2)]

def rawRow9718 : Integer.Sparse Key := [(key2640, 1), (key2644, 1), (key2632, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2870, 1), (key2885, 1), (key2860, 1), (key2885, 1), (key2860, 1), (key2870, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3030, 1), (key3023, 1), (key3026, 1), (key2660, -2), (key2658, -2), (key2660, -2), (key2758, -2), (key2753, -2), (key2758, -2), (key2923, -2), (key2927, -2), (key2920, -2), (key2927, -2), (key2920, -2), (key2923, -2)]

def rawRow9719 : Integer.Sparse Key := [(key2644, 1), (key2640, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2632, 1), (key2732, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2706, 1), (key2885, 1), (key2870, 1), (key2885, 1), (key2860, 1), (key2870, 1), (key2860, 1), (key3030, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3026, 1), (key3023, 1), (key2660, -2), (key2660, -2), (key2658, -2), (key2758, -2), (key2758, -2), (key2753, -2), (key2927, -2), (key2923, -2), (key2927, -2), (key2920, -2), (key2923, -2), (key2920, -2)]

def rawRow9720 : Integer.Sparse Key := [(key2706, 1), (key2706, 1), (key2860, 1), (key2860, 1), (key3023, 1), (key3023, 1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1), (key2640, 1), (key2640, 1), (key2726, 1), (key2726, 1), (key3030, 1), (key3030, 1), (key2644, 1), (key2644, 1), (key2732, 1), (key2732, 1), (key2885, 1), (key2885, 1), (key2753, -2), (key2920, -2), (key2920, -2), (key2658, -2), (key2923, -2), (key2923, -2), (key2660, -2), (key2660, -2), (key2758, -2), (key2758, -2), (key2927, -2), (key2927, -2)]

def rawRow9721 : Integer.Sparse Key := [(key2860, 1), (key3023, 1), (key2706, 1), (key3023, 1), (key2706, 1), (key2860, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2885, 1), (key2644, 1), (key2732, 1), (key2920, -2), (key2753, -2), (key2920, -2), (key2923, -2), (key2658, -2), (key2923, -2), (key2758, -2), (key2927, -2), (key2660, -2), (key2927, -2), (key2660, -2), (key2758, -2)]

def rawRow9722 : Integer.Sparse Key := [(key3023, 1), (key2860, 1), (key3023, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key3030, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2640, 1), (key2885, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2732, 1), (key2644, 1), (key2920, -2), (key2920, -2), (key2753, -2), (key2923, -2), (key2923, -2), (key2658, -2), (key2927, -2), (key2758, -2), (key2927, -2), (key2660, -2), (key2758, -2), (key2660, -2)]

def rawRow9723 : Integer.Sparse Key := [(key2726, 1), (key2732, 1), (key2870, 1), (key2885, 1), (key3026, 1), (key3030, 1), (key2640, 1), (key2644, 1), (key2860, 1), (key2885, 1), (key3023, 1), (key3030, 1), (key2632, 1), (key2644, 1), (key2706, 1), (key2732, 1), (key3023, 1), (key3026, 1), (key2632, 1), (key2640, 1), (key2706, 1), (key2726, 1), (key2860, 1), (key2870, 1), (key2758, -2), (key2923, -2), (key2927, -2), (key2660, -2), (key2920, -2), (key2927, -2), (key2658, -2), (key2660, -2), (key2753, -2), (key2758, -2), (key2920, -2), (key2923, -2)]

def rawRow9724 : Integer.Sparse Key := [(key2732, 1), (key2726, 1), (key2885, 1), (key2870, 1), (key3030, 1), (key3026, 1), (key2644, 1), (key2640, 1), (key2885, 1), (key2860, 1), (key3030, 1), (key3023, 1), (key2644, 1), (key2632, 1), (key2732, 1), (key2706, 1), (key3026, 1), (key3023, 1), (key2640, 1), (key2632, 1), (key2726, 1), (key2706, 1), (key2870, 1), (key2860, 1), (key2758, -2), (key2927, -2), (key2923, -2), (key2660, -2), (key2927, -2), (key2920, -2), (key2660, -2), (key2658, -2), (key2758, -2), (key2753, -2), (key2923, -2), (key2920, -2)]

def rawRow9725 : Integer.Sparse Key := [(key2870, 1), (key3026, 1), (key2726, 1), (key3030, 1), (key2732, 1), (key2885, 1), (key2860, 1), (key3023, 1), (key2640, 1), (key3030, 1), (key2644, 1), (key2885, 1), (key2706, 1), (key3023, 1), (key2632, 1), (key3026, 1), (key2644, 1), (key2732, 1), (key2706, 1), (key2860, 1), (key2632, 1), (key2870, 1), (key2640, 1), (key2726, 1), (key2923, -2), (key2758, -2), (key2927, -2), (key2920, -2), (key2660, -2), (key2927, -2), (key2753, -2), (key2920, -2), (key2658, -2), (key2923, -2), (key2660, -2), (key2758, -2)]

def rawRow9726 : Integer.Sparse Key := [(key3026, 1), (key2870, 1), (key3030, 1), (key2726, 1), (key2885, 1), (key2732, 1), (key3023, 1), (key2860, 1), (key3030, 1), (key2640, 1), (key2885, 1), (key2644, 1), (key3023, 1), (key2706, 1), (key3026, 1), (key2632, 1), (key2732, 1), (key2644, 1), (key2860, 1), (key2706, 1), (key2870, 1), (key2632, 1), (key2726, 1), (key2640, 1), (key2923, -2), (key2927, -2), (key2758, -2), (key2920, -2), (key2927, -2), (key2660, -2), (key2920, -2), (key2753, -2), (key2923, -2), (key2658, -2), (key2758, -2), (key2660, -2)]

def rawRow9727 : Integer.Sparse Key := [(key2885, 1), (key3030, 1), (key2732, 1), (key3026, 1), (key2726, 1), (key2870, 1), (key2885, 1), (key3030, 1), (key2644, 1), (key3023, 1), (key2640, 1), (key2860, 1), (key2732, 1), (key3026, 1), (key2644, 1), (key3023, 1), (key2632, 1), (key2706, 1), (key2726, 1), (key2870, 1), (key2640, 1), (key2860, 1), (key2632, 1), (key2706, 1), (key2927, -2), (key2758, -2), (key2923, -2), (key2927, -2), (key2660, -2), (key2920, -2), (key2758, -2), (key2923, -2), (key2660, -2), (key2920, -2), (key2658, -2), (key2753, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def row1025 : Integer.Sparse (Fin 3237) := [(507, 1), (776, 3), (862, 1), (1167, 1), (2819, -1)]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def merged0 : Integer.Sparse (Fin 3237) := [(0, 1285216599745830279647700), (225, 678992630976707666623200), (261, -1964209230722537946270900), (1593, -13967661671904069084513600), (1595, -6983830835952034542256800), (1611, -13967661671904069084513600), (1618, -13967661671904069084513600), (1619, -13967661671904069084513600), (1620, -8293176571694532856228800), (1622, -2764392190564844285409600), (1631, -6983830835952034542256800), (1632, -2764392190564844285409600), (2160, -8293176571694532856228800), (2177, -13967661671904069084513600), (2573, -13967661671904069084513600), (2574, -8293176571694532856228800), (2578, -13967661671904069084513600), (2579, -2764392190564844285409600), (2694, -13967661671904069084513600), (2699, -27935323343808138169027200), (2702, -13967661671904069084513600), (2703, -27935323343808138169027200), (2704, -16586353143389065712457600), (2765, -27935323343808138169027200), (2766, -22260838243598601940742400), (2768, -13967661671904069084513600), (2769, -13967661671904069084513600)]

def merged1 : Integer.Sparse (Fin 3237) := [(0, -267672051461567578867020), (225, -372209690275116851278800), (261, -752392518963147553900500), (1593, 2058860222619330042864000), (1595, 1029430111309665021432000), (1611, 2058860222619330042864000), (2159, 4640914202332773280154400), (2160, 4640914202332773280154400), (2177, 2058860222619330042864000), (2567, 4640914202332773280154400), (2571, 2320457101166386640077200), (2574, 4640914202332773280154400), (2694, 2058860222619330042864000), (2699, 4117720445238660085728000), (2704, 9281828404665546560308800), (2760, 4640914202332773280154400), (2763, 4640914202332773280154400), (2768, 2058860222619330042864000), (2769, 2058860222619330042864000)]

def merged10 : Integer.Sparse (Fin 3237) := [(0, -1215677085924961445671830), (32, 8894609147891515350750), (160, -142313746366264245612000), (225, 426941239098792736836000), (256, -284627492732528491224000), (261, 2609042335648583758321020), (2177, 7684942303778269263048000), (2570, 7684942303778269263048000), (2571, -9092637834964183732075200), (2573, 7684942303778269263048000), (2575, 5828490711579439089774000), (2578, 5828490711579439089774000), (2579, -1088049041128248214100400), (2580, 1942830237193146363258000), (2694, 7684942303778269263048000), (2699, 15369884607556538526096000), (2702, 7684942303778269263048000), (2703, 15369884607556538526096000), (2762, 7684942303778269263048000), (2763, -18185275669928367464150400), (2764, 11656981423158878179548000), (2766, -9092637834964183732075200), (2767, 7684942303778269263048000), (2768, 7684942303778269263048000), (2769, 5828490711579439089774000), (2794, 7684942303778269263048000), (2797, 7684942303778269263048000), (2832, 16383626893939884229183680), (2833, 2047953361742485528647960), (2840, 24575440340909826343775520)]

def merged11 : Integer.Sparse (Fin 3237) := [(0, -199460843543045468633340), (225, 82058675379216313764000), (261, -402378821215909068377700), (1591, 2598904946898691116235200), (1592, 5197809893797382232470400), (1610, 5197809893797382232470400), (2177, -1682773185109196202724800), (2693, 5197809893797382232470400), (2694, -1682773185109196202724800), (2698, 5197809893797382232470400), (2699, -3365546370218392405449600), (2762, 5197809893797382232470400), (2763, 5197809893797382232470400), (2764, 10395619787594764464940800), (2794, -1682773185109196202724800), (2797, -1682773185109196202724800)]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def merged100 : Integer.Sparse (Fin 3237) := [(677, -276634243526994557215200), (913, -2895529304393043091200), (950, -276634243526994557215200), (1404, 1654014402553181257108800), (1426, 827007201276590628554400), (1622, 550372957749596071339200), (2158, 827007201276590628554400), (2832, -550372957749596071339200)]

def merged101 : Integer.Sparse (Fin 3237) := [(697, -235022837585087810815200), (950, 275140773281033470188000), (1426, -705068512755263432445600), (1494, 825422319843100410564000), (1622, 40117935695945659372800), (1981, 275140773281033470188000), (2832, -40117935695945659372800)]

def merged102 : Integer.Sparse (Fin 3237) := [(672, -631171747232298670053600), (697, -235022837585087810815200), (950, 275140773281033470188000), (1404, -1262343494464597340107200), (1426, -705068512755263432445600), (1494, 194250572610801740510400), (1619, -631171747232298670053600), (1622, -591053811536353010680800), (1981, 275140773281033470188000), (2832, 591053811536353010680800)]

def merged103 : Integer.Sparse (Fin 3237) := [(672, -631171747232298670053600), (677, -276634243526994557215200), (697, -235022837585087810815200), (913, -2895529304393043091200), (950, -1493470245961087027200), (1404, 391670908088583917001600), (1426, 121938688521327196108800), (1494, 194250572610801740510400), (1619, -631171747232298670053600), (1622, -40680853786756939341600), (1981, 275140773281033470188000), (2158, 827007201276590628554400), (2832, 40680853786756939341600)]

def merged104 : Integer.Sparse (Fin 3237) := [(0, -3432002413967769600), (32, -17160012069838848000), (672, 575329970233002945996000), (677, 191776656744334315332000), (697, 191776656744334315332000), (700, 411840289676132352000), (1167, 411840289676132352000), (1429, 1235520869028397056000), (1571, 1235520869028397056000), (1595, 1235520869028397056000), (1622, 192188497034010447684000), (1631, 1235520869028397056000), (1632, 411840289676132352000), (2580, 411840289676132352000), (2832, -191776656744334315332000), (2937, -4942083476113588224000), (2940, -1647361158704529408000), (3040, -9884166952227176448000), (3043, -4942083476113588224000), (3066, -4942083476113588224000), (3067, -1647361158704529408000), (3182, -4942083476113588224000)]

def merged105 : Integer.Sparse (Fin 3237) := [(0, 212411403750318322200), (32, 955851316876432449900), (162, 1699291230002546577600), (261, 318617105625477483300), (700, -135560373450244870176000), (1151, -45880863210068757595200), (1167, -15293621070022919198400), (1173, -15293621070022919198400), (1429, -406681120350734610528000), (1555, -91761726420137515190400), (1571, -45880863210068757595200), (1575, -45880863210068757595200), (1595, -45880863210068757595200), (1603, -45880863210068757595200), (1626, -15293621070022919198400), (1632, -135560373450244870176000), (1943, -45880863210068757595200), (2833, 135560373450244870176000)]

def merged106 : Integer.Sparse (Fin 3237) := [(0, 11502685502777074200), (32, -98919453923159102100), (162, 2502926102992711569600), (261, 469298644311133419300), (700, -135560373450244870176000), (948, 10849070785367227392000), (950, 3616356928455742464000), (1151, -45880863210068757595200), (1167, -15293621070022919198400), (1173, -15293621070022919198400), (1429, -406681120350734610528000), (1495, 10849070785367227392000), (1555, -91761726420137515190400), (1571, -45880863210068757595200), (1575, -45880863210068757595200), (1595, -45880863210068757595200), (1603, -35031792424701530203200), (1622, 3616356928455742464000), (1626, -11677264141567176734400), (1632, -135560373450244870176000), (1928, 21698141570734454784000), (1943, -35031792424701530203200), (2833, 135560373450244870176000)]

def merged107 : Integer.Sparse (Fin 3237) := [(0, 8070683088809304600), (32, -116079465992997950100), (162, 2502926102992711569600), (261, 469298644311133419300), (672, 575329970233002945996000), (677, 191776656744334315332000), (697, 191776656744334315332000), (700, -135148533160568737824000), (948, 10849070785367227392000), (950, 3616356928455742464000), (1151, -45880863210068757595200), (1167, -14881780780346786846400), (1173, -15293621070022919198400), (1429, -405445599481706213472000), (1495, 10849070785367227392000), (1555, -91761726420137515190400), (1571, -44645342341040360539200), (1575, -45880863210068757595200), (1595, -44645342341040360539200), (1603, -35031792424701530203200), (1622, 195804853962466190148000), (1626, -11677264141567176734400), (1631, 1235520869028397056000), (1632, -135148533160568737824000), (1928, 21698141570734454784000), (1943, -35031792424701530203200), (2580, 411840289676132352000), (2832, -191776656744334315332000), (2833, 135560373450244870176000), (2937, -4942083476113588224000), (2940, -1647361158704529408000), (3040, -9884166952227176448000), (3043, -4942083476113588224000), (3066, -4942083476113588224000), (3067, -1647361158704529408000), (3182, -4942083476113588224000)]

def merged108 : Integer.Sparse (Fin 3237) := [(0, 8070683088809304600), (32, -116079465992997950100), (162, 2502926102992711569600), (261, 469298644311133419300), (672, -55841776999295724057600), (677, -84857586782660241883200), (697, -43246180840753495483200), (700, -135148533160568737824000), (913, -2895529304393043091200), (948, 10849070785367227392000), (950, 2122886682494655436800), (1151, -45880863210068757595200), (1167, -14881780780346786846400), (1173, -15293621070022919198400), (1404, 391670908088583917001600), (1426, 121938688521327196108800), (1429, -405445599481706213472000), (1494, 194250572610801740510400), (1495, 10849070785367227392000), (1555, -91761726420137515190400), (1571, -44645342341040360539200), (1575, -45880863210068757595200), (1595, -44645342341040360539200), (1603, -35031792424701530203200), (1619, -631171747232298670053600), (1622, 155124000175709250806400), (1626, -11677264141567176734400), (1631, 1235520869028397056000), (1632, -135148533160568737824000), (1928, 21698141570734454784000), (1943, -35031792424701530203200), (1981, 275140773281033470188000), (2158, 827007201276590628554400), (2580, 411840289676132352000), (2832, -151095802957577375990400), (2833, 135560373450244870176000), (2937, -4942083476113588224000), (2940, -1647361158704529408000), (3040, -9884166952227176448000), (3043, -4942083476113588224000), (3066, -4942083476113588224000), (3067, -1647361158704529408000), (3182, -4942083476113588224000)]

def merged109 : Integer.Sparse (Fin 3237) := [(0, 166647687242114999378010), (32, 862400637369782396908050), (160, 137552081957426623200), (162, 19139953194863198510400), (225, 3137582130547112421600), (261, 12198006991643294967600), (503, 2455834941810652852800), (507, 818611647270217617600), (518, -87170552466582688236000), (520, -28238239174924011794400), (521, -29056850822194229412000), (672, -55841776999295724057600), (674, 224599865740251573700800), (677, -9990964869243050649600), (697, -42378923204840127931200), (698, 74866621913417191233600), (700, -135148533160568737824000), (780, 2455834941810652852800), (869, 818611647270217617600), (913, -2895529304393043091200), (916, 224599865740251573700800), (948, 10849070785367227392000), (950, 2122886682494655436800), (1151, -45880863210068757595200), (1159, -8771514062401274335200), (1167, -14881780780346786846400), (1172, -8771514062401274335200), (1173, -18217459090823343976800), (1179, -2056580384887057226400), (1180, -2923838020800424778400), (1316, 4911669883621305705600), (1329, -174341104933165376472000), (1331, -84714717524772035383200), (1332, -87170552466582688236000), (1404, 391670908088583917001600), (1426, 124540461429067298764800), (1429, -405445599481706213472000), (1473, 2455834941810652852800), (1494, 194250572610801740510400), (1495, 10849070785367227392000), (1555, -91761726420137515190400), (1563, -17543028124802548670400), (1571, -44645342341040360539200), (1575, -45880863210068757595200), (1580, -6169741154661171679200), (1595, -6869981231154805041482400), (1603, -35031792424701530203200), (1611, -6169741154661171679200), (1612, -8771514062401274335200), (1619, 15503016032083120510216800), (1620, -84714717524772035383200), (1622, 3228150521884819820284800), (1626, -11677264141567176734400), (1628, -87170552466582688236000), (1630, -29056850822194229412000), (1631, 18377721280771401662139600), (1632, 5991165331787492568154800), (1769, 449199731480503147401600), (1787, 224599865740251573700800), (1925, -13650671777627529361886400), (1928, 21698141570734454784000), (1936, -6825335888813764680943200), (1943, -6860367681238466211146400), (1951, -8771514062401274335200), (1975, 224599865740251573700800), (1981, 347083557173650236643200), (2158, 827007201276590628554400), (2160, 2455834941810652852800), (2502, -9465034118049957856449600), (2574, -87170552466582688236000), (2579, 5349005742282945497344800), (2580, 2970895720907147935230000), (2832, -5528291138426803735195200), (2833, -2834923507167226932702000), (2929, -10407091630960410624000), (2930, -10407091630960410624000), (2932, -3469030543653470208000), (2937, -4942083476113588224000), (2940, -5116391702357999616000), (3033, -20814183261920821248000), (3040, -9884166952227176448000), (3043, -4942083476113588224000), (3061, -10407091630960410624000), (3066, -4942083476113588224000), (3067, -1647361158704529408000), (3182, -4942083476113588224000), (3185, -10407091630960410624000), (3200, -3469030543653470208000)]

def merged110 : Integer.Sparse (Fin 3237) := [(0, 174827531441737637882895), (32, 853595734436285450604225), (160, 850365912694737961200), (162, 19139953194863198510400), (225, 3850395961284423759600), (261, 4253060931385738948350), (503, 2455834941810652852800), (507, 818611647270217617600), (518, -87170552466582688236000), (520, -28238239174924011794400), (521, -29056850822194229412000), (659, -231309093798208090728000), (664, -77103031266069363576000), (672, -55841776999295724057600), (674, 224599865740251573700800), (677, -9990964869243050649600), (697, -119481954470909491507200), (698, 74866621913417191233600), (700, -135148533160568737824000), (780, 2455834941810652852800), (796, 1799238072013198711624800), (806, 2399997036955251359505600), (828, -231309093798208090728000), (835, -6451063194646925115559200), (869, 818611647270217617600), (913, -2895529304393043091200), (916, 224599865740251573700800), (920, -10564255929754205280000), (927, 8681702133494465393623200), (932, 58960774622564610969600), (948, 10849070785367227392000), (950, 2122886682494655436800), (1062, -38491946859814812252000), (1063, -38491946859814812252000), (1067, -76983893719629624504000), (1151, -45880863210068757595200), (1155, -38491946859814812252000), (1159, -8771514062401274335200), (1167, -14881780780346786846400), (1172, -8771514062401274335200), (1173, -18217459090823343976800), (1176, -160552327831636096540800), (1178, -53517442610545365513600), (1179, -55574022995432422740000), (1180, -2923838020800424778400), (1316, 4911669883621305705600), (1329, -174341104933165376472000), (1331, -84714717524772035383200), (1332, -87170552466582688236000), (1404, 391670908088583917001600), (1419, 42338235268295376076800), (1421, 69218710061460390144000), (1423, 82023418248457667788800), (1426, 124540461429067298764800), (1427, 10902412848954547151204400), (1429, -405445599481706213472000), (1473, 2455834941810652852800), (1494, 194250572610801740510400), (1495, 10849070785367227392000), (1555, -91761726420137515190400), (1563, -17543028124802548670400), (1571, -44645342341040360539200), (1575, -45880863210068757595200), (1580, -6169741154661171679200), (1595, -6912102519435579734368800), (1603, -35031792424701530203200), (1611, -6169741154661171679200), (1612, -8771514062401274335200), (1619, 15503016032083120510216800), (1620, -84714717524772035383200), (1622, 3214110092457894922656000), (1626, -11677264141567176734400), (1628, -87170552466582688236000), (1630, -29056850822194229412000), (1631, 7291263386183069797207200), (1632, 5977124902360567670526000), (1743, 10480940205507664105248000), (1758, 19300783116347765965296000), (1769, 449199731480503147401600), (1786, -231309093798208090728000), (1787, 224599865740251573700800), (1801, 2378868525095742948945600), (1816, -6461627450576679320839200), (1847, 3657436918648962034219200), (1855, 2458957811577815970475200), (1861, -12843165614671285620148800), (1925, 30647879210712180359023200), (1928, 21698141570734454784000), (1934, 140232151979281032751080000), (1936, -6867457177094539373829600), (1943, -6860367681238466211146400), (1951, -8771514062401274335200), (1958, 62465014276515965580228000), (1975, 224599865740251573700800), (1981, 347083557173650236643200), (2158, 827007201276590628554400), (2160, 2455834941810652852800), (2168, -31106361305261735935041600), (2177, -22414094915837516336138400), (2182, -62132633324041398848553600), (2210, 10902412848954547151204400), (2216, 5451206424477273575602200), (2289, -38491946859814812252000), (2293, -38491946859814812252000), (2301, -76983893719629624504000), (2310, -160552327831636096540800), (2320, -53517442610545365513600), (2341, -38491946859814812252000), (2345, -76983893719629624504000), (2368, 26880474793165014067200), (2372, -1326526144066542182400), (2407, -76983893719629624504000), (2436, -38491946859814812252000), (2449, -398088549382901817585600), (2451, -160552327831636096540800), (2479, -76983893719629624504000), (2482, -76983893719629624504000), (2496, -38491946859814812252000), (2497, -76983893719629624504000), (2500, -11014803079226259073614000), (2501, -76983893719629624504000), (2502, -9450741404456269436836800), (2504, 5451206424477273575602200), (2535, -38491946859814812252000), (2564, -160552327831636096540800), (2573, -38491946859814812252000), (2574, -87170552466582688236000), (2575, -160552327831636096540800), (2578, -160552327831636096540800), (2579, 5295488299672400131831200), (2580, -8135513238665025417153600), (2763, 37820280421830908966025600), (2832, -5528291138426803735195200), (2833, -2812674483990067895478000), (2839, -44298550988339709720909600), (2929, -10407091630960410624000), (2930, -10407091630960410624000), (2932, -3469030543653470208000), (2937, -4942083476113588224000), (2940, -5116391702357999616000), (3033, -20814183261920821248000), (3040, -9884166952227176448000), (3043, -4942083476113588224000), (3061, -10407091630960410624000), (3066, -4942083476113588224000), (3067, -1647361158704529408000), (3171, 168485153123098771545600), (3182, 79300493085435797548800), (3185, -10407091630960410624000), (3200, -3469030543653470208000)]

def merged111 : Integer.Sparse (Fin 3237) := [(0, 20599686078642851460), (32, -29121487609536000), (160, -93188760350515200), (225, -82310214992238416400), (261, 61686066864003554700), (473, -2516096529463910400), (476, -1258048264731955200), (491, -2516096529463910400), (514, -4442235513051410575200), (516, -2221117756525705287600), (517, -4442235513051410575200), (792, -2516096529463910400), (825, -2516096529463910400), (1294, -2516096529463910400), (1306, -5032193058927820800), (1325, -4442235513051410575200), (1327, -4442235513051410575200), (1328, -8884471026102821150400), (1394, -5032193058927820800), (1426, -2516096529463910400), (1577, -8884471026102821150400), (1579, -4442235513051410575200), (1580, -4442235513051410575200), (1593, -2516096529463910400), (1611, -2516096529463910400), (1618, -4442235513051410575200), (1619, -4442235513051410575200), (2177, -2516096529463910400), (2573, -4442235513051410575200), (2578, -4442235513051410575200)]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def merged1001 : Integer.Sparse (Fin 3237) := [(602, 574094896129316061964800), (609, 194558094389809866643200), (614, 6141511972205568000), (625, 97279047194904933321600), (634, 287047448064658030982400), (668, 97279047194904933321600), (769, -194545811365865455507200), (780, -97272905682932727753600), (784, -287047448064658030982400), (792, -287047448064658030982400), (800, -574094896129316061964800), (841, -97272905682932727753600), (1571, 6141511972205568000), (2830, -6141511972205568000)]

def merged1002 : Integer.Sparse (Fin 3237) := [(0, 241872449970499084800), (3, -967489799881996339200), (4, -241872449970499084800), (261, 967489799881996339200), (349, -34829632795751868211200), (356, -4353704099468983526400), (744, -52244449193627802316800), (1013, -1651223845039104000), (1017, -206402980629888000), (2285, -2476835767558656000), (2320, -1651223845039104000)]

def merged1003 : Integer.Sparse (Fin 3237) := [(0, -98224113355224998400), (3, 392896453420899993600), (4, -491120566776124992000), (261, 196448226710449996800), (664, 14144272323152399769600), (810, 21216408484728599654400), (1178, 23267922125611870022400), (2323, 5816980531402967505600), (2820, -5816980531402967505600)]

def merged1004 : Integer.Sparse (Fin 3237) := [(0, -98224113355224998400), (3, 392896453420899993600), (4, -491120566776124992000), (261, 196448226710449996800), (664, 14144567991059926425600), (810, 21216408484728599654400), (1178, 23268217793519396678400), (2323, 5816980531402967505600), (2820, -5816980531402967505600), (2964, -887003722579968000)]

def merged1005 : Integer.Sparse (Fin 3237) := [(0, 143648336615274086400), (3, -574593346461096345600), (4, -732993016746624076800), (261, 1163938026592446336000), (349, -34829632795751868211200), (356, -4353704099468983526400), (664, 14144567991059926425600), (744, -52244449193627802316800), (810, 21216408484728599654400), (1013, -1651223845039104000), (1017, -206402980629888000), (1178, 23268217793519396678400), (2285, -2476835767558656000), (2320, -1651223845039104000), (2323, 5816980531402967505600), (2820, -5816980531402967505600), (2964, -887003722579968000)]

def merged1006 : Integer.Sparse (Fin 3237) := [(0, 143648336615274086400), (3, -574593346461096345600), (4, -732993016746624076800), (261, 1163938026592446336000), (349, -34829632795751868211200), (356, -4353704099468983526400), (602, 574094896129316061964800), (609, 194558094389809866643200), (614, 6141511972205568000), (625, 97279047194904933321600), (634, 287047448064658030982400), (664, 14144567991059926425600), (668, 97279047194904933321600), (744, -52244449193627802316800), (769, -194545811365865455507200), (780, -97272905682932727753600), (784, -287047448064658030982400), (792, -287047448064658030982400), (800, -574094896129316061964800), (810, 21216408484728599654400), (841, -97272905682932727753600), (1013, -1651223845039104000), (1017, -206402980629888000), (1178, 23268217793519396678400), (1571, 6141511972205568000), (2285, -2476835767558656000), (2320, -1651223845039104000), (2323, 5816980531402967505600), (2820, -5816980531402967505600), (2830, -6141511972205568000), (2964, -887003722579968000)]

def merged1007 : Integer.Sparse (Fin 3237) := [(0, 899429184321892963200), (3, 946767562444097856000), (4, -1183459453055122320000), (32, -1420151343666146784000), (261, -946767562444097856000), (321, -34083632247987522816000), (325, -11361210749329174272000), (349, -92076263110508544000), (351, -11361210749329174272000), (367, -34083632247987522816000), (574, -276228789331525632000), (656, -276228789331525632000), (722, -68167264495975045632000), (746, -34083632247987522816000), (825, -276228789331525632000), (869, -92076263110508544000), (1013, -92076263110508544000), (1132, -276228789331525632000), (1157, -276228789331525632000), (1579, -276228789331525632000), (1630, -92076263110508544000), (2848, 1104915157326102528000), (2851, 1104915157326102528000), (2855, 368305052442034176000), (2864, 368305052442034176000), (2868, 2209830314652205056000), (2889, 1104915157326102528000)]

def merged1008 : Integer.Sparse (Fin 3237) := [(325, 13653083709351620352000), (362, -44454557741508943257600), (377, 13653083709351620352000), (551, -170827617739127608627200), (574, -85413808869563804313600), (664, -71760725160212183961600), (825, -85413808869563804313600), (2832, 71760725160212183961600)]

def merged1009 : Integer.Sparse (Fin 3237) := [(325, 13653083709351620352000), (362, -44454557741508943257600), (377, 13653083709351620352000), (551, -170827617739127608627200), (574, -85413808869563804313600), (664, -71760725160212183961600), (825, -85413808869563804313600), (992, 276147382278039552000), (1008, 276147382278039552000), (1010, 92049127426013184000), (1013, 92049127426013184000), (1016, 92049127426013184000), (1112, 552294764556079104000), (1132, 276147382278039552000), (1154, 276147382278039552000), (1157, 276147382278039552000), (1579, 276147382278039552000), (1630, 92049127426013184000), (2832, 71760725160212183961600)]

def merged1010 : Integer.Sparse (Fin 3237) := [(0, 899429184321892963200), (3, 946767562444097856000), (4, -1183459453055122320000), (32, -1420151343666146784000), (261, -946767562444097856000), (321, -34083632247987522816000), (325, 2291872960022446080000), (349, -92076263110508544000), (351, -11361210749329174272000), (362, -44454557741508943257600), (367, -34083632247987522816000), (377, 13653083709351620352000), (551, -170827617739127608627200), (574, -85690037658895329945600), (656, -276228789331525632000), (664, -71760725160212183961600), (722, -68167264495975045632000), (746, -34083632247987522816000), (825, -85690037658895329945600), (869, -92076263110508544000), (992, 276147382278039552000), (1008, 276147382278039552000), (1010, 92049127426013184000), (1013, -27135684495360000), (1016, 92049127426013184000), (1112, 552294764556079104000), (1132, -81407053486080000), (1154, 276147382278039552000), (1157, -81407053486080000), (1579, -81407053486080000), (1630, -27135684495360000), (2832, 71760725160212183961600), (2848, 1104915157326102528000), (2851, 1104915157326102528000), (2855, 368305052442034176000), (2864, 368305052442034176000), (2868, 2209830314652205056000), (2889, 1104915157326102528000)]

def merged1011 : Integer.Sparse (Fin 3237) := [(318, 56292462603027247564800), (377, -12574890263324164608000), (551, 112584925206054495129600), (588, 18567791813054753740800), (656, 56292462603027247564800), (664, 43717572339703082956800), (869, -12574890263324164608000), (2832, -43717572339703082956800)]

def merged1012 : Integer.Sparse (Fin 3237) := [(0, 5639415322408560), (3, -10253482404379200), (4, -2563370601094800), (32, 15380223606568800), (261, 10253482404379200), (285, -1107376099672953600), (289, -369125366557651200), (299, -369125366557651200), (308, -1107376099672953600), (343, -369125366557651200), (399, -90091795788288000), (402, -30030598596096000), (406, -30030598596096000), (529, -2214752199345907200), (541, -1107376099672953600), (574, -1107376099672953600), (659, -1107376099672953600), (697, -369125366557651200), (828, -1107376099672953600), (970, -90091795788288000), (997, -30030598596096000), (1032, -180183591576576000), (1038, -90091795788288000), (1132, -90091795788288000), (1176, -90091795788288000), (1179, -30030598596096000), (2310, -90091795788288000), (2320, -30030598596096000), (2580, -30030598596096000)]

def merged1013 : Integer.Sparse (Fin 3237) := [(0, 5639415322408560), (3, -10253482404379200), (4, -2563370601094800), (32, 15380223606568800), (261, 10253482404379200), (285, -1107376099672953600), (289, -369125366557651200), (299, -369125366557651200), (308, -1107376099672953600), (343, -369125366557651200), (349, 39727937897514923212800), (399, -90091795788288000), (402, -30030598596096000), (406, -30030598596096000), (529, -2214752199345907200), (541, -1107376099672953600), (574, 119182706316445096684800), (659, -1107376099672953600), (664, 39727937897514923212800), (697, -369125366557651200), (828, -1107376099672953600), (970, -90091795788288000), (997, -30030598596096000), (1032, -180183591576576000), (1038, -90091795788288000), (1132, -90091795788288000), (1176, -90091795788288000), (1179, -30030598596096000), (2310, -90091795788288000), (2320, -30030598596096000), (2580, -30030598596096000), (2832, -39727937897514923212800)]

def merged1014 : Integer.Sparse (Fin 3237) := [(0, 5639415322408560), (3, -10253482404379200), (4, -2563370601094800), (32, 15380223606568800), (261, 10253482404379200), (285, -1107376099672953600), (289, -369125366557651200), (299, -369125366557651200), (308, -1107376099672953600), (318, 56292462603027247564800), (343, -369125366557651200), (349, 39727937897514923212800), (377, -12574890263324164608000), (399, -90091795788288000), (402, -30030598596096000), (406, -30030598596096000), (529, -2214752199345907200), (541, -1107376099672953600), (551, 112584925206054495129600), (574, 119182706316445096684800), (588, 18567791813054753740800), (656, 56292462603027247564800), (659, -1107376099672953600), (664, 83445510237218006169600), (697, -369125366557651200), (828, -1107376099672953600), (869, -12574890263324164608000), (970, -90091795788288000), (997, -30030598596096000), (1032, -180183591576576000), (1038, -90091795788288000), (1132, -90091795788288000), (1176, -90091795788288000), (1179, -30030598596096000), (2310, -90091795788288000), (2320, -30030598596096000), (2580, -30030598596096000), (2832, -83445510237218006169600)]

def merged1015 : Integer.Sparse (Fin 3237) := [(0, 899434823737215371760), (3, 946757308961693476800), (4, -1183462016425723414800), (32, -1420135963442540215200), (261, -946757308961693476800), (285, -1107376099672953600), (289, -369125366557651200), (299, -369125366557651200), (308, -1107376099672953600), (318, 56292462603027247564800), (321, -34083632247987522816000), (325, 2291872960022446080000), (343, -369125366557651200), (349, 39635861634404414668800), (351, -11361210749329174272000), (362, -44454557741508943257600), (367, -34083632247987522816000), (377, 1078193446027455744000), (399, -90091795788288000), (402, -30030598596096000), (406, -30030598596096000), (529, -2214752199345907200), (541, -1107376099672953600), (551, -58242692533073113497600), (574, 33492668657549766739200), (588, 18567791813054753740800), (656, 56016233813695721932800), (659, -1107376099672953600), (664, 11684785077005822208000), (697, -369125366557651200), (722, -68167264495975045632000), (746, -34083632247987522816000), (825, -85690037658895329945600), (828, -1107376099672953600), (869, -12666966526434673152000), (970, -90091795788288000), (992, 276147382278039552000), (997, -30030598596096000), (1008, 276147382278039552000), (1010, 92049127426013184000), (1013, -27135684495360000), (1016, 92049127426013184000), (1032, -180183591576576000), (1038, -90091795788288000), (1112, 552294764556079104000), (1132, -171498849274368000), (1154, 276147382278039552000), (1157, -81407053486080000), (1176, -90091795788288000), (1179, -30030598596096000), (1579, -81407053486080000), (1630, -27135684495360000), (2310, -90091795788288000), (2320, -30030598596096000), (2580, -30030598596096000), (2832, -11684785077005822208000), (2848, 1104915157326102528000), (2851, 1104915157326102528000), (2855, 368305052442034176000), (2864, 368305052442034176000), (2868, 2209830314652205056000), (2889, 1104915157326102528000)]

def merged1016 : Integer.Sparse (Fin 3237) := [(0, 1043083160352489458160), (3, 372163962500597131200), (4, -1916455033172347491600), (32, -1420135963442540215200), (261, 217180717630752859200), (285, -1107376099672953600), (289, -369125366557651200), (299, -369125366557651200), (308, -1107376099672953600), (318, 56292462603027247564800), (321, -34083632247987522816000), (325, 2291872960022446080000), (343, -369125366557651200), (349, 4806228838652546457600), (351, -11361210749329174272000), (356, -4353704099468983526400), (362, -44454557741508943257600), (367, -34083632247987522816000), (377, 1078193446027455744000), (399, -90091795788288000), (402, -30030598596096000), (406, -30030598596096000), (529, -2214752199345907200), (541, -1107376099672953600), (551, -58242692533073113497600), (574, 33492668657549766739200), (588, 18567791813054753740800), (602, 574094896129316061964800), (609, 194558094389809866643200), (614, 6141511972205568000), (625, 97279047194904933321600), (634, 287047448064658030982400), (656, 56016233813695721932800), (659, -1107376099672953600), (664, 25829353068065748633600), (668, 97279047194904933321600), (697, -369125366557651200), (722, -68167264495975045632000), (744, -52244449193627802316800), (746, -34083632247987522816000), (769, -194545811365865455507200), (780, -97272905682932727753600), (784, -287047448064658030982400), (792, -287047448064658030982400), (800, -574094896129316061964800), (810, 21216408484728599654400), (825, -85690037658895329945600), (828, -1107376099672953600), (841, -97272905682932727753600), (869, -12666966526434673152000), (970, -90091795788288000), (992, 276147382278039552000), (997, -30030598596096000), (1008, 276147382278039552000), (1010, 92049127426013184000), (1013, -1678359529534464000), (1016, 92049127426013184000), (1017, -206402980629888000), (1032, -180183591576576000), (1038, -90091795788288000), (1112, 552294764556079104000), (1132, -171498849274368000), (1154, 276147382278039552000), (1157, -81407053486080000), (1176, -90091795788288000), (1178, 23268217793519396678400), (1179, -30030598596096000), (1571, 6141511972205568000), (1579, -81407053486080000), (1630, -27135684495360000), (2285, -2476835767558656000), (2310, -90091795788288000), (2320, -1681254443635200000), (2323, 5816980531402967505600), (2580, -30030598596096000), (2820, -5816980531402967505600), (2830, -6141511972205568000), (2832, -11684785077005822208000), (2848, 1104915157326102528000), (2851, 1104915157326102528000), (2855, 368305052442034176000), (2864, 368305052442034176000), (2868, 2209830314652205056000), (2889, 1104915157326102528000), (2964, -887003722579968000)]

set_option maxHeartbeats 1000000 in
def merged1017 : Integer.Sparse (Fin 3237) := [(0, -4550189413294195338192), (3, 1156340378673572408400), (4, -1995376742358456569700), (32, 2958191298719299505100), (66, 3769343306789930889600), (71, 630109704879715468800), (160, 18319696906918468488000), (218, -3771871244008245201600), (222, -5638245750067458124800), (225, 3331745427387085833600), (255, 333011299533994972800), (256, 13233520920227200320000), (260, -2352529248518925831600), (261, -4743276496205397502800), (274, -999033898601984918400), (285, -1107376099672953600), (289, -369125366557651200), (299, -369125366557651200), (308, -1107376099672953600), (318, 56292462603027247564800), (321, -89862403840236295833600), (325, 2291872960022446080000), (343, -369125366557651200), (349, 4806228838652546457600), (351, 2380899296640117657600), (356, -4353704099468983526400), (362, -44454557741508943257600), (367, 151903017209047694284800), (377, 1078193446027455744000), (399, -90091795788288000), (402, -30030598596096000), (406, -30030598596096000), (478, 1761047075114611200), (481, 880523537557305600), (491, 880523537557305600), (503, 880523537557305600), (516, 2220942473802420807600), (521, 29056909249768657572000), (529, -2214752199345907200), (541, -1107376099672953600), (551, -58242692533073113497600), (554, -111557543184497546035200), (574, 33492668657549766739200), (576, 41226330137907875788800), (588, 18567791813054753740800), (591, -55778771592248773017600), (602, 574094896129316061964800), (609, 194558094389809866643200), (614, 6141511972205568000), (625, 97279047194904933321600), (634, 287047448064658030982400), (641, -55778771592248773017600), (656, 56016233813695721932800), (659, -55779878968348445971200), (664, 25829353068065748633600), (668, 97279047194904933321600), (677, 13742110045969291929600), (697, 13741740920602734278400), (719, 371973298914070434201600), (722, -68167264495975045632000), (744, 133742200263407414784000), (746, -34083632247987522816000), (769, -194545811365865455507200), (780, -97272905682932727753600), (784, -287047448064658030982400), (792, -287047448064658030982400), (800, -574094896129316061964800), (810, 207203057941763816755200), (825, -85690037658895329945600), (828, 185985542080935544147200), (841, -97272905682932727753600), (869, -12666966526434673152000), (970, -90091795788288000), (992, 276147382278039552000), (997, -30030598596096000), (1008, 276147382278039552000), (1010, 92049127426013184000), (1013, -1678359529534464000), (1016, 92049127426013184000), (1017, -206402980629888000), (1032, -180183591576576000), (1038, -90091795788288000), (1063, 38491946859814812252000), (1068, 17025030956104985318400), (1074, 104195758705410958034400), (1112, 552294764556079104000), (1132, -171498849274368000), (1151, 880523537557305600), (1154, 276147382278039552000), (1157, -81407053486080000), (1175, -78779779647398473669200), (1176, -90091795788288000), (1178, -1882160593516840896000), (1179, -30030598596096000), (1180, 2056668542701692746400), (1385, 68028903480095783769600), (1392, 34014451740047891884800), (1415, 34014451740047891884800), (1436, 67462499437709610931200), (1438, 33731249718854805465600), (1466, 33731249718854805465600), (1567, 33731249718854805465600), (1571, 6141511972205568000), (1579, -81407053486080000), (1589, 34014451740047891884800), (1630, -27135684495360000), (1810, 338153540070176393068800), (1836, 74180913018743974262400), (1888, 8991305087417864265600), (1889, 8991305087417864265600), (1893, 17982610174835728531200), (1932, -38349139536732690691200), (1957, 8991305087417864265600), (1968, -38536933671314823427200), (2285, -2476835767558656000), (2308, -15485552233466203324800), (2310, -90091795788288000), (2320, -1681254443635200000), (2323, -5019880531787428708800), (2480, 338153540070176393068800), (2487, 17982610174835728531200), (2489, -29357834449314826425600), (2494, 8991305087417864265600), (2518, 74180913018743974262400), (2524, 8991305087417864265600), (2536, -38536933671314823427200), (2553, 17012962031752317657600), (2557, 34025924063504635315200), (2562, 17012962031752317657600), (2580, -30030598596096000), (2604, 68028903480095783769600), (2609, 34014451740047891884800), (2618, 34014451740047891884800), (2633, 67462499437709610931200), (2635, 371884789789031198534400), (2642, 74180913018743974262400), (2649, 67462499437709610931200), (2651, 33731249718854805465600), (2667, 33731249718854805465600), (2679, -67459924394026405516800), (2681, 68028903480095783769600), (2682, -76698279073465381382400), (2684, -105809063930759096208000), (2689, 68028903480095783769600), (2692, 67462499437709610931200), (2697, -58715668898629652851200), (2700, -96817758843341231942400), (2715, 372167991810224284953600), (2717, 599233212797723139283200), (2719, 17982610174835728531200), (2722, 599233212797723139283200), (2725, 17982610174835728531200), (2726, 295094124467594638099200), (2727, 135491402917805394700800), (2729, 9313234581466130918400), (2733, 74180913018743974262400), (2741, 294810922446401551680000), (2742, -9235779635755770451200), (2746, 17982610174835728531200), (2749, -212240765722703569488000), (2751, 51027413771800209542400), (2752, 17012962031752317657600), (2753, 34025924063504635315200), (2756, -16864981098506601379200), (2757, 34025924063504635315200), (2758, 50744211750607123123200), (2762, -8657903269912854182400), (2763, -67459924394026405516800), (2764, 34025924063504635315200), (2765, 101488423501214246246400), (2767, 112717846690058797689600), (2768, 7967998169218454572800), (2782, -154147734685259293708800), (2791, -153396558146930762764800), (2794, -38349139536732690691200), (2797, 112717846690058797689600), (2802, 299616606398861569641600), (2817, -880523537557305600), (2820, -16282761440821670163600), (2827, 972866107843499520), (2828, 2918598323530498560), (2830, -6141511972205568000), (2831, 55779744458356616517120), (2832, -25426895122975114137600), (2835, 972866107843499520), (2836, 2918598323530498560), (2838, -17718062410133003520), (2839, -450894037977340857930240), (2840, -185980812260388156103680), (2848, 1104915157326102528000), (2851, 1104915157326102528000), (2855, 368305052442034176000), (2864, 368305052442034176000), (2868, 2209830314652205056000), (2889, 1104915157326102528000), (2964, -887003722579968000), (3129, 308295469370518587417600), (3132, 154147734685259293708800), (3142, 306793116293861525529600), (3143, 153396558146930762764800), (3146, 153396558146930762764800), (3155, 153396558146930762764800), (3156, 153396558146930762764800), (3159, 306793116293861525529600), (3167, 154147734685259293708800), (3168, 154147734685259293708800), (3179, 308295469370518587417600), (3189, 153396558146930762764800), (3215, 308295469370518587417600), (3225, 308295469370518587417600), (3226, 306793116293861525529600), (3228, 462443204055777881126400), (3229, 306793116293861525529600), (3231, 306793116293861525529600)]

def merged1018 : Integer.Sparse (Fin 3237) := [(501, -48118441106470019342400), (507, -16039480368823339780800), (1068, -17025249987835979904000), (1167, -16039480368823339780800), (1178, -5675083329278659968000), (2819, 16039480368823339780800), (2820, 5675083329278659968000)]

def merged1019 : Integer.Sparse (Fin 3237) := [(299, 225506864633299200), (426, 676520593899897600), (507, -3638152478352672000), (776, -11590978028957913600), (862, -3863659342985971200), (1167, -3863659342985971200), (2819, 3638152478352672000)]

def merged1020 : Integer.Sparse (Fin 3237) := [(299, 225506864633299200), (426, 676520593899897600), (501, -48118441106470019342400), (507, -16043118521301692452800), (776, -11590978028957913600), (862, -3863659342985971200), (1068, -17025249987835979904000), (1167, -16043344028166325752000), (1178, -5675083329278659968000), (2819, 16043118521301692452800), (2820, 5675083329278659968000)]

def merged1021 : Integer.Sparse (Fin 3237) := [(285, -34025955354424049184000), (414, -68051910708848098368000), (438, -34025955354424049184000), (471, 422984682030194158694400), (476, 177466385660673030163200), (1145, 211492341015097079347200), (2817, -177466385660673030163200)]

def merged1022 : Integer.Sparse (Fin 3237) := [(343, 48957114625143653376000), (356, 6119639328142956672000), (568, 73435671937715480064000), (599, -68069693297127500697600), (606, -34034846648563750348800), (651, -34034846648563750348800), (997, 48957114625143653376000), (1017, 6119639328142956672000), (1117, 73435671937715480064000), (2829, 34034846648563750348800), (2833, -24478557312571826688000)]

def merged1023 : Integer.Sparse (Fin 3237) := [(343, 48957114625143653376000), (356, 6119639328142956672000), (476, -211491258249555631872000), (568, 73435671937715480064000), (599, -68069693297127500697600), (606, -34034846648563750348800), (651, -34034846648563750348800), (789, -422982516499111263744000), (818, -422982516499111263744000), (997, 48957114625143653376000), (1017, 6119639328142956672000), (1117, 73435671937715480064000), (1145, -211491258249555631872000), (2817, 211491258249555631872000), (2829, 34034846648563750348800), (2833, -24478557312571826688000)]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def merged1024 : Integer.Sparse (Fin 3237) := [(285, -34025955354424049184000), (343, 48957114625143653376000), (356, 6119639328142956672000), (414, -68051910708848098368000), (438, -34025955354424049184000), (471, 422984682030194158694400), (476, -34024872588882601708800), (568, 73435671937715480064000), (599, -68069693297127500697600), (606, -34034846648563750348800), (651, -34034846648563750348800), (789, -422982516499111263744000), (818, -422982516499111263744000), (997, 48957114625143653376000), (1017, 6119639328142956672000), (1117, 73435671937715480064000), (1145, 1082765541447475200), (2817, 34024872588882601708800), (2829, 34034846648563750348800), (2833, -24478557312571826688000)]

def merged1025 : Integer.Sparse (Fin 3237) := [(285, -34025955354424049184000), (299, 225506864633299200), (343, 48957114625143653376000), (356, 6119639328142956672000), (414, -68051910708848098368000), (426, 676520593899897600), (438, -34025955354424049184000), (471, 422984682030194158694400), (476, -34024872588882601708800), (501, -48118441106470019342400), (507, -16043118521301692452800), (568, 73435671937715480064000), (599, -68069693297127500697600), (606, -34034846648563750348800), (651, -34034846648563750348800), (776, -11590978028957913600), (789, -422982516499111263744000), (818, -422982516499111263744000), (862, -3863659342985971200), (997, 48957114625143653376000), (1017, 6119639328142956672000), (1068, -17025249987835979904000), (1117, 73435671937715480064000), (1145, 1082765541447475200), (1167, -16043344028166325752000), (1178, -5675083329278659968000), (2817, 34024872588882601708800), (2819, 16043118521301692452800), (2820, 5675083329278659968000), (2829, 34034846648563750348800), (2833, -24478557312571826688000)]

def merged1026 : Integer.Sparse (Fin 3237) := [(343, -10344189432449953382400), (356, -2586047358112488345600), (997, -48955207809026856960000), (1017, -6119400976128357120000), (1117, -73432811713540285440000), (2833, -3533353618015868774400)]

def merged1027 : Integer.Sparse (Fin 3237) := [(280, 9836233386673881600), (289, 3278744462224627200), (304, 9836233386673881600), (330, 3278744462224627200), (388, 430855505773056000), (402, 143618501924352000), (410, 19672466773347763200), (433, 9836233386673881600), (446, 861711011546112000), (459, 430855505773056000), (485, 430855505773056000), (513, 143618501924352000), (621, 10267088892446937600), (689, 3422362964148979200), (2818, -16250103809198784000)]

def merged1028 : Integer.Sparse (Fin 3237) := [(0, -162298817856000), (3, -3245976357120000), (4, -811494089280000), (261, -1622988178560000), (280, 9836233386673881600), (289, 3278744462224627200), (304, 9836233386673881600), (330, 3278744462224627200), (388, 430855505773056000), (402, 143618501924352000), (410, 19672466773347763200), (433, 9836233386673881600), (446, 861711011546112000), (459, 430855505773056000), (485, 430855505773056000), (513, 143618501924352000), (606, 350565446568960000), (621, 10267088892446937600), (664, 233710297712640000), (689, 3422362964148979200), (1068, 350565446568960000), (1178, 233710297712640000), (2323, 29213787214080000), (2818, -16250103809198784000), (2820, -116855148856320000)]

def merged1029 : Integer.Sparse (Fin 3237) := [(0, -162298817856000), (3, -3245976357120000), (4, -811494089280000), (261, -1622988178560000), (280, 9836233386673881600), (289, 3278744462224627200), (304, 9836233386673881600), (330, 3278744462224627200), (343, -10344189432449953382400), (356, -2586047358112488345600), (388, 430855505773056000), (402, 143618501924352000), (410, 19672466773347763200), (433, 9836233386673881600), (446, 861711011546112000), (459, 430855505773056000), (485, 430855505773056000), (513, 143618501924352000), (606, 350565446568960000), (621, 10267088892446937600), (664, 233710297712640000), (689, 3422362964148979200), (997, -48955207809026856960000), (1017, -6119400976128357120000), (1068, 350565446568960000), (1117, -73432811713540285440000), (1178, 233710297712640000), (2323, 29213787214080000), (2818, -16250103809198784000), (2820, -116855148856320000), (2833, -3533353618015868774400)]

def merged1030 : Integer.Sparse (Fin 3237) := [(280, -34036037252898849907200), (289, -2909619095666976000), (304, -8728857287000928000), (330, -2909619095666976000), (410, -68072074505797699814400), (433, -34036037252898849907200), (2818, 34038946871994516883200)]

def merged1031 : Integer.Sparse (Fin 3237) := [(355, -1555112456522956800000), (580, -4665337369568870400000), (698, -1555112456522956800000), (700, -1555112456522956800000), (2808, -241384039206912000), (2810, -30173004900864000), (2814, -362076058810368000), (2818, -241384039206912000), (2833, 1555082283518055936000)]

def merged1032 : Integer.Sparse (Fin 3237) := [(330, -15224790808470536294400), (355, -1555112456522956800000), (433, -45674372425411608883200), (580, -4665337369568870400000), (689, -15224790808470536294400), (698, -1555112456522956800000), (700, -1555112456522956800000), (2808, -241384039206912000), (2810, -30173004900864000), (2814, -362076058810368000), (2818, 15224549424431329382400), (2833, 1555082283518055936000)]

def merged1033 : Integer.Sparse (Fin 3237) := [(280, -34036037252898849907200), (289, -2909619095666976000), (304, -8728857287000928000), (330, -15227700427566203270400), (355, -1555112456522956800000), (410, -68072074505797699814400), (433, -79710409678310458790400), (580, -4665337369568870400000), (689, -15224790808470536294400), (698, -1555112456522956800000), (700, -1555112456522956800000), (2808, -241384039206912000), (2810, -30173004900864000), (2814, -362076058810368000), (2818, 49263496296425846265600), (2833, 1555082283518055936000)]

def merged1034 : Integer.Sparse (Fin 3237) := [(0, -162298817856000), (3, -3245976357120000), (4, -811494089280000), (261, -1622988178560000), (280, -34026201019512176025600), (289, 369125366557651200), (304, 1107376099672953600), (330, -15224421683103978643200), (343, -10344189432449953382400), (355, -1555112456522956800000), (356, -2586047358112488345600), (388, 430855505773056000), (402, 143618501924352000), (410, -68052402039024352051200), (433, -79700573444923784908800), (446, 861711011546112000), (459, 430855505773056000), (485, 430855505773056000), (513, 143618501924352000), (580, -4665337369568870400000), (606, 350565446568960000), (621, 10267088892446937600), (664, 233710297712640000), (689, -15221368445506387315200), (698, -1555112456522956800000), (700, -1555112456522956800000), (997, -48955207809026856960000), (1017, -6119400976128357120000), (1068, 350565446568960000), (1117, -73432811713540285440000), (1178, 233710297712640000), (2323, 29213787214080000), (2808, -241384039206912000), (2810, -30173004900864000), (2814, -362076058810368000), (2818, 49247246192616647481600), (2820, -116855148856320000), (2833, -1978271334497812838400)]

def merged1035 : Integer.Sparse (Fin 3237) := [(0, -162298817856000), (3, -3245976357120000), (4, -811494089280000), (261, -1622988178560000), (280, -34026201019512176025600), (285, -34025955354424049184000), (289, 369125366557651200), (299, 225506864633299200), (304, 1107376099672953600), (330, -15224421683103978643200), (343, 38612925192693699993600), (355, -1555112456522956800000), (356, 3533591970030468326400), (388, 430855505773056000), (402, 143618501924352000), (410, -68052402039024352051200), (414, -68051910708848098368000), (426, 676520593899897600), (433, -79700573444923784908800), (438, -34025955354424049184000), (446, 861711011546112000), (459, 430855505773056000), (471, 422984682030194158694400), (476, -34024872588882601708800), (485, 430855505773056000), (501, -48118441106470019342400), (507, -16043118521301692452800), (513, 143618501924352000), (568, 73435671937715480064000), (580, -4665337369568870400000), (599, -68069693297127500697600), (606, -34034496083117181388800), (621, 10267088892446937600), (651, -34034846648563750348800), (664, 233710297712640000), (689, -15221368445506387315200), (698, -1555112456522956800000), (700, -1555112456522956800000), (776, -11590978028957913600), (789, -422982516499111263744000), (818, -422982516499111263744000), (862, -3863659342985971200), (997, 1906816116796416000), (1017, 238352014599552000), (1068, -17024899422389410944000), (1117, 2860224175194624000), (1145, 1082765541447475200), (1167, -16043344028166325752000), (1178, -5674849618980947328000), (2323, 29213787214080000), (2808, -241384039206912000), (2810, -30173004900864000), (2814, -362076058810368000), (2817, 34024872588882601708800), (2818, 49247246192616647481600), (2819, 16043118521301692452800), (2820, 5674966474129803648000), (2829, 34034846648563750348800), (2833, -26456828647069639526400)]

def merged1036 : Integer.Sparse (Fin 3237) := [(699, 7552827555840000), (1171, -33899733511841585404800), (1173, -11299903617786305961600), (1179, -11299911170613861801600), (1428, 22658482667520000), (1630, -11299903617786305961600), (2818, 11299903617786305961600)]

def merged1037 : Integer.Sparse (Fin 3237) := [(346, -33124266012654183628800), (520, 28238356030072868114400), (571, -66248532025308367257600), (660, -33124266012654183628800), (674, -33124266012654183628800), (695, -33124266012654183628800), (1073, 84715068090218604343200), (1173, 28238356030072868114400), (1179, 28238356030072868114400), (2818, -28238356030072868114400), (2832, 33124266012654183628800)]

def merged1038 : Integer.Sparse (Fin 3237) := [(346, -33124266012654183628800), (520, 28238356030072868114400), (571, -66248532025308367257600), (660, -33124266012654183628800), (674, -33124266012654183628800), (695, -33124266012654183628800), (699, 7552827555840000), (1073, 84715068090218604343200), (1171, -33899733511841585404800), (1173, 16938452412286562152800), (1179, 16938444859459006312800), (1428, 22658482667520000), (1630, -11299903617786305961600), (2818, -16938452412286562152800), (2832, 33124266012654183628800)]

def merged1039 : Integer.Sparse (Fin 3237) := [(324, -28126801140905288908800), (557, -56253602281810577817600), (591, 22341565876800877056000), (594, -28126801140905288908800), (660, -28126801140905288908800), (662, -28126801140905288908800), (894, 44683131753601754112000), (898, 22341565876800877056000), (938, 22341565876800877056000), (1473, 22341565876800877056000), (2831, -22341565876800877056000), (2832, 28126801140905288908800)]

def merged1040 : Integer.Sparse (Fin 3237) := [(517, -34489907629859349108000), (1067, -68979815259718698216000), (1170, -92245922009240349168000), (1171, -80612868634479523692000), (1172, -46122961004620174584000), (1176, -80612868634479523692000), (1179, -34489907629859349108000), (1579, -46122961004620174584000), (2818, 80612868634479523692000)]

def merged1041 : Integer.Sparse (Fin 3237) := [(517, -34489907629859349108000), (684, -6531306164169292800), (1067, -68979815259718698216000), (1170, -92245922009240349168000), (1171, -80619399940643692984800), (1172, -46122961004620174584000), (1176, -80612868634479523692000), (1179, -34489907629859349108000), (1414, -13062612328338585600), (1579, -46129492310784343876800), (1630, -6531306164169292800), (2818, 80619399940643692984800)]

def merged1042 : Integer.Sparse (Fin 3237) := [(324, -28126801140905288908800), (517, -34489907629859349108000), (557, -56253602281810577817600), (591, 22341565876800877056000), (594, -28126801140905288908800), (660, -28126801140905288908800), (662, -28126801140905288908800), (684, -6531306164169292800), (894, 44683131753601754112000), (898, 22341565876800877056000), (938, 22341565876800877056000), (1067, -68979815259718698216000), (1170, -92245922009240349168000), (1171, -80619399940643692984800), (1172, -46122961004620174584000), (1176, -80612868634479523692000), (1179, -34489907629859349108000), (1414, -13062612328338585600), (1473, 22341565876800877056000), (1579, -46129492310784343876800), (1630, -6531306164169292800), (2818, 80619399940643692984800), (2831, -22341565876800877056000), (2832, 28126801140905288908800)]

def merged1043 : Integer.Sparse (Fin 3237) := [(324, -28126801140905288908800), (346, -33124266012654183628800), (517, -34489907629859349108000), (520, 28238356030072868114400), (557, -56253602281810577817600), (571, -66248532025308367257600), (591, 22341565876800877056000), (594, -28126801140905288908800), (660, -61251067153559472537600), (662, -28126801140905288908800), (674, -33124266012654183628800), (684, -6531306164169292800), (695, -33124266012654183628800), (699, 7552827555840000), (894, 44683131753601754112000), (898, 22341565876800877056000), (938, 22341565876800877056000), (1067, -68979815259718698216000), (1073, 84715068090218604343200), (1170, -92245922009240349168000), (1171, -114519133452485278389600), (1172, -46122961004620174584000), (1173, 16938452412286562152800), (1176, -80612868634479523692000), (1179, -17551462770400342795200), (1414, -13062612328338585600), (1428, 22658482667520000), (1473, 22341565876800877056000), (1579, -46129492310784343876800), (1630, -11306434923950475254400), (2818, 63680947528357130832000), (2831, -22341565876800877056000), (2832, 61251067153559472537600)]

def merged1044 : Integer.Sparse (Fin 3237) := [(340, 67872300910007153817600), (566, 135744601820014307635200), (672, 67872300910007153817600), (693, 67872300910007153817600), (697, 67872300910007153817600), (746, -43412522391413834803200), (877, -86825044782827669606400), (884, -43412522391413834803200), (916, -43412522391413834803200), (1786, -43412522391413834803200), (2832, -67872300910007153817600), (2840, 43412522391413834803200)]

def merged1045 : Integer.Sparse (Fin 3237) := [(489, 1761047075114611200), (492, 880523537557305600), (493, 880523537557305600), (518, 880523537557305600), (1155, -119831254577894412201600), (1157, -59915627288947206100800), (1159, -59914746765409648795200), (1176, -59915627288947206100800), (2310, -59915627288947206100800), (2818, 59914746765409648795200)]

def merged1046 : Integer.Sparse (Fin 3237) := [(489, 1761047075114611200), (492, 880523537557305600), (493, 880523537557305600), (518, 880523537557305600), (1155, -119831254577894412201600), (1157, -59915627288947206100800), (1159, 27262122495868529488800), (1176, -59915627288947206100800), (1332, 87176869261278178284000), (2252, 174353738522556356568000), (2257, 87176869261278178284000), (2310, 27261241972330972183200), (2818, -27262122495868529488800)]

def merged1047 : Integer.Sparse (Fin 3237) := [(340, 67872300910007153817600), (489, 1761047075114611200), (492, 880523537557305600), (493, 880523537557305600), (518, 880523537557305600), (566, 135744601820014307635200), (672, 67872300910007153817600), (693, 67872300910007153817600), (697, 67872300910007153817600), (746, -43412522391413834803200), (877, -86825044782827669606400), (884, -43412522391413834803200), (916, -43412522391413834803200), (1155, -119831254577894412201600), (1157, -59915627288947206100800), (1159, 27262122495868529488800), (1176, -59915627288947206100800), (1332, 87176869261278178284000), (1786, -43412522391413834803200), (2252, 174353738522556356568000), (2257, 87176869261278178284000), (2310, 27261241972330972183200), (2818, -27262122495868529488800), (2832, -67872300910007153817600), (2840, 43412522391413834803200)]

def merged1048 : Integer.Sparse (Fin 3237) := [(493, 34024466343935054131200), (518, 50694589379139345309600), (1053, 68048932687870108262400), (1070, 101389178758278690619200), (1096, 34024466343935054131200), (1157, 34024466343935054131200), (1159, 84719055723074399440800), (1172, 50694589379139345309600), (1176, 50694589379139345309600), (2818, -84719055723074399440800)]

def merged1049 : Integer.Sparse (Fin 3237) := [(315, -48881604363298269696000), (549, -48881604363298269696000), (585, -48881604363298269696000), (627, -6141511972205568000), (636, -48881604363298269696000), (654, -48881604363298269696000), (659, -48881604363298269696000), (1172, -6141511972205568000), (1332, -6141511972205568000), (1375, -12283023944411136000), (1579, -6141511972205568000), (2818, 6141511972205568000), (2831, 48881604363298269696000)]

def merged1050 : Integer.Sparse (Fin 3237) := [(315, -48881604363298269696000), (549, -48881604363298269696000), (576, -854953460832996403200), (585, -48881604363298269696000), (627, -6141511972205568000), (636, -48881604363298269696000), (654, -48881604363298269696000), (659, -48881604363298269696000), (875, -1709906921665992806400), (883, -854953460832996403200), (913, -854953460832996403200), (1172, -6141511972205568000), (1332, -6141511972205568000), (1375, -12283023944411136000), (1426, -854953460832996403200), (1579, -6141511972205568000), (2818, 6141511972205568000), (2831, 48881604363298269696000), (2832, 854953460832996403200)]

def merged1051 : Integer.Sparse (Fin 3237) := [(315, -48881604363298269696000), (493, 34024466343935054131200), (518, 50694589379139345309600), (549, -48881604363298269696000), (576, -854953460832996403200), (585, -48881604363298269696000), (627, -6141511972205568000), (636, -48881604363298269696000), (654, -48881604363298269696000), (659, -48881604363298269696000), (875, -1709906921665992806400), (883, -854953460832996403200), (913, -854953460832996403200), (1053, 68048932687870108262400), (1070, 101389178758278690619200), (1096, 34024466343935054131200), (1157, 34024466343935054131200), (1159, 84719055723074399440800), (1172, 50688447867167139741600), (1176, 50694589379139345309600), (1332, -6141511972205568000), (1375, -12283023944411136000), (1426, -854953460832996403200), (1579, -6141511972205568000), (2818, -84712914211102193872800), (2831, 48881604363298269696000), (2832, 854953460832996403200)]

def merged1052 : Integer.Sparse (Fin 3237) := [(315, -48881604363298269696000), (340, 67872300910007153817600), (489, 1761047075114611200), (492, 880523537557305600), (493, 34025346867472611436800), (518, 50695469902676902615200), (549, -48881604363298269696000), (566, 135744601820014307635200), (576, -854953460832996403200), (585, -48881604363298269696000), (627, -6141511972205568000), (636, -48881604363298269696000), (654, -48881604363298269696000), (659, -48881604363298269696000), (672, 67872300910007153817600), (693, 67872300910007153817600), (697, 67872300910007153817600), (746, -43412522391413834803200), (875, -1709906921665992806400), (877, -86825044782827669606400), (883, -854953460832996403200), (884, -43412522391413834803200), (913, -854953460832996403200), (916, -43412522391413834803200), (1053, 68048932687870108262400), (1070, 101389178758278690619200), (1096, 34024466343935054131200), (1155, -119831254577894412201600), (1157, -25891160945012151969600), (1159, 111981178218942928929600), (1172, 50688447867167139741600), (1176, -9221037909807860791200), (1332, 87170727749305972716000), (1375, -12283023944411136000), (1426, -854953460832996403200), (1579, -6141511972205568000), (1786, -43412522391413834803200), (2252, 174353738522556356568000), (2257, 87176869261278178284000), (2310, 27261241972330972183200), (2818, -111975036706970723361600), (2831, 48881604363298269696000), (2832, -67017347449174157414400), (2840, 43412522391413834803200)]

def merged1053 : Integer.Sparse (Fin 3237) := [(315, -48881604363298269696000), (324, -28126801140905288908800), (340, 67872300910007153817600), (346, -33124266012654183628800), (489, 1761047075114611200), (492, 880523537557305600), (493, 34025346867472611436800), (517, -34489907629859349108000), (518, 50695469902676902615200), (520, 28238356030072868114400), (549, -48881604363298269696000), (557, -56253602281810577817600), (566, 135744601820014307635200), (571, -66248532025308367257600), (576, -854953460832996403200), (585, -48881604363298269696000), (591, 22341565876800877056000), (594, -28126801140905288908800), (627, -6141511972205568000), (636, -48881604363298269696000), (654, -48881604363298269696000), (659, -48881604363298269696000), (660, -61251067153559472537600), (662, -28126801140905288908800), (672, 67872300910007153817600), (674, -33124266012654183628800), (684, -6531306164169292800), (693, 67872300910007153817600), (695, -33124266012654183628800), (697, 67872300910007153817600), (699, 7552827555840000), (746, -43412522391413834803200), (875, -1709906921665992806400), (877, -86825044782827669606400), (883, -854953460832996403200), (884, -43412522391413834803200), (894, 44683131753601754112000), (898, 22341565876800877056000), (913, -854953460832996403200), (916, -43412522391413834803200), (938, 22341565876800877056000), (1053, 68048932687870108262400), (1067, -68979815259718698216000), (1070, 101389178758278690619200), (1073, 84715068090218604343200), (1096, 34024466343935054131200), (1155, -119831254577894412201600), (1157, -25891160945012151969600), (1159, 111981178218942928929600), (1170, -92245922009240349168000), (1171, -114519133452485278389600), (1172, 4565486862546965157600), (1173, 16938452412286562152800), (1176, -89833906544287384483200), (1179, -17551462770400342795200), (1332, 87170727749305972716000), (1375, -12283023944411136000), (1414, -13062612328338585600), (1426, -854953460832996403200), (1428, 22658482667520000), (1473, 22341565876800877056000), (1579, -46135633822756549444800), (1630, -11306434923950475254400), (1786, -43412522391413834803200), (2252, 174353738522556356568000), (2257, 87176869261278178284000), (2310, 27261241972330972183200), (2818, -48294089178613592529600), (2831, 26540038486497392640000), (2832, -5766280295614684876800), (2840, 43412522391413834803200)]

def merged1054 : Integer.Sparse (Fin 3237) := [(0, -162298817856000), (3, -3245976357120000), (4, -811494089280000), (261, -1622988178560000), (280, -34026201019512176025600), (285, -34025955354424049184000), (289, 369125366557651200), (299, 225506864633299200), (304, 1107376099672953600), (315, -48881604363298269696000), (324, -28126801140905288908800), (330, -15224421683103978643200), (340, 67872300910007153817600), (343, 38612925192693699993600), (346, -33124266012654183628800), (355, -1555112456522956800000), (356, 3533591970030468326400), (388, 430855505773056000), (402, 143618501924352000), (410, -68052402039024352051200), (414, -68051910708848098368000), (426, 676520593899897600), (433, -79700573444923784908800), (438, -34025955354424049184000), (446, 861711011546112000), (459, 430855505773056000), (471, 422984682030194158694400), (476, -34024872588882601708800), (485, 430855505773056000), (489, 1761047075114611200), (492, 880523537557305600), (493, 34025346867472611436800), (501, -48118441106470019342400), (507, -16043118521301692452800), (513, 143618501924352000), (517, -34489907629859349108000), (518, 50695469902676902615200), (520, 28238356030072868114400), (549, -48881604363298269696000), (557, -56253602281810577817600), (566, 135744601820014307635200), (568, 73435671937715480064000), (571, -66248532025308367257600), (576, -854953460832996403200), (580, -4665337369568870400000), (585, -48881604363298269696000), (591, 22341565876800877056000), (594, -28126801140905288908800), (599, -68069693297127500697600), (606, -34034496083117181388800), (621, 10267088892446937600), (627, -6141511972205568000), (636, -48881604363298269696000), (651, -34034846648563750348800), (654, -48881604363298269696000), (659, -48881604363298269696000), (660, -61251067153559472537600), (662, -28126801140905288908800), (664, 233710297712640000), (672, 67872300910007153817600), (674, -33124266012654183628800), (684, -6531306164169292800), (689, -15221368445506387315200), (693, 67872300910007153817600), (695, -33124266012654183628800), (697, 67872300910007153817600), (698, -1555112456522956800000), (699, 7552827555840000), (700, -1555112456522956800000), (746, -43412522391413834803200), (776, -11590978028957913600), (789, -422982516499111263744000), (818, -422982516499111263744000), (862, -3863659342985971200), (875, -1709906921665992806400), (877, -86825044782827669606400), (883, -854953460832996403200), (884, -43412522391413834803200), (894, 44683131753601754112000), (898, 22341565876800877056000), (913, -854953460832996403200), (916, -43412522391413834803200), (938, 22341565876800877056000), (997, 1906816116796416000), (1017, 238352014599552000), (1053, 68048932687870108262400), (1067, -68979815259718698216000), (1068, -17024899422389410944000), (1070, 101389178758278690619200), (1073, 84715068090218604343200), (1096, 34024466343935054131200), (1117, 2860224175194624000), (1145, 1082765541447475200), (1155, -119831254577894412201600), (1157, -25891160945012151969600), (1159, 111981178218942928929600), (1167, -16043344028166325752000), (1170, -92245922009240349168000), (1171, -114519133452485278389600), (1172, 4565486862546965157600), (1173, 16938452412286562152800), (1176, -89833906544287384483200), (1178, -5674849618980947328000), (1179, -17551462770400342795200), (1332, 87170727749305972716000), (1375, -12283023944411136000), (1414, -13062612328338585600), (1426, -854953460832996403200), (1428, 22658482667520000), (1473, 22341565876800877056000), (1579, -46135633822756549444800), (1630, -11306434923950475254400), (1786, -43412522391413834803200), (2252, 174353738522556356568000), (2257, 87176869261278178284000), (2310, 27261241972330972183200), (2323, 29213787214080000), (2808, -241384039206912000), (2810, -30173004900864000), (2814, -362076058810368000), (2817, 34024872588882601708800), (2818, 953157014003054952000), (2819, 16043118521301692452800), (2820, 5674966474129803648000), (2829, 34034846648563750348800), (2831, 26540038486497392640000), (2832, -5766280295614684876800), (2833, -26456828647069639526400), (2840, 43412522391413834803200)]

set_option maxHeartbeats 1000000 in
def merged1055 : Integer.Sparse (Fin 3237) := [(0, -4550189575593013194192), (3, 1156337132697215288400), (4, -1995377553852545849700), (32, 2958191298719299505100), (66, 3769343306789930889600), (71, 630109704879715468800), (160, 18319696906918468488000), (218, -3771871244008245201600), (222, -5638245750067458124800), (225, 3331745427387085833600), (255, 333011299533994972800), (256, 13233520920227200320000), (260, -2352529248518925831600), (261, -4743278119193576062800), (274, -999033898601984918400), (280, -34026201019512176025600), (285, -34027062730523722137600), (299, -143618501924352000), (304, 1107376099672953600), (308, -1107376099672953600), (315, -48881604363298269696000), (318, 56292462603027247564800), (321, -89862403840236295833600), (324, -28126801140905288908800), (325, 2291872960022446080000), (330, -15224421683103978643200), (340, 67872300910007153817600), (343, 38612556067327142342400), (346, -33124266012654183628800), (349, 4806228838652546457600), (351, 2380899296640117657600), (355, -1555112456522956800000), (356, -820112129438515200000), (362, -44454557741508943257600), (367, 151903017209047694284800), (377, 1078193446027455744000), (388, 430855505773056000), (399, -90091795788288000), (402, 113587903328256000), (406, -30030598596096000), (410, -68052402039024352051200), (414, -68051910708848098368000), (426, 676520593899897600), (433, -79700573444923784908800), (438, -34025955354424049184000), (446, 861711011546112000), (459, 430855505773056000), (471, 422984682030194158694400), (476, -34024872588882601708800), (478, 1761047075114611200), (481, 880523537557305600), (485, 430855505773056000), (489, 1761047075114611200), (491, 880523537557305600), (492, 880523537557305600), (493, 34025346867472611436800), (501, -48118441106470019342400), (503, 880523537557305600), (507, -16043118521301692452800), (513, 143618501924352000), (516, 2220942473802420807600), (517, -34489907629859349108000), (518, 50695469902676902615200), (520, 28238356030072868114400), (521, 29056909249768657572000), (529, -2214752199345907200), (541, -1107376099672953600), (549, -48881604363298269696000), (551, -58242692533073113497600), (554, -111557543184497546035200), (557, -56253602281810577817600), (566, 135744601820014307635200), (568, 73435671937715480064000), (571, -66248532025308367257600), (574, 33492668657549766739200), (576, 40371376677074879385600), (580, -4665337369568870400000), (585, -48881604363298269696000), (588, 18567791813054753740800), (591, -33437205715447895961600), (594, -28126801140905288908800), (599, -68069693297127500697600), (602, 574094896129316061964800), (606, -34034496083117181388800), (609, 194558094389809866643200), (614, 6141511972205568000), (621, 10267088892446937600), (625, 97279047194904933321600), (627, -6141511972205568000), (634, 287047448064658030982400), (636, -48881604363298269696000), (641, -55778771592248773017600), (651, -34034846648563750348800), (654, -48881604363298269696000), (656, 56016233813695721932800), (659, -104661483331646715667200), (660, -61251067153559472537600), (662, -28126801140905288908800), (664, 25829586778363461273600), (668, 97279047194904933321600), (672, 67872300910007153817600), (674, -33124266012654183628800), (677, 13742110045969291929600), (684, -6531306164169292800), (689, -15221368445506387315200), (693, 67872300910007153817600), (695, -33124266012654183628800), (697, 81614041830609888096000), (698, -1555112456522956800000), (699, 7552827555840000), (700, -1555112456522956800000), (719, 371973298914070434201600), (722, -68167264495975045632000), (744, 133742200263407414784000), (746, -77496154639401357619200), (769, -194545811365865455507200), (776, -11590978028957913600), (780, -97272905682932727753600), (784, -287047448064658030982400), (789, -422982516499111263744000), (792, -287047448064658030982400), (800, -574094896129316061964800), (810, 207203057941763816755200), (818, -422982516499111263744000), (825, -85690037658895329945600), (828, 185985542080935544147200), (841, -97272905682932727753600), (862, -3863659342985971200), (869, -12666966526434673152000), (875, -1709906921665992806400), (877, -86825044782827669606400), (883, -854953460832996403200), (884, -43412522391413834803200), (894, 44683131753601754112000), (898, 22341565876800877056000), (913, -854953460832996403200), (916, -43412522391413834803200), (938, 22341565876800877056000), (970, -90091795788288000), (992, 276147382278039552000), (997, 1876785518200320000), (1008, 276147382278039552000), (1010, 92049127426013184000), (1013, -1678359529534464000), (1016, 92049127426013184000), (1017, 31949033969664000), (1032, -180183591576576000), (1038, -90091795788288000), (1053, 68048932687870108262400), (1063, 38491946859814812252000), (1067, -68979815259718698216000), (1068, 131533715574374400), (1070, 101389178758278690619200), (1073, 84715068090218604343200), (1074, 104195758705410958034400), (1096, 34024466343935054131200), (1112, 552294764556079104000), (1117, 2860224175194624000), (1132, -171498849274368000), (1145, 1082765541447475200), (1151, 880523537557305600), (1154, 276147382278039552000), (1155, -119831254577894412201600), (1157, -25891242352065638049600), (1159, 111981178218942928929600), (1167, -16043344028166325752000), (1170, -92245922009240349168000), (1171, -114519133452485278389600), (1172, 4565486862546965157600), (1173, 16938452412286562152800), (1175, -78779779647398473669200), (1176, -89833996636083172771200), (1178, -7557010212497788224000), (1179, -17551492800998938891200), (1180, 2056668542701692746400), (1332, 87170727749305972716000), (1375, -12283023944411136000), (1385, 68028903480095783769600), (1392, 34014451740047891884800), (1414, -13062612328338585600), (1415, 34014451740047891884800), (1426, -854953460832996403200), (1428, 22658482667520000), (1436, 67462499437709610931200), (1438, 33731249718854805465600), (1466, 33731249718854805465600), (1473, 22341565876800877056000), (1567, 33731249718854805465600), (1571, 6141511972205568000), (1579, -46135715229810035524800), (1589, 34014451740047891884800), (1630, -11306462059634970614400), (1786, -43412522391413834803200), (1810, 338153540070176393068800), (1836, 74180913018743974262400), (1888, 8991305087417864265600), (1889, 8991305087417864265600), (1893, 17982610174835728531200), (1932, -38349139536732690691200), (1957, 8991305087417864265600), (1968, -38536933671314823427200), (2252, 174353738522556356568000), (2257, 87176869261278178284000), (2285, -2476835767558656000), (2308, -15485552233466203324800), (2310, 27261151880535183895200), (2320, -1681254443635200000), (2323, -5019851318000214628800), (2480, 338153540070176393068800), (2487, 17982610174835728531200), (2489, -29357834449314826425600), (2494, 8991305087417864265600), (2518, 74180913018743974262400), (2524, 8991305087417864265600), (2536, -38536933671314823427200), (2553, 17012962031752317657600), (2557, 34025924063504635315200), (2562, 17012962031752317657600), (2580, -30030598596096000), (2604, 68028903480095783769600), (2609, 34014451740047891884800), (2618, 34014451740047891884800), (2633, 67462499437709610931200), (2635, 371884789789031198534400), (2642, 74180913018743974262400), (2649, 67462499437709610931200), (2651, 33731249718854805465600), (2667, 33731249718854805465600), (2679, -67459924394026405516800), (2681, 68028903480095783769600), (2682, -76698279073465381382400), (2684, -105809063930759096208000), (2689, 68028903480095783769600), (2692, 67462499437709610931200), (2697, -58715668898629652851200), (2700, -96817758843341231942400), (2715, 372167991810224284953600), (2717, 599233212797723139283200), (2719, 17982610174835728531200), (2722, 599233212797723139283200), (2725, 17982610174835728531200), (2726, 295094124467594638099200), (2727, 135491402917805394700800), (2729, 9313234581466130918400), (2733, 74180913018743974262400), (2741, 294810922446401551680000), (2742, -9235779635755770451200), (2746, 17982610174835728531200), (2749, -212240765722703569488000), (2751, 51027413771800209542400), (2752, 17012962031752317657600), (2753, 34025924063504635315200), (2756, -16864981098506601379200), (2757, 34025924063504635315200), (2758, 50744211750607123123200), (2762, -8657903269912854182400), (2763, -67459924394026405516800), (2764, 34025924063504635315200), (2765, 101488423501214246246400), (2767, 112717846690058797689600), (2768, 7967998169218454572800), (2782, -154147734685259293708800), (2791, -153396558146930762764800), (2794, -38349139536732690691200), (2797, 112717846690058797689600), (2802, 299616606398861569641600), (2808, -241384039206912000), (2810, -30173004900864000), (2814, -362076058810368000), (2817, 34023992065345044403200), (2818, 953157014003054952000), (2819, 16043118521301692452800), (2820, -10607794966691866515600), (2827, 972866107843499520), (2828, 2918598323530498560), (2829, 34034846648563750348800), (2830, -6141511972205568000), (2831, 82319782944854009157120), (2832, -31193175418589799014400), (2833, -26456828647069639526400), (2835, 972866107843499520), (2836, 2918598323530498560), (2838, -17718062410133003520), (2839, -450894037977340857930240), (2840, -142568289868974321300480), (2848, 1104915157326102528000), (2851, 1104915157326102528000), (2855, 368305052442034176000), (2864, 368305052442034176000), (2868, 2209830314652205056000), (2889, 1104915157326102528000), (2964, -887003722579968000), (3129, 308295469370518587417600), (3132, 154147734685259293708800), (3142, 306793116293861525529600), (3143, 153396558146930762764800), (3146, 153396558146930762764800), (3155, 153396558146930762764800), (3156, 153396558146930762764800), (3159, 306793116293861525529600), (3167, 154147734685259293708800), (3168, 154147734685259293708800), (3179, 308295469370518587417600), (3189, 153396558146930762764800), (3215, 308295469370518587417600), (3225, 308295469370518587417600), (3226, 306793116293861525529600), (3228, 462443204055777881126400), (3229, 306793116293861525529600), (3231, 306793116293861525529600)]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def merged1056part0 : Integer.Sparse (Fin 3237) := [(0, -42025476345378246452004), (3, -35715667433047240800), (4, -1747519569430563205200), (32, 9959389417498493172900), (66, -2714167436796030700800), (68, 452298377897536665600), (71, -2524915258602168700800), (160, 58722029116377172929600), (162, 904596755795073331200), (218, -57618213843456000), (222, 2470952804333304412800), (225, 12673659420387096028800), (251, -1356895133692609996800), (252, -2064943097210356473600), (255, 12665263534566096921600), (256, 50148406428810239390400), (260, 617560911346348620000), (261, -120978822714419793583320), (273, -651540734066476800), (274, -13738952072108466302400), (280, -34026201019512176025600), (285, -34027062730523722137600), (299, -143618501924352000), (304, 1107376099672953600), (308, -1107376099672953600), (315, -48881604363298269696000), (318, 56292462603027247564800), (321, -89862403840236295833600), (324, -28126801140905288908800), (325, 2291872960022446080000), (330, -15224421683103978643200), (340, 67872300910007153817600), (343, 38612556067327142342400), (346, -33124266012654183628800), (349, 4806228838652546457600), (351, 2380899296640117657600), (355, -1555112456522956800000), (356, -820112129438515200000), (362, -44454557741508943257600), (367, 151903017209047694284800), (377, 1078193446027455744000), (388, 430855505773056000), (399, -90091795788288000), (402, 113587903328256000), (406, -30030598596096000), (410, -68052402039024352051200), (414, -68051910708848098368000), (426, 676520593899897600), (433, -79700573444923784908800), (438, -34025955354424049184000), (446, 861711011546112000), (459, 430855505773056000), (471, 422984682030194158694400), (476, -34024872588882601708800), (478, 1761047075114611200), (481, 880523537557305600), (485, 430855505773056000), (489, 1761047075114611200), (491, 880523537557305600), (492, 880523537557305600), (493, 34025346867472611436800), (501, -48118441106470019342400), (503, 880523537557305600), (507, -16043118521301692452800)]

def merged1056part1 : Integer.Sparse (Fin 3237) := [(513, 143618501924352000), (516, 2220942473802420807600), (517, -34489907629859349108000), (518, 50695469902676902615200), (520, 28238356030072868114400), (521, 29056909249768657572000), (529, -2214752199345907200), (541, -1107376099672953600), (549, -48881604363298269696000), (551, -58242692533073113497600), (554, -111557543184497546035200), (557, -56253602281810577817600), (566, 135744601820014307635200), (568, 73435671937715480064000), (571, -66248532025308367257600), (574, 33492668657549766739200), (576, 40371376677074879385600), (580, -4665337369568870400000), (585, -48881604363298269696000), (588, 18567791813054753740800), (591, -33437205715447895961600), (594, -28126801140905288908800), (599, -68069693297127500697600), (602, 574094896129316061964800), (606, -34034496083117181388800), (609, 194558094389809866643200), (614, 6141511972205568000), (621, 10267088892446937600), (625, 97279047194904933321600), (627, -6141511972205568000), (634, 287047448064658030982400), (636, -48881604363298269696000), (641, -55778771592248773017600), (651, -34034846648563750348800), (654, -48881604363298269696000), (656, 56016233813695721932800), (659, -104661483331646715667200), (660, -61251067153559472537600), (662, -28126801140905288908800), (664, 25829586778363461273600), (668, 97279047194904933321600), (672, 67872300910007153817600), (674, -33124266012654183628800), (677, 13742110045969291929600), (684, -6531306164169292800), (689, -15221368445506387315200), (693, 67872300910007153817600), (695, -33124266012654183628800), (697, 81614041830609888096000), (698, -1555112456522956800000), (699, 7552827555840000), (700, -1555112456522956800000), (719, 371973298914070434201600), (722, -68167264495975045632000), (744, 133742200263407414784000), (746, -77496154639401357619200), (769, -194545811365865455507200), (776, -11590978028957913600), (780, -97272905682932727753600), (784, -287047448064658030982400), (789, -422982516499111263744000), (792, -287047448064658030982400), (800, -574094896129316061964800), (810, 207203057941763816755200)]

def merged1056part2 : Integer.Sparse (Fin 3237) := [(818, -422982516499111263744000), (825, -85690037658895329945600), (828, 185985542080935544147200), (841, -97272905682932727753600), (862, -3863659342985971200), (869, -12666966526434673152000), (875, -1709906921665992806400), (877, -86825044782827669606400), (883, -854953460832996403200), (884, -43412522391413834803200), (894, 44683131753601754112000), (898, 22341565876800877056000), (913, -854953460832996403200), (916, -43412522391413834803200), (938, 22341565876800877056000), (970, -90091795788288000), (992, 276147382278039552000), (997, 1876785518200320000), (1008, 276147382278039552000), (1010, 92049127426013184000), (1013, -1678359529534464000), (1016, 92049127426013184000), (1017, 31949033969664000), (1032, -180183591576576000), (1038, -90091795788288000), (1053, 68048932687870108262400), (1063, 38491946859814812252000), (1067, -68979815259718698216000), (1068, 131533715574374400), (1070, 101389178758278690619200), (1073, 84715068090218604343200), (1074, 104195758705410958034400), (1096, 34024466343935054131200), (1112, 552294764556079104000), (1117, 2860224175194624000), (1132, -171498849274368000), (1145, 1082765541447475200), (1151, 880523537557305600), (1154, 276147382278039552000), (1155, -119831254577894412201600), (1157, -25891242352065638049600), (1159, 111981178218942928929600), (1167, -16043344028166325752000), (1170, -92245922009240349168000), (1171, -114519133452485278389600), (1172, 4565486862546965157600), (1173, 16938452412286562152800), (1175, -78779779647398473669200), (1176, -89833996636083172771200), (1178, -7557010212497788224000), (1179, -17551492800998938891200), (1180, 2056668542701692746400), (1332, 87170727749305972716000), (1358, 324847711899648000), (1359, -3952453694334566400), (1361, -3302758270535270400), (1367, 2073673130471308800), (1368, 2723368554270604800), (1370, -4456071311265907200), (1373, -2577290747402649600), (1375, -12283023944411136000), (1376, -2577290747402649600), (1385, 136092789948012657984000), (1387, 68063886467916874214400)]

def merged1056part3 : Integer.Sparse (Fin 3237) := [(1388, 22447674725980893984000), (1389, 44890097607419854809600), (1392, 34014451740047891884800), (1397, 68063886467916874214400), (1414, -13062612328338585600), (1415, 34014451740047891884800), (1417, 68063886467916874214400), (1420, 22449098703687565996800), (1422, -2577290747402649600), (1426, -854953460832996403200), (1428, 22658482667520000), (1436, 135526385905626485145600), (1438, 33726132610087372761600), (1440, -5117108767432704000), (1443, 68058769359149441510400), (1461, -300550665138760108800), (1462, 135520950118330331251200), (1464, 34030512862151962867200), (1466, 73345549091160109276800), (1467, 107678185840222178025600), (1468, 79223481635843174918400), (1471, -300550665138760108800), (1473, 22341565876800877056000), (1476, 68061025724303925734400), (1548, 22447674725980893984000), (1549, 22443072576862760121600), (1560, 44896123734244660684800), (1562, -2577290747402649600), (1567, 33731249718854805465600), (1568, 68063886467916874214400), (1569, -5117108767432704000), (1571, 6141511972205568000), (1579, -46135715229810035524800), (1589, 73628751112353195696000), (1590, 107678185840222178025600), (1591, 44894050061114189376000), (1593, 39614299372305303811200), (1608, 79228598744610607622400), (1616, -300550665138760108800), (1617, 68061025724303925734400), (1618, 39614299372305303811200), (1630, -11306462059634970614400), (1680, -136073227616590878028800), (1681, -68027426743127001292800), (1683, 7898419794736396800), (1684, 5321129047333747200), (1694, -68026977476694567475200), (1695, 8347686227170214400), (1696, 5770395479767564800), (1698, -11147013247610419200), (1700, -6848279817379257600), (1703, -13696559634758515200), (1727, 1285576834410086400), (1728, -1381300025514393600), (1734, 905426768837606400), (1735, -3047026925496960000), (1737, 11375000232394176000), (1741, 7898419794736396800), (1749, 24424112406466979942400), (1750, -68034621212506055923200), (1751, 24424112406466979942400), (1752, -138716535365951017507200), (1753, 249040390293471501043200), (1754, 24424112406466979942400)]

def merged1056part4 : Integer.Sparse (Fin 3237) := [(1755, -138717881120732905756800), (1756, -34014752051869311609600), (1758, 249027222722850235238400), (1760, -138722998229500338460800), (1761, 249027222722850235238400), (1773, 24424112406466979942400), (1775, 34046059024606735008000), (1776, 68060811076476046617600), (1777, 68055693967708613913600), (1780, -83655912480562306684800), (1781, 165385178830781247945600), (1782, 81730961134768617235200), (1784, -180986483870112568435200), (1786, -43412522391413834803200), (1796, -1203725312842752000), (1806, 184923265123889488627200), (1807, 184923265123889488627200), (1808, -195008349204022765017600), (1810, 297163858756865681548800), (1811, 184923265123889488627200), (1815, -95441831575300106265600), (1834, 184923265123889488627200), (1836, 65338161720330765974400), (1837, -252170167687356453091200), (1888, 8991305087417864265600), (1889, 8991305087417864265600), (1893, 17982610174835728531200), (1895, -401241770947584000), (1900, -86566016700546564384000), (1901, -86566016700546564384000), (1902, -188747511212919478579200), (1903, -25545373628093228548800), (1904, -86566016700546564384000), (1910, -51090747256186457097600), (1918, 165385178830781247945600), (1919, 165385178830781247945600), (1920, 165385178830781247945600), (1923, 57088960936608206995200), (1924, 57088960936608206995200), (1930, 280633540549908605875200), (1931, -18467646447197296742400), (1932, -118345304825291797948800), (1933, -202834275081237174816000), (1934, 241316326773930026304000), (1935, -18467646447197296742400), (1938, 105257929318349344992000), (1939, 105257929318349344992000), (1942, 105257929318349344992000), (1944, 105257929318349344992000), (1945, -18467646447197296742400), (1948, 111657419094801623702400), (1950, 43270251405592777372800), (1957, 66080266024026071260800), (1967, 5956465959269683200000), (1968, 42500026232105417136000), (1969, -39597479536110041347200), (1973, 18691912617802780608000), (1974, -51090747256186457097600), (1979, 16724149070931850262400), (2023, -2941724368538726400), (2046, 49748111960702577206400), (2047, 47089607576459286787200), (2050, -4647376896246153216000), (2055, -49700850681850140931200)]

def merged1056part5 : Integer.Sparse (Fin 3237) := [(2068, -1770709794526310400), (2081, 60030487072278394963200), (2087, 244379845826604082022400), (2097, 392414859223790944665600), (2159, 57080909265810451257600), (2164, -101416185705927690864000), (2165, -101416185705927690864000), (2175, -304248557117783072592000), (2177, 249027222722850235238400), (2252, 174353738522556356568000), (2257, 87176869261278178284000), (2285, -2476835767558656000), (2308, -15485552233466203324800), (2310, 27261151880535183895200), (2320, -1681254443635200000), (2323, -5019851318000214628800), (2331, -136073227616590878028800), (2332, -68027426743127001292800), (2335, 5321129047333747200), (2342, -68026977476694567475200), (2343, 8347686227170214400), (2344, 5770395479767564800), (2346, -11147013247610419200), (2348, -6848279817379257600), (2351, -2941724368538726400), (2369, -980574789512908800), (2402, 2979099899308915200), (2405, -4740549990395788800), (2406, -7407426850320268800), (2408, -227986984783756800), (2412, 184923265123889488627200), (2414, -67468217170119883084800), (2415, 184923265123889488627200), (2416, 34326702491416105075200), (2418, 68060811076476046617600), (2429, -138710509239126211632000), (2430, -83655912480562306684800), (2431, -304248557117783072592000), (2433, 184923265123889488627200), (2437, 249028338039821889292800), (2438, -138717881120732905756800), (2439, 81731410401201051052800), (2445, -33734108585059941542400), (2446, -138717881120732905756800), (2447, -180986483870112568435200), (2449, 249027222722850235238400), (2450, 249027222722850235238400), (2458, 165385178830781247945600), (2460, 165385178830781247945600), (2461, 24424112406466979942400), (2465, 24424112406466979942400), (2475, 91841074014586819507200), (2476, 39036527280448459776000), (2477, 336528057803325071040000), (2479, 32145524729348483174400), (2480, 329309383486214164723200), (2481, 16992858573638013830400), (2482, 112434690148938120096000), (2483, -119301284663109624297600), (2484, -32735267962563059913600), (2487, -18409578260014387353600), (2488, -57487669210270560441600), (2489, -109353999737873933683200), (2490, -282503263103858956723200)]

def merged1056part6 : Integer.Sparse (Fin 3237) := [(2491, 391615390495878797808000), (2492, 29078347490276003942400), (2494, 121425995236355984361600), (2495, 25868673448391555712000), (2496, 32145524729348483174400), (2498, 112434690148938120096000), (2499, 29078347490276003942400), (2501, 273450248516061331545600), (2503, 155705390820963331286400), (2512, -79675014149446587782400), (2513, 391172815945128636115200), (2517, 61223872219624487116800), (2518, 65337582387312200649600), (2519, -233478255069553672483200), (2520, 228303320510366172288000), (2524, -93693991488551800617600), (2525, -291432807788889143462400), (2527, 166455618676692191884800), (2528, -102685296575969664883200), (2533, -111756731309622177004800), (2534, -27813232311506356579200), (2535, 29078347490276003942400), (2536, 42780669698914787203200), (2537, -177249126384075630124800), (2538, 121982078389281195254400), (2539, -4535717366826256060800), (2552, -1770709794526310400), (2553, -73624800162628549296000), (2554, -52571429035557343027200), (2555, 92176011801626878137600), (2556, 373947212776593647923200), (2557, 283048867857788387712000), (2558, -40130018176382222155200), (2561, 273458193316880085964800), (2562, 190662054255025035782400), (2563, 10988172690648774768000), (2564, 91245721139957489414400), (2565, 91243233236501759750400), (2566, 17013423331158082617600), (2567, -44335276440117239606400), (2568, -1203725312842752000), (2569, 24430970594029850726400), (2570, -57364148194977698121600), (2571, 240060608033201217763200), (2572, 56839001149427742000000), (2573, 249027222722850235238400), (2575, -2487903455729664000), (2577, -54236568048676396992000), (2578, 91245721139957489414400), (2580, -30030598596096000), (2597, -2342029148024832000), (2600, -323658371226355200), (2601, 6918928921128268800), (2604, 68058168735506602060800), (2605, 24424112406466979942400), (2606, -72992811094537324032000), (2607, 388781296075629382867200), (2608, 24424112406466979942400), (2609, 49748792223670670390400), (2610, -27383062216150664755200), (2611, 244379845826604082022400), (2617, 24424112406466979942400), (2618, 68060510764654626892800), (2619, 136119580435625488128000)]

def merged1056part7 : Integer.Sparse (Fin 3237) := [(2620, -57393255745848253392000), (2621, -13859759488652579980800), (2622, -177172925839086081139200), (2627, -1770709794526310400), (2633, -174220701844730462611200), (2635, 105242954236554563251200), (2642, 92462645367016541971200), (2643, 50386340949098339203200), (2646, -2342029148024832000), (2647, -4684058296049664000), (2648, 184923265123889488627200), (2649, 68058168735506602060800), (2650, 184923265123889488627200), (2651, 68052835101503477836800), (2657, 39447905181225601939200), (2658, -160084578448642724150400), (2659, -304248557117783072592000), (2661, 184923265123889488627200), (2664, 352383081513954461107200), (2665, -125616041531842323168000), (2667, 17010965706723894124800), (2668, 85056745041554888044800), (2669, -279863339523823178726400), (2671, 273458193316880085964800), (2672, -1203725312842752000), (2673, -2941724368538726400), (2674, 174769225618612577702400), (2676, -271573481170360242316800), (2677, -364796816846682716899200), (2681, -58778378253753969888000), (2682, 79430406797208817324800), (2684, 3019072320372159475200), (2685, 225379300705666483622400), (2688, 85270892982208083763200), (2689, 113195125416265294752000), (2690, -18268240309469018870400), (2691, 206914750347961060876800), (2692, -40652869678337362118400), (2693, -194621096483637378307200), (2694, -828099932740113304051200), (2697, 378612961564339324569600), (2698, -9697831359747889680000), (2699, -654503054575931734723200), (2700, 69099338344398230736000), (2701, 69078253566901119811200), (2702, -828099932740113304051200), (2703, -654499578577820342774400), (2704, -199396414503086403456000), (2705, 206911654258469186880000), (2711, 424538635545796211193600), (2712, 3445501275549988300800), (2713, 200283406518063020140800), (2714, 32145524729348483174400), (2715, 137676798095863565548800), (2716, 79800832532041478726400), (2717, 954449960016813084115200), (2718, 392393110816447728019200), (2719, 304832033393445313056000), (2720, 279958420667509607923200), (2721, 56569637135815463116800), (2722, 751432887697849714022400), (2723, -69843528018618577171200), (2724, -86566016700546564384000), (2725, 259475512434540680275200)]

def merged1056part8 : Integer.Sparse (Fin 3237) := [(2726, 571579319238018858144000), (2727, -195938660118111515136000), (2728, -86566016700546564384000), (2729, 310484761206330852691200), (2732, 385216349985858952915200), (2733, 92462645367016541971200), (2734, 217692619467287465088000), (2735, 242046312441332612169600), (2736, -100642982725137901708800), (2737, 604642522833518267750400), (2738, 452352909897949215859200), (2739, 21020900471936061177600), (2740, -33325011195777636652800), (2741, 546628207367607985267200), (2742, 664352375692355120736000), (2743, 115007322891317800204800), (2746, 365077590754435599398400), (2747, -83489581894570133587200), (2748, 9749393572968455212800), (2749, 311124413031838020720000), (2750, -225729817608263884675200), (2751, 4028080011475968000), (2752, 38550929510638276099200), (2753, 295745965088030221766400), (2754, -6098261362502394456000), (2755, 91245721139957489414400), (2756, 249532873648128000), (2757, 252110568305078411846400), (2758, 50744211750607123123200), (2759, 206917330883912834572800), (2760, 34977735896633160220800), (2761, -373159287243223767216000), (2762, -145597277356790181753600), (2763, 525971280905607373804800), (2764, -483386729496221022595200), (2765, -151621770202970659401600), (2766, 128487504780678800937600), (2767, 77615868665919573964800), (2768, 147203114084672878915200), (2769, 84034113764049163612800), (2770, 184923265123889488627200), (2771, 184923265123889488627200), (2775, 341708287387140797558400), (2776, 184923265123889488627200), (2777, 24424112406466979942400), (2779, 66538527026066162726400), (2780, -78331603601924517801600), (2781, 244241352115058489990400), (2782, 33177410434187428550400), (2783, 425607459417156047875200), (2784, -101146030266543469804800), (2785, 10610701043078707200000), (2786, 331999401020328821404800), (2787, -90203372387442562752000), (2788, -372878643776414397148800), (2789, -29592270704609718739200), (2790, 5956465959269683200000), (2791, 1444380909058136818137600), (2792, 318735531238526772249600), (2793, 638771904740481336115200), (2794, 441508913556359213174400), (2796, -579418766745290141241600), (2797, 77615289332901008640000), (2798, -77130286829568000)]

def merged1056part9 : Integer.Sparse (Fin 3237) := [(2799, 66531501514368773568000), (2800, -1243951727864832000), (2801, 66539845284786553075200), (2802, 437861008320730357305600), (2803, 71756525499083627328000), (2808, -241384039206912000), (2810, -30173004900864000), (2814, -362076058810368000), (2817, 34023992065345044403200), (2818, 953157014003054952000), (2819, 16043118521301692452800), (2820, -10607794966691866515600), (2827, 972866107843499520), (2828, -20613744374499279360), (2829, 34028963562889242904320), (2830, -17907683321220456960), (2831, 82319782944854009157120), (2832, -31204941589938813903360), (2833, -26456828647069639526400), (2835, 972866107843499520), (2836, -20613744374499279360), (2837, -5883085674507444480), (2838, -29484233759147892480), (2839, -1622329986100173483893760), (2840, 1408457115886264717271040), (2848, 1104915157326102528000), (2851, 1104915157326102528000), (2855, 368305052442034176000), (2864, 368305052442034176000), (2868, 2209830314652205056000), (2889, 1104915157326102528000), (2964, -887003722579968000), (3031, 1119070548052221226291200), (3039, 373023516017407075430400), (3047, 673110671428925598758400), (3054, 224370223809641866252800), (3063, 597393739827048941683200), (3106, 997559827955712000), (3107, 997559827955712000), (3108, 997559827955712000), (3112, 58386378042687356928000), (3117, 997559827955712000), (3118, 19462126014229118976000), (3122, 30885462089535062016000), (3123, 109601221162605871104000), (3124, 997559827955712000), (3125, -88813953417963922444800), (3126, -173104198181731197964800), (3128, 256439456864250127372800), (3129, 357770439045038262297600), (3131, 196313205376163931148800), (3132, 154147734685259293708800), (3133, 177723697791179318284800), (3134, 109500120130274721792000), (3135, 23852887615596920832000), (3136, 74684845041027121152000), (3137, 205346648022176785420800), (3141, -21272672350789042176000), (3142, -72610116405090582528000), (3143, -19707640034800435200000), (3144, 4619499609448120320000), (3145, 18589507584984612864000), (3146, 138142326022824813580800), (3147, 123760969503455601676800)]

def merged1056part10 : Integer.Sparse (Fin 3237) := [(3148, 382352573330695178265600), (3149, 89724577322795840006400), (3151, -19354248081808883712000), (3155, 153396558146930762764800), (3156, 153396558146930762764800), (3159, 306793116293861525529600), (3162, 177723697791179318284800), (3163, 177723697791179318284800), (3164, 139015201627561550860800), (3165, -9677124040904441856000), (3167, 154147734685259293708800), (3168, 154147734685259293708800), (3169, 160888685954279695372800), (3170, 1268229744765456830784000), (3174, 345631257083984267289600), (3175, 23852887615596920832000), (3177, 205346648022176785420800), (3178, 205346648022176785420800), (3179, -138489024795313398796800), (3180, -476986740462742638643200), (3181, 32242449840445587456000), (3183, 23852887615596920832000), (3184, -247788124023863625753600), (3186, 392485642031636194406400), (3189, 82268546789455036416000), (3190, -229198616438879012889600), (3194, 47706772791021797376000), (3197, 367816113689250154521600), (3198, 179449154645591680012800), (3205, 997559827955712000), (3206, 997559827955712000), (3209, 1177456926094908583219200), (3212, 997559827955712000), (3213, 39357879536535404544000), (3214, 30885462089535062016000), (3215, 46376320210995511296000), (3216, 136739043796923187200000), (3217, 85646234954849845248000), (3218, 32242449840445587456000), (3222, -5865234347243077632000), (3223, 30886459649363017728000), (3224, -8410595016858402816000), (3225, -88348151629752827904000), (3226, 1799285430923152764480000), (3227, -119700413067326940172800), (3228, 645020254745822899238400), (3229, 1858857884393367241843200), (3230, 194711915507518956556800), (3231, -670627032337520129088000), (3232, 85222139827450649587200), (3233, 23853885175424876544000), (3234, 42442395200581533696000), (3235, -33771975614967840768000), (3236, 400369606789116250137600)]

def merged1056 : Integer.Sparse (Fin 3237) := (((merged1056part0 ++ merged1056part1) ++ (merged1056part2 ++ (merged1056part3 ++ merged1056part4))) ++ ((merged1056part5 ++ (merged1056part6 ++ merged1056part7)) ++ (merged1056part8 ++ (merged1056part9 ++ merged1056part10))))

def merged1057 : Integer.Sparse (Fin 3237) := [(722, -128159422325701046784000), (887, -128159422325701046784000), (891, -128159422325701046784000), (895, -128159422325701046784000), (927, -128159422325701046784000), (1155, 4455431321137016623200), (1327, 4455431321137016623200), (1758, -128159422325701046784000), (2289, 4455431321137016623200), (2293, 4455431321137016623200), (2310, 8910862642274033246400), (2818, -4455431321137016623200), (2839, 128159422325701046784000)]

def merged1058 : Integer.Sparse (Fin 3237) := [(487, 80260553754098458675200), (514, -71703185183039637914400), (1062, -71703185183039637914400), (1087, 80260553754098458675200), (1155, 8557368571058820760800), (1157, 160521107508196917350400), (1170, -71703185183039637914400), (1176, -143406370366079275828800), (2818, -8557368571058820760800)]

def merged1059 : Integer.Sparse (Fin 3237) := [(487, 80260553754098458675200), (514, -71703185183039637914400), (722, -128159422325701046784000), (887, -128159422325701046784000), (891, -128159422325701046784000), (895, -128159422325701046784000), (927, -128159422325701046784000), (1062, -71703185183039637914400), (1087, 80260553754098458675200), (1155, 13012799892195837384000), (1157, 160521107508196917350400), (1170, -71703185183039637914400), (1176, -143406370366079275828800), (1327, 4455431321137016623200), (1758, -128159422325701046784000), (2289, 4455431321137016623200), (2293, 4455431321137016623200), (2310, 8910862642274033246400), (2818, -13012799892195837384000), (2839, 128159422325701046784000)]

def merged1060 : Integer.Sparse (Fin 3237) := [(319, -63671503808991285043200), (552, -63671503808991285043200), (554, -44563645709533504512000), (589, -63671503808991285043200), (638, -127343007617982570086400), (657, -63671503808991285043200), (886, -44563645709533504512000), (890, -44563645709533504512000), (894, -44563645709533504512000), (925, -44563645709533504512000), (1394, -44563645709533504512000), (2831, 108235149518524789555200)]

def merged1061 : Integer.Sparse (Fin 3237) := [(736, 67159889013511700582400), (746, 33579944506755850291200), (749, 33579944506755850291200), (829, 33579944506755850291200), (900, -9662719411699200), (1297, -9662719411699200), (1306, -9662719411699200), (1316, -9662719411699200), (1555, -9662719411699200), (1786, 33579944506755850291200), (2134, -9662719411699200), (2828, 9662719411699200), (2840, -33579944506755850291200)]

def merged1062 : Integer.Sparse (Fin 3237) := [(616, -9772680138298560000), (736, 67159889013511700582400), (746, 33579944506755850291200), (749, 33579944506755850291200), (829, 33579944506755850291200), (900, -9662719411699200), (1170, -9772680138298560000), (1297, -9662719411699200), (1306, -9662719411699200), (1316, -9662719411699200), (1327, -9772680138298560000), (1366, -9772680138298560000), (1555, -9662719411699200), (1579, -19545360276597120000), (1786, 33579944506755850291200), (2134, -9662719411699200), (2818, 9772680138298560000), (2828, 9662719411699200), (2840, -33579944506755850291200)]

def merged1063 : Integer.Sparse (Fin 3237) := [(319, -63671503808991285043200), (552, -63671503808991285043200), (554, -44563645709533504512000), (589, -63671503808991285043200), (616, -9772680138298560000), (638, -127343007617982570086400), (657, -63671503808991285043200), (736, 67159889013511700582400), (746, 33579944506755850291200), (749, 33579944506755850291200), (829, 33579944506755850291200), (886, -44563645709533504512000), (890, -44563645709533504512000), (894, -44563645709533504512000), (900, -9662719411699200), (925, -44563645709533504512000), (1170, -9772680138298560000), (1297, -9662719411699200), (1306, -9662719411699200), (1316, -9662719411699200), (1327, -9772680138298560000), (1366, -9772680138298560000), (1394, -44563645709533504512000), (1555, -9662719411699200), (1579, -19545360276597120000), (1786, 33579944506755850291200), (2134, -9662719411699200), (2818, 9772680138298560000), (2828, 9662719411699200), (2831, 108235149518524789555200), (2840, -33579944506755850291200)]

def merged1064 : Integer.Sparse (Fin 3237) := [(319, -63671503808991285043200), (487, 80260553754098458675200), (514, -71703185183039637914400), (552, -63671503808991285043200), (554, -44563645709533504512000), (589, -63671503808991285043200), (616, -9772680138298560000), (638, -127343007617982570086400), (657, -63671503808991285043200), (722, -128159422325701046784000), (736, 67159889013511700582400), (746, 33579944506755850291200), (749, 33579944506755850291200), (829, 33579944506755850291200), (886, -44563645709533504512000), (887, -128159422325701046784000), (890, -44563645709533504512000), (891, -128159422325701046784000), (894, -44563645709533504512000), (895, -128159422325701046784000), (900, -9662719411699200), (925, -44563645709533504512000), (927, -128159422325701046784000), (1062, -71703185183039637914400), (1087, 80260553754098458675200), (1155, 13012799892195837384000), (1157, 160521107508196917350400), (1170, -71712957863177936474400), (1176, -143406370366079275828800), (1297, -9662719411699200), (1306, -9662719411699200), (1316, -9662719411699200), (1327, 4445658640998718063200), (1366, -9772680138298560000), (1394, -44563645709533504512000), (1555, -9662719411699200), (1579, -19545360276597120000), (1758, -128159422325701046784000), (1786, 33579944506755850291200), (2134, -9662719411699200), (2289, 4455431321137016623200), (2293, 4455431321137016623200), (2310, 8910862642274033246400), (2818, -13003027212057538824000), (2828, 9662719411699200), (2831, 108235149518524789555200), (2839, 128159422325701046784000), (2840, -33579944506755850291200)]

def merged1065 : Integer.Sparse (Fin 3237) := [(370, -110249053050412765440000), (375, 144185043974014239436800), (749, -110249053050412765440000), (759, -220498106100825530880000), (763, 288370087948028478873600), (828, 144185043974014239436800), (829, -110249053050412765440000), (832, -110249053050412765440000), (847, 144185043974014239436800), (866, 144185043974014239436800), (2840, -33935990923601473996800)]

def merged1066 : Integer.Sparse (Fin 3237) := [(1067, 38957798484739620662400), (1073, 19478899242369810331200), (1075, 19478899242369810331200), (1179, 64726229853641210954400), (1630, 45247330611271400623200), (2312, 155220891076184012200800), (2320, 45247330611271400623200), (2818, -64726229853641210954400)]

def merged1067 : Integer.Sparse (Fin 3237) := [(1067, 38957798484739620662400), (1073, 19478899242369810331200), (1075, 19478899242369810331200), (1087, -67904413173121519411200), (1091, -33952206586560759705600), (1096, -33952206586560759705600), (1157, -33952206586560759705600), (1179, 64726229853641210954400), (1630, 45247330611271400623200), (2312, 121268684489623252495200), (2320, 45247330611271400623200), (2818, -30774023267080451248800)]

def merged1068 : Integer.Sparse (Fin 3237) := [(370, -110249053050412765440000), (375, 144185043974014239436800), (749, -110249053050412765440000), (759, -220498106100825530880000), (763, 288370087948028478873600), (828, 144185043974014239436800), (829, -110249053050412765440000), (832, -110249053050412765440000), (847, 144185043974014239436800), (866, 144185043974014239436800), (1067, 38957798484739620662400), (1073, 19478899242369810331200), (1075, 19478899242369810331200), (1087, -67904413173121519411200), (1091, -33952206586560759705600), (1096, -33952206586560759705600), (1157, -33952206586560759705600), (1179, 64726229853641210954400), (1630, 45247330611271400623200), (2312, 121268684489623252495200), (2320, 45247330611271400623200), (2818, -30774023267080451248800), (2840, -33935990923601473996800)]

def merged1069 : Integer.Sparse (Fin 3237) := [(1075, 17011638558178823059200), (1157, -111226958457519482222400), (2257, 17011638558178823059200), (2293, 34023277116357646118400), (2301, -222453916915038964444800), (2310, -94215319899340659163200), (2312, -94215319899340659163200), (2320, -111226958457519482222400), (2818, 94215319899340659163200)]

def merged1070 : Integer.Sparse (Fin 3237) := [(360, 75044812250892131020800), (715, 206657067412215995904000), (719, 206657067412215995904000), (723, 206657067412215995904000), (735, 281701879663108126924800), (752, 75044812250892131020800), (804, 281701879663108126924800), (822, 75044812250892131020800), (828, 75044812250892131020800), (1755, 206657067412215995904000), (2840, -281701879663108126924800)]

def merged1071 : Integer.Sparse (Fin 3237) := [(360, 75044812250892131020800), (715, 206657067412215995904000), (719, 206657067412215995904000), (723, 206657067412215995904000), (735, 281701879663108126924800), (752, 75044812250892131020800), (804, 281701879663108126924800), (822, 75044812250892131020800), (828, 75044812250892131020800), (841, 97201279899533695536000), (1480, 194402559799067391072000), (1490, 97201279899533695536000), (1571, 97201279899533695536000), (1755, 206657067412215995904000), (1965, 97201279899533695536000), (2830, -97201279899533695536000), (2840, -281701879663108126924800)]

def merged1072 : Integer.Sparse (Fin 3237) := [(360, 75044812250892131020800), (715, 206657067412215995904000), (719, 206657067412215995904000), (723, 206657067412215995904000), (735, 281701879663108126924800), (752, 75044812250892131020800), (804, 281701879663108126924800), (822, 75044812250892131020800), (828, 75044812250892131020800), (841, 97201279899533695536000), (1075, 17011638558178823059200), (1157, -111226958457519482222400), (1480, 194402559799067391072000), (1490, 97201279899533695536000), (1571, 97201279899533695536000), (1755, 206657067412215995904000), (1965, 97201279899533695536000), (2257, 17011638558178823059200), (2293, 34023277116357646118400), (2301, -222453916915038964444800), (2310, -94215319899340659163200), (2312, -94215319899340659163200), (2320, -111226958457519482222400), (2818, 94215319899340659163200), (2830, -97201279899533695536000), (2840, -281701879663108126924800)]

def merged1073 : Integer.Sparse (Fin 3237) := [(360, 75044812250892131020800), (370, -110249053050412765440000), (375, 144185043974014239436800), (715, 206657067412215995904000), (719, 206657067412215995904000), (723, 206657067412215995904000), (735, 281701879663108126924800), (749, -110249053050412765440000), (752, 75044812250892131020800), (759, -220498106100825530880000), (763, 288370087948028478873600), (804, 281701879663108126924800), (822, 75044812250892131020800), (828, 219229856224906370457600), (829, -110249053050412765440000), (832, -110249053050412765440000), (841, 97201279899533695536000), (847, 144185043974014239436800), (866, 144185043974014239436800), (1067, 38957798484739620662400), (1073, 19478899242369810331200), (1075, 36490537800548633390400), (1087, -67904413173121519411200), (1091, -33952206586560759705600), (1096, -33952206586560759705600), (1157, -145179165044080241928000), (1179, 64726229853641210954400), (1480, 194402559799067391072000), (1490, 97201279899533695536000), (1571, 97201279899533695536000), (1630, 45247330611271400623200), (1755, 206657067412215995904000), (1965, 97201279899533695536000), (2257, 17011638558178823059200), (2293, 34023277116357646118400), (2301, -222453916915038964444800), (2310, -94215319899340659163200), (2312, 27053364590282593332000), (2320, -65979627846248081599200), (2818, 63441296632260207914400), (2830, -97201279899533695536000), (2840, -315637870586709600921600)]

def merged1074 : Integer.Sparse (Fin 3237) := [(319, -63671503808991285043200), (360, 75044812250892131020800), (370, -110249053050412765440000), (375, 144185043974014239436800), (487, 80260553754098458675200), (514, -71703185183039637914400), (552, -63671503808991285043200), (554, -44563645709533504512000), (589, -63671503808991285043200), (616, -9772680138298560000), (638, -127343007617982570086400), (657, -63671503808991285043200), (715, 206657067412215995904000), (719, 206657067412215995904000), (722, -128159422325701046784000), (723, 206657067412215995904000), (735, 281701879663108126924800), (736, 67159889013511700582400), (746, 33579944506755850291200), (749, -76669108543656915148800), (752, 75044812250892131020800), (759, -220498106100825530880000), (763, 288370087948028478873600), (804, 281701879663108126924800), (822, 75044812250892131020800), (828, 219229856224906370457600), (829, -76669108543656915148800), (832, -110249053050412765440000), (841, 97201279899533695536000), (847, 144185043974014239436800), (866, 144185043974014239436800), (886, -44563645709533504512000), (887, -128159422325701046784000), (890, -44563645709533504512000), (891, -128159422325701046784000), (894, -44563645709533504512000), (895, -128159422325701046784000), (900, -9662719411699200), (925, -44563645709533504512000), (927, -128159422325701046784000), (1062, -71703185183039637914400), (1067, 38957798484739620662400), (1073, 19478899242369810331200), (1075, 36490537800548633390400), (1087, 12356140580976939264000), (1091, -33952206586560759705600), (1096, -33952206586560759705600), (1155, 13012799892195837384000), (1157, 15341942464116675422400), (1170, -71712957863177936474400), (1176, -143406370366079275828800), (1179, 64726229853641210954400), (1297, -9662719411699200), (1306, -9662719411699200), (1316, -9662719411699200), (1327, 4445658640998718063200), (1366, -9772680138298560000), (1394, -44563645709533504512000), (1480, 194402559799067391072000), (1490, 97201279899533695536000), (1555, -9662719411699200), (1571, 97201279899533695536000), (1579, -19545360276597120000), (1630, 45247330611271400623200), (1755, 206657067412215995904000), (1758, -128159422325701046784000), (1786, 33579944506755850291200), (1965, 97201279899533695536000), (2134, -9662719411699200), (2257, 17011638558178823059200), (2289, 4455431321137016623200), (2293, 38478708437494662741600), (2301, -222453916915038964444800), (2310, -85304457257066625916800), (2312, 27053364590282593332000), (2320, -65979627846248081599200), (2818, 50438269420202669090400), (2828, 9662719411699200), (2830, -97201279899533695536000), (2831, 108235149518524789555200), (2839, 128159422325701046784000), (2840, -349217815093465451212800)]

def merged1075 : Integer.Sparse (Fin 3237) := [(364, -27699221334183475507200), (716, 53676069873930743500800), (722, 53676069873930743500800), (724, 53676069873930743500800), (740, 25976848539747267993600), (754, -27699221334183475507200), (806, -1722372794436207513600), (826, -27699221334183475507200), (1758, 53676069873930743500800), (2839, -25976848539747267993600)]

def merged1076 : Integer.Sparse (Fin 3237) := [(1048, -68048932687870108262400), (1053, -68048932687870108262400), (1062, 107005693411203528412800), (1065, 38956760723333420150400), (1067, 107005693411203528412800), (1070, 107005693411203528412800), (1157, -68048932687870108262400), (1176, 107005693411203528412800), (2301, 38956760723333420150400), (2818, -38956760723333420150400)]

def merged1077 : Integer.Sparse (Fin 3237) := [(364, -27699221334183475507200), (716, 53676069873930743500800), (722, 53676069873930743500800), (724, 53676069873930743500800), (740, 25976848539747267993600), (754, -27699221334183475507200), (806, -1722372794436207513600), (826, -27699221334183475507200), (1048, -68048932687870108262400), (1053, -68048932687870108262400), (1062, 107005693411203528412800), (1065, 38956760723333420150400), (1067, 107005693411203528412800), (1070, 107005693411203528412800), (1157, -68048932687870108262400), (1176, 107005693411203528412800), (1758, 53676069873930743500800), (2301, 38956760723333420150400), (2818, -38956760723333420150400), (2839, -25976848539747267993600)]

def merged1078 : Integer.Sparse (Fin 3237) := [(1065, 34042129027415221708800), (1176, 65227658909684858546400), (1579, 65227658909684858546400), (2252, 34042129027415221708800), (2289, 34042129027415221708800), (2301, 198539575874200160510400), (2310, 99269787937100080255200), (2320, 65227658909684858546400), (2818, -99269787937100080255200)]

def merged1079 : Integer.Sparse (Fin 3237) := [(771, -15789974939756236800), (800, 573954180458419046361600), (1431, 573954180458419046361600), (1440, 573954180458419046361600), (1448, 573954180458419046361600), (1551, 573954180458419046361600), (1683, -15789974939756236800), (1729, -15789974939756236800), (1764, -15789974939756236800), (1890, -15789974939756236800), (1896, -15789974939756236800), (1931, 573954180458419046361600), (2828, -573954180458419046361600), (2836, 15789974939756236800)]

def merged1080 : Integer.Sparse (Fin 3237) := [(771, -15789974939756236800), (800, 573954180458419046361600), (1048, 7932884794748928000), (1366, 7932884794748928000), (1375, 7932884794748928000), (1414, 7932884794748928000), (1431, 573954180458419046361600), (1440, 573954180458419046361600), (1448, 573954180458419046361600), (1551, 573954180458419046361600), (1579, 7932884794748928000), (1683, -15789974939756236800), (1729, -15789974939756236800), (1764, -15789974939756236800), (1890, -15789974939756236800), (1896, -15789974939756236800), (1931, 573954180458419046361600), (2301, 7932884794748928000), (2818, -7932884794748928000), (2828, -573954180458419046361600), (2836, 15789974939756236800)]

def merged1081 : Integer.Sparse (Fin 3237) := [(771, -15789974939756236800), (800, 573954180458419046361600), (1048, 7932884794748928000), (1065, 34042129027415221708800), (1176, 65227658909684858546400), (1366, 7932884794748928000), (1375, 7932884794748928000), (1414, 7932884794748928000), (1431, 573954180458419046361600), (1440, 573954180458419046361600), (1448, 573954180458419046361600), (1551, 573954180458419046361600), (1579, 65235591794479607474400), (1683, -15789974939756236800), (1729, -15789974939756236800), (1764, -15789974939756236800), (1890, -15789974939756236800), (1896, -15789974939756236800), (1931, 573954180458419046361600), (2252, 34042129027415221708800), (2289, 34042129027415221708800), (2301, 198547508758994909438400), (2310, 99269787937100080255200), (2320, 65227658909684858546400), (2818, -99277720821894829183200), (2828, -573954180458419046361600), (2836, 15789974939756236800)]

def merged1082 : Integer.Sparse (Fin 3237) := [(364, -27699221334183475507200), (716, 53676069873930743500800), (722, 53676069873930743500800), (724, 53676069873930743500800), (740, 25976848539747267993600), (754, -27699221334183475507200), (771, -15789974939756236800), (800, 573954180458419046361600), (806, -1722372794436207513600), (826, -27699221334183475507200), (1048, -68040999803075359334400), (1053, -68048932687870108262400), (1062, 107005693411203528412800), (1065, 72998889750748641859200), (1067, 107005693411203528412800), (1070, 107005693411203528412800), (1157, -68048932687870108262400), (1176, 172233352320888386959200), (1366, 7932884794748928000), (1375, 7932884794748928000), (1414, 7932884794748928000), (1431, 573954180458419046361600), (1440, 573954180458419046361600), (1448, 573954180458419046361600), (1551, 573954180458419046361600), (1579, 65235591794479607474400), (1683, -15789974939756236800), (1729, -15789974939756236800), (1758, 53676069873930743500800), (1764, -15789974939756236800), (1890, -15789974939756236800), (1896, -15789974939756236800), (1931, 573954180458419046361600), (2252, 34042129027415221708800), (2289, 34042129027415221708800), (2301, 237504269482328329588800), (2310, 99269787937100080255200), (2320, 65227658909684858546400), (2818, -138234481545228249333600), (2828, -573954180458419046361600), (2836, 15789974939756236800), (2839, -25976848539747267993600)]

def merged1083 : Integer.Sparse (Fin 3237) := [(768, 17921366125916198400), (769, 194550161505015117715200), (771, 17921366125916198400), (772, 17921366125916198400), (778, 17921366125916198400), (840, 17921366125916198400), (1362, 194550161505015117715200), (1373, 194550161505015117715200), (1401, 194550161505015117715200), (1571, 194550161505015117715200), (1894, 194550161505015117715200), (1896, 17921366125916198400), (2830, -194550161505015117715200), (2836, -17921366125916198400)]

def merged1084 : Integer.Sparse (Fin 3237) := [(784, 287047448064658030982400), (785, 6403435625374905600), (786, 6403435625374905600), (790, 6403435625374905600), (799, 12806871250749811200), (1359, 574094896129316061964800), (1377, 287047448064658030982400), (1551, 287047448064658030982400), (1913, 6403435625374905600), (2828, -287047448064658030982400), (2838, -6403435625374905600)]

def merged1085 : Integer.Sparse (Fin 3237) := [(784, 287047448064658030982400), (786, 6403435625374905600), (790, 6403435625374905600), (799, 12806871250749811200), (1359, 574094896129316061964800), (1377, 287047448064658030982400), (1551, 287047448064658030982400), (1727, -12806871250749811200), (1742, -6403435625374905600), (2828, -287047448064658030982400)]

def merged1086 : Integer.Sparse (Fin 3237) := [(768, 17921366125916198400), (769, 194550161505015117715200), (771, 17921366125916198400), (772, 17921366125916198400), (778, 17921366125916198400), (784, 287047448064658030982400), (786, 6403435625374905600), (790, 6403435625374905600), (799, 12806871250749811200), (840, 17921366125916198400), (1359, 574094896129316061964800), (1362, 194550161505015117715200), (1373, 194550161505015117715200), (1377, 287047448064658030982400), (1401, 194550161505015117715200), (1551, 287047448064658030982400), (1571, 194550161505015117715200), (1727, -12806871250749811200), (1742, -6403435625374905600), (1894, 194550161505015117715200), (1896, 17921366125916198400), (2828, -287047448064658030982400), (2830, -194550161505015117715200), (2836, -17921366125916198400)]

def merged1087 : Integer.Sparse (Fin 3237) := [(0, -1758349319976136339200), (3, -1850894021027511936000), (4, -462723505256877984000), (261, -9254470105137559680000), (345, 66632184756990429696000), (349, 22210728252330143232000), (354, 22210728252330143232000), (740, 133264369513980859392000), (744, 66632184756990429696000), (749, 66632184756990429696000), (1011, -1158021835020288000), (1013, -386007278340096000), (1015, -386007278340096000), (2283, -2316043670040576000), (2285, -1158021835020288000), (2287, -1158021835020288000), (2318, -1158021835020288000), (2320, -1158021835020288000), (2321, -386007278340096000), (2323, -386007278340096000), (2558, -1158021835020288000)]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def merged1088 : Integer.Sparse (Fin 3237) := [(0, 555093944764962624000), (3, 444080366892323481600), (4, 111020091723080870400), (261, -1110194403380366976000), (339, -23980105313569565798400), (343, -7993368437856521932800), (353, -7993368437856521932800), (574, -23980105313569565798400), (656, 468997231804416000), (659, 468997231804416000), (664, -7993368437856521932800), (697, 156332410601472000), (735, -47960210627139131596800), (748, -23980105313569565798400), (825, 468997231804416000), (828, -23979167319105956966400), (869, 156332410601472000), (1157, 468997231804416000), (1176, 468997231804416000), (1179, 156332410601472000), (1579, 468997231804416000), (1630, 156332410601472000), (2310, 937994463608832000), (2320, 156332410601472000), (2961, -3751977854435328000), (2969, -1875988927217664000)]

def merged1089 : Integer.Sparse (Fin 3237) := [(0, 555132174987991104000), (3, 444110951070746265600), (4, 111027737767686566400), (261, -1110270863826423936000), (339, -23981756859204396134400), (343, -7993918953068132044800), (353, -7993918953068132044800), (574, -23981756859204396134400), (656, 468997231804416000), (659, 468997231804416000), (664, -7993918953068132044800), (697, 156332410601472000), (735, -47963513718408792268800), (748, -23981756859204396134400), (825, 468997231804416000), (828, -23980818864740787302400), (869, 156332410601472000), (994, -1651545634830336000), (997, -550515211610112000), (1014, -550515211610112000), (1132, -1651545634830336000), (1157, 468997231804416000), (1176, 468997231804416000), (1178, -550515211610112000), (1179, 156332410601472000), (1579, 468997231804416000), (1630, 156332410601472000), (2274, -3303091269660672000), (2286, -1651545634830336000), (2310, -713551171221504000), (2319, -1651545634830336000), (2320, 156332410601472000), (2322, -550515211610112000), (2564, -1651545634830336000), (2580, -550515211610112000), (2961, -3751977854435328000), (2969, -1875988927217664000)]

def merged1090 : Integer.Sparse (Fin 3237) := [(0, -1203217144988145235200), (3, -1406783069956765670400), (4, -351695767489191417600), (261, -10364740968963983616000), (339, -23981756859204396134400), (343, -7993918953068132044800), (345, 66632184756990429696000), (349, 22210728252330143232000), (353, -7993918953068132044800), (354, 22210728252330143232000), (574, -23981756859204396134400), (656, 468997231804416000), (659, 468997231804416000), (664, -7993918953068132044800), (697, 156332410601472000), (735, -47963513718408792268800), (740, 133264369513980859392000), (744, 66632184756990429696000), (748, -23981756859204396134400), (749, 66632184756990429696000), (825, 468997231804416000), (828, -23980818864740787302400), (869, 156332410601472000), (994, -1651545634830336000), (997, -550515211610112000), (1011, -1158021835020288000), (1013, -386007278340096000), (1014, -550515211610112000), (1015, -386007278340096000), (1132, -1651545634830336000), (1157, 468997231804416000), (1176, 468997231804416000), (1178, -550515211610112000), (1179, 156332410601472000), (1579, 468997231804416000), (1630, 156332410601472000), (2274, -3303091269660672000), (2283, -2316043670040576000), (2285, -1158021835020288000), (2286, -1651545634830336000), (2287, -1158021835020288000), (2310, -713551171221504000), (2318, -1158021835020288000), (2319, -1651545634830336000), (2320, -1001689424418816000), (2321, -386007278340096000), (2322, -550515211610112000), (2323, -386007278340096000), (2558, -1158021835020288000), (2564, -1651545634830336000), (2580, -550515211610112000), (2961, -3751977854435328000), (2969, -1875988927217664000)]

def merged1091 : Integer.Sparse (Fin 3237) := [(0, -1203217144988145235200), (3, -1406783069956765670400), (4, -351695767489191417600), (261, -10364740968963983616000), (339, -23981756859204396134400), (343, -7993918953068132044800), (345, 66632184756990429696000), (349, 22210728252330143232000), (353, -7993918953068132044800), (354, 22210728252330143232000), (574, -23981756859204396134400), (656, 468997231804416000), (659, 468997231804416000), (664, -7993918953068132044800), (697, 156332410601472000), (735, -47963513718408792268800), (740, 133264369513980859392000), (744, 66632184756990429696000), (748, -23981756859204396134400), (749, 66632184756990429696000), (768, 17921366125916198400), (769, 194550161505015117715200), (771, 17921366125916198400), (772, 17921366125916198400), (778, 17921366125916198400), (784, 287047448064658030982400), (786, 6403435625374905600), (790, 6403435625374905600), (799, 12806871250749811200), (825, 468997231804416000), (828, -23980818864740787302400), (840, 17921366125916198400), (869, 156332410601472000), (994, -1651545634830336000), (997, -550515211610112000), (1011, -1158021835020288000), (1013, -386007278340096000), (1014, -550515211610112000), (1015, -386007278340096000), (1132, -1651545634830336000), (1157, 468997231804416000), (1176, 468997231804416000), (1178, -550515211610112000), (1179, 156332410601472000), (1359, 574094896129316061964800), (1362, 194550161505015117715200), (1373, 194550161505015117715200), (1377, 287047448064658030982400), (1401, 194550161505015117715200), (1551, 287047448064658030982400), (1571, 194550161505015117715200), (1579, 468997231804416000), (1630, 156332410601472000), (1727, -12806871250749811200), (1742, -6403435625374905600), (1894, 194550161505015117715200), (1896, 17921366125916198400), (2274, -3303091269660672000), (2283, -2316043670040576000), (2285, -1158021835020288000), (2286, -1651545634830336000), (2287, -1158021835020288000), (2310, -713551171221504000), (2318, -1158021835020288000), (2319, -1651545634830336000), (2320, -1001689424418816000), (2321, -386007278340096000), (2322, -550515211610112000), (2323, -386007278340096000), (2558, -1158021835020288000), (2564, -1651545634830336000), (2580, -550515211610112000), (2828, -287047448064658030982400), (2830, -194550161505015117715200), (2836, -17921366125916198400), (2961, -3751977854435328000), (2969, -1875988927217664000)]

def merged1092 : Integer.Sparse (Fin 3237) := [(0, -1203217144988145235200), (3, -1406783069956765670400), (4, -351695767489191417600), (261, -10364740968963983616000), (339, -23981756859204396134400), (343, -7993918953068132044800), (345, 66632184756990429696000), (349, 22210728252330143232000), (353, -7993918953068132044800), (354, 22210728252330143232000), (364, -27699221334183475507200), (574, -23981756859204396134400), (656, 468997231804416000), (659, 468997231804416000), (664, -7993918953068132044800), (697, 156332410601472000), (716, 53676069873930743500800), (722, 53676069873930743500800), (724, 53676069873930743500800), (735, -47963513718408792268800), (740, 159241218053728127385600), (744, 66632184756990429696000), (748, -23981756859204396134400), (749, 66632184756990429696000), (754, -27699221334183475507200), (768, 17921366125916198400), (769, 194550161505015117715200), (771, 2131391186159961600), (772, 17921366125916198400), (778, 17921366125916198400), (784, 287047448064658030982400), (786, 6403435625374905600), (790, 6403435625374905600), (799, 12806871250749811200), (800, 573954180458419046361600), (806, -1722372794436207513600), (825, 468997231804416000), (826, -27699221334183475507200), (828, -23980818864740787302400), (840, 17921366125916198400), (869, 156332410601472000), (994, -1651545634830336000), (997, -550515211610112000), (1011, -1158021835020288000), (1013, -386007278340096000), (1014, -550515211610112000), (1015, -386007278340096000), (1048, -68040999803075359334400), (1053, -68048932687870108262400), (1062, 107005693411203528412800), (1065, 72998889750748641859200), (1067, 107005693411203528412800), (1070, 107005693411203528412800), (1132, -1651545634830336000), (1157, -68048463690638303846400), (1176, 172233821318120191375200), (1178, -550515211610112000), (1179, 156332410601472000), (1359, 574094896129316061964800), (1362, 194550161505015117715200), (1366, 7932884794748928000), (1373, 194550161505015117715200), (1375, 7932884794748928000), (1377, 287047448064658030982400), (1401, 194550161505015117715200), (1414, 7932884794748928000), (1431, 573954180458419046361600), (1440, 573954180458419046361600), (1448, 573954180458419046361600), (1551, 861001628523077077344000), (1571, 194550161505015117715200), (1579, 65236060791711411890400), (1630, 156332410601472000), (1683, -15789974939756236800), (1727, -12806871250749811200), (1729, -15789974939756236800), (1742, -6403435625374905600), (1758, 53676069873930743500800), (1764, -15789974939756236800), (1890, -15789974939756236800), (1894, 194550161505015117715200), (1896, 2131391186159961600), (1931, 573954180458419046361600), (2252, 34042129027415221708800), (2274, -3303091269660672000), (2283, -2316043670040576000), (2285, -1158021835020288000), (2286, -1651545634830336000), (2287, -1158021835020288000), (2289, 34042129027415221708800), (2301, 237504269482328329588800), (2310, 99269074385928858751200), (2318, -1158021835020288000), (2319, -1651545634830336000), (2320, 65226657220260439730400), (2321, -386007278340096000), (2322, -550515211610112000), (2323, -386007278340096000), (2558, -1158021835020288000), (2564, -1651545634830336000), (2580, -550515211610112000), (2818, -138234481545228249333600), (2828, -861001628523077077344000), (2830, -194550161505015117715200), (2836, -2131391186159961600), (2839, -25976848539747267993600), (2961, -3751977854435328000), (2969, -1875988927217664000)]

def merged1093 : Integer.Sparse (Fin 3237) := [(0, -1203217144988145235200), (3, -1406783069956765670400), (4, -351695767489191417600), (261, -10364740968963983616000), (319, -63671503808991285043200), (339, -23981756859204396134400), (343, -7993918953068132044800), (345, 66632184756990429696000), (349, 22210728252330143232000), (353, -7993918953068132044800), (354, 22210728252330143232000), (360, 75044812250892131020800), (364, -27699221334183475507200), (370, -110249053050412765440000), (375, 144185043974014239436800), (487, 80260553754098458675200), (514, -71703185183039637914400), (552, -63671503808991285043200), (554, -44563645709533504512000), (574, -23981756859204396134400), (589, -63671503808991285043200), (616, -9772680138298560000), (638, -127343007617982570086400), (656, 468997231804416000), (657, -63671503808991285043200), (659, 468997231804416000), (664, -7993918953068132044800), (697, 156332410601472000), (715, 206657067412215995904000), (716, 53676069873930743500800), (719, 206657067412215995904000), (722, -74483352451770303283200), (723, 206657067412215995904000), (724, 53676069873930743500800), (735, 233738365944699334656000), (736, 67159889013511700582400), (740, 159241218053728127385600), (744, 66632184756990429696000), (746, 33579944506755850291200), (748, -23981756859204396134400), (749, -10036923786666485452800), (752, 75044812250892131020800), (754, -27699221334183475507200), (759, -220498106100825530880000), (763, 288370087948028478873600), (768, 17921366125916198400), (769, 194550161505015117715200), (771, 2131391186159961600), (772, 17921366125916198400), (778, 17921366125916198400), (784, 287047448064658030982400), (786, 6403435625374905600), (790, 6403435625374905600), (799, 12806871250749811200), (800, 573954180458419046361600), (804, 281701879663108126924800), (806, -1722372794436207513600), (822, 75044812250892131020800), (825, 468997231804416000), (826, -27699221334183475507200), (828, 195249037360165583155200), (829, -76669108543656915148800), (832, -110249053050412765440000), (840, 17921366125916198400), (841, 97201279899533695536000), (847, 144185043974014239436800), (866, 144185043974014239436800), (869, 156332410601472000), (886, -44563645709533504512000), (887, -128159422325701046784000), (890, -44563645709533504512000), (891, -128159422325701046784000), (894, -44563645709533504512000), (895, -128159422325701046784000), (900, -9662719411699200), (925, -44563645709533504512000), (927, -128159422325701046784000), (994, -1651545634830336000), (997, -550515211610112000), (1011, -1158021835020288000), (1013, -386007278340096000), (1014, -550515211610112000), (1015, -386007278340096000), (1048, -68040999803075359334400), (1053, -68048932687870108262400), (1062, 35302508228163890498400), (1065, 72998889750748641859200), (1067, 145963491895943149075200), (1070, 107005693411203528412800), (1073, 19478899242369810331200), (1075, 36490537800548633390400), (1087, 12356140580976939264000), (1091, -33952206586560759705600), (1096, -33952206586560759705600), (1132, -1651545634830336000), (1155, 13012799892195837384000), (1157, -52706521226521628424000), (1170, -71712957863177936474400), (1176, 28827450952040915546400), (1178, -550515211610112000), (1179, 64726386186051812426400), (1297, -9662719411699200), (1306, -9662719411699200), (1316, -9662719411699200), (1327, 4445658640998718063200), (1359, 574094896129316061964800), (1362, 194550161505015117715200), (1366, -1839795343549632000), (1373, 194550161505015117715200), (1375, 7932884794748928000), (1377, 287047448064658030982400), (1394, -44563645709533504512000), (1401, 194550161505015117715200), (1414, 7932884794748928000), (1431, 573954180458419046361600), (1440, 573954180458419046361600), (1448, 573954180458419046361600), (1480, 194402559799067391072000), (1490, 97201279899533695536000), (1551, 861001628523077077344000), (1555, -9662719411699200), (1571, 291751441404548813251200), (1579, 65216515431434814770400), (1630, 45247486943682002095200), (1683, -15789974939756236800), (1727, -12806871250749811200), (1729, -15789974939756236800), (1742, -6403435625374905600), (1755, 206657067412215995904000), (1758, -74483352451770303283200), (1764, -15789974939756236800), (1786, 33579944506755850291200), (1890, -15789974939756236800), (1894, 194550161505015117715200), (1896, 2131391186159961600), (1931, 573954180458419046361600), (1965, 97201279899533695536000), (2134, -9662719411699200), (2252, 34042129027415221708800), (2257, 17011638558178823059200), (2274, -3303091269660672000), (2283, -2316043670040576000), (2285, -1158021835020288000), (2286, -1651545634830336000), (2287, -1158021835020288000), (2289, 38497560348552238332000), (2293, 38478708437494662741600), (2301, 15050352567289365144000), (2310, 13964617128862232834400), (2312, 27053364590282593332000), (2318, -1158021835020288000), (2319, -1651545634830336000), (2320, -752970625987641868800), (2321, -386007278340096000), (2322, -550515211610112000), (2323, -386007278340096000), (2558, -1158021835020288000), (2564, -1651545634830336000), (2580, -550515211610112000), (2818, -87796212125025580243200), (2828, -861001618860357665644800), (2830, -291751441404548813251200), (2831, 108235149518524789555200), (2836, -2131391186159961600), (2839, 102182573785953778790400), (2840, -349217815093465451212800), (2961, -3751977854435328000), (2969, -1875988927217664000)]

def merged1094 : Integer.Sparse (Fin 3237) := [(0, -1278615208038582919680), (3, -1345910745303771494400), (4, 1682388431629714368000), (32, 2018866117955657241600), (261, 1345910745303771494400), (659, 48452786830935773798400), (697, 16150928943645257932800), (806, 96905573661871547596800), (828, 48452786830935773798400), (829, 48452786830935773798400), (1176, -79426946452294308168000), (1179, -26475648817431436056000), (2320, -26475648817431436056000), (2818, 26475648817431436056000)]

def merged1095 : Integer.Sparse (Fin 3237) := [(1157, -90642338923884066345600), (2310, 70537308464072024366400), (2320, 16810759334753327462400), (2818, 6701676819937347326400)]

def merged1096 : Integer.Sparse (Fin 3237) := [(0, -1278615208038582919680), (3, -1345910745303771494400), (4, 1682388431629714368000), (32, 2018866117955657241600), (261, 1345910745303771494400), (659, 48452786830935773798400), (697, 16150928943645257932800), (806, 96905573661871547596800), (828, 48452786830935773798400), (829, 48452786830935773798400), (1157, -90642338923884066345600), (1176, -79426946452294308168000), (1179, -26475648817431436056000), (2310, 70537308464072024366400), (2320, -9664889482678108593600), (2818, 33177325637368783382400)]

def merged1097 : Integer.Sparse (Fin 3237) := [(0, -34578088152501196800), (4, -8644522038125299200), (32, 34578088152501196800), (68, 138312352610004787200), (261, 77800698343127692800), (346, 1867216760235064627200), (351, 622405586745021542400), (355, 622405586745021542400), (664, 185804558775779328000), (741, 3734433520470129254400), (746, 1867216760235064627200), (750, 1867216760235064627200), (825, 557413676327337984000), (871, 1867216760235064627200), (873, 622405586745021542400), (1178, 185804558775779328000), (1470, 557413676327337984000), (1579, 557413676327337984000), (1609, 557413676327337984000), (1980, 371609117551558656000), (2862, -2229654705309351936000), (2864, -743218235103117312000), (2865, -743218235103117312000), (2889, -2229654705309351936000), (2956, -4459309410618703872000), (2958, -2229654705309351936000), (2972, -2229654705309351936000), (2974, -743218235103117312000)]

def merged1098 : Integer.Sparse (Fin 3237) := [(373, 9515235662612805888000), (377, 2423026464653120256000), (380, 2423026464653120256000), (761, 4492312537306890240000), (825, 2246156268653445120000), (864, 2246156268653445120000), (869, 4669182733306565376000), (2832, -4669182733306565376000)]

def merged1099 : Integer.Sparse (Fin 3237) := [(373, 9515235662612805888000), (377, 2423026464653120256000), (380, 2423026464653120256000), (761, 4492312537306890240000), (825, 2246156268653445120000), (864, 2246156268653445120000), (869, 4669182733306565376000), (1006, -557336653721809920000), (1007, -185778884573936640000), (1016, -185778884573936640000), (1154, -557336653721809920000), (1178, -185778884573936640000), (1558, -1114673307443619840000), (1579, -557336653721809920000), (1606, -557336653721809920000), (1609, -557336653721809920000), (1946, -557336653721809920000), (1977, -185778884573936640000), (1980, -185778884573936640000), (2832, -4669182733306565376000)]

def merged1100 : Integer.Sparse (Fin 3237) := [(0, -34578088152501196800), (4, -8644522038125299200), (32, 34578088152501196800), (68, 138312352610004787200), (261, 77800698343127692800), (346, 1867216760235064627200), (351, 622405586745021542400), (355, 622405586745021542400), (373, 9515235662612805888000), (377, 2423026464653120256000), (380, 2423026464653120256000), (664, 185804558775779328000), (741, 3734433520470129254400), (746, 1867216760235064627200), (750, 1867216760235064627200), (761, 4492312537306890240000), (825, 2803569944980783104000), (864, 2246156268653445120000), (869, 4669182733306565376000), (871, 1867216760235064627200), (873, 622405586745021542400), (1006, -557336653721809920000), (1007, -185778884573936640000), (1016, -185778884573936640000), (1154, -557336653721809920000), (1178, 25674201842688000), (1470, 557413676327337984000), (1558, -1114673307443619840000), (1579, 77022605528064000), (1606, -557336653721809920000), (1609, 77022605528064000), (1946, -557336653721809920000), (1977, -185778884573936640000), (1980, 185830232977622016000), (2832, -4669182733306565376000), (2862, -2229654705309351936000), (2864, -743218235103117312000), (2865, -743218235103117312000), (2889, -2229654705309351936000), (2956, -4459309410618703872000), (2958, -2229654705309351936000), (2972, -2229654705309351936000), (2974, -743218235103117312000)]

def merged1101 : Integer.Sparse (Fin 3237) := [(0, -1313193296191084116480), (3, -1345910745303771494400), (4, 1673743909591589068800), (32, 2053444206108158438400), (68, 138312352610004787200), (261, 1423711443646899187200), (346, 1867216760235064627200), (351, 622405586745021542400), (355, 622405586745021542400), (373, 9515235662612805888000), (377, 2423026464653120256000), (380, 2423026464653120256000), (659, 48452786830935773798400), (664, 185804558775779328000), (697, 16150928943645257932800), (741, 3734433520470129254400), (746, 1867216760235064627200), (750, 1867216760235064627200), (761, 4492312537306890240000), (806, 96905573661871547596800), (825, 2803569944980783104000), (828, 48452786830935773798400), (829, 48452786830935773798400), (864, 2246156268653445120000), (869, 4669182733306565376000), (871, 1867216760235064627200), (873, 622405586745021542400), (1006, -557336653721809920000), (1007, -185778884573936640000), (1016, -185778884573936640000), (1154, -557336653721809920000), (1157, -90642338923884066345600), (1176, -79426946452294308168000), (1178, 25674201842688000), (1179, -26475648817431436056000), (1470, 557413676327337984000), (1558, -1114673307443619840000), (1579, 77022605528064000), (1606, -557336653721809920000), (1609, 77022605528064000), (1946, -557336653721809920000), (1977, -185778884573936640000), (1980, 185830232977622016000), (2310, 70537308464072024366400), (2320, -9664889482678108593600), (2818, 33177325637368783382400), (2832, -4669182733306565376000), (2862, -2229654705309351936000), (2864, -743218235103117312000), (2865, -743218235103117312000), (2889, -2229654705309351936000), (2956, -4459309410618703872000), (2958, -2229654705309351936000), (2972, -2229654705309351936000), (2974, -743218235103117312000)]

def merged1102 : Integer.Sparse (Fin 3237) := [(0, 1795231274054400), (3, 3989402831232000), (32, -997350707808000), (66, 15957611324928000), (160, 15957611324928000), (261, 9973507078080000), (328, -430855505773056000), (330, -143618501924352000), (352, -143618501924352000), (438, -430855505773056000), (507, -143618501924352000), (510, -430855505773056000), (513, -143618501924352000), (521, -143618501924352000), (588, 606438917347737600000), (727, -861711011546112000), (747, -430855505773056000), (761, 1212877834695475200000), (767, 606438917347737600000), (780, -430855505773056000), (866, -430855505773056000), (869, 606438917347737600000), (975, -430855505773056000), (1003, -143618501924352000), (1322, -861711011546112000), (1332, -430855505773056000), (1470, 606438917347737600000), (1473, -430855505773056000), (1526, -430855505773056000), (1622, -143618501924352000), (1628, -430855505773056000), (1632, -143618501924352000), (2315, -430855505773056000), (2321, -143618501924352000), (2579, -143618501924352000), (2832, -606438917347737600000)]

def merged1103 : Integer.Sparse (Fin 3237) := [(0, -12614250331167206400), (3, 663201698139187200), (4, 15684912701691609600), (32, 12614250331167206400), (68, 49130597928390451200), (165, -2652806792556748800), (261, 8880386262503616000), (651, 71625783399032217600), (660, 663263072033271091200), (689, 23875261133010739200), (697, 221087690677757030400), (698, 221087690677757030400), (800, 143251566798064435200), (807, 1326526144066542182400), (818, 71625783399032217600), (825, 71625783399032217600), (829, 663263072033271091200), (830, 663263072033271091200), (841, 71625783399032217600), (847, 71625783399032217600), (850, 663263072033271091200), (862, 23875261133010739200), (872, 221087690677757030400), (938, 71625783399032217600), (950, 23875261133010739200)]

def merged1104 : Integer.Sparse (Fin 3237) := [(0, -202921316601240993840), (3, -422241390013135896000), (4, 15684912701691609600), (32, 118340398258985977200), (66, -1691618366845100332800), (68, 49130597928390451200), (160, -1691618366845100332800), (165, -2652806792556748800), (261, -1048381093015684092000), (328, 45673695904817708985600), (330, 15224565301605902995200), (352, 15224565301605902995200), (438, 45673695904817708985600), (507, 15224565301605902995200), (651, 71625783399032217600), (660, 663263072033271091200), (689, 23875261133010739200), (697, 221087690677757030400), (698, 221087690677757030400), (727, 91347391809635417971200), (747, 45673695904817708985600), (780, 45673695904817708985600), (800, 143251566798064435200), (807, 1326526144066542182400), (818, 71625783399032217600), (825, 71625783399032217600), (829, 663263072033271091200), (830, 663263072033271091200), (841, 71625783399032217600), (847, 71625783399032217600), (850, 663263072033271091200), (862, 23875261133010739200), (866, 45673695904817708985600), (872, 221087690677757030400), (938, 71625783399032217600), (950, 23875261133010739200), (1473, 45673695904817708985600), (1622, 15224565301605902995200)]

def merged1105 : Integer.Sparse (Fin 3237) := [(0, -202919521369966939440), (3, -422237400610304664000), (4, 15684912701691609600), (32, 118339400908278169200), (66, -1691602409233775404800), (68, 49130597928390451200), (160, -1691602409233775404800), (165, -2652806792556748800), (261, -1048371119508606012000), (328, 45673265049311935929600), (330, 15224421683103978643200), (352, 15224421683103978643200), (438, 45673265049311935929600), (507, 15224421683103978643200), (510, -430855505773056000), (513, -143618501924352000), (521, -143618501924352000), (588, 606438917347737600000), (651, 71625783399032217600), (660, 663263072033271091200), (689, 23875261133010739200), (697, 221087690677757030400), (698, 221087690677757030400), (727, 91346530098623871859200), (747, 45673265049311935929600), (761, 1212877834695475200000), (767, 606438917347737600000), (780, 45673265049311935929600), (800, 143251566798064435200), (807, 1326526144066542182400), (818, 71625783399032217600), (825, 71625783399032217600), (829, 663263072033271091200), (830, 663263072033271091200), (841, 71625783399032217600), (847, 71625783399032217600), (850, 663263072033271091200), (862, 23875261133010739200), (866, 45673265049311935929600), (869, 606438917347737600000), (872, 221087690677757030400), (938, 71625783399032217600), (950, 23875261133010739200), (975, -430855505773056000), (1003, -143618501924352000), (1322, -861711011546112000), (1332, -430855505773056000), (1470, 606438917347737600000), (1473, 45673265049311935929600), (1526, -430855505773056000), (1622, 15224421683103978643200), (1628, -430855505773056000), (1632, -143618501924352000), (2315, -430855505773056000), (2321, -143618501924352000), (2579, -143618501924352000), (2832, -606438917347737600000)]

def merged1106 : Integer.Sparse (Fin 3237) := [(689, -11367993179963788300800), (862, -20011601790024768000), (1091, -34103979539891364902400), (1101, -60034805370074304000), (1167, -20011601790024768000), (1630, -11367993179963788300800), (1977, -20011601790024768000), (2818, 11367993179963788300800), (2819, 20011601790024768000)]

def merged1107 : Integer.Sparse (Fin 3237) := [(0, 3972383003321995691520), (3, -3055679233324612070400), (4, 1527839616662306035200), (32, 4583518849986918105600), (261, -1527839616662306035200), (315, -110004452399686034534400), (318, -55002226199843017267200), (323, -55002226199843017267200), (340, -55002226199843017267200), (716, -110004452399686034534400), (719, -110004452399686034534400), (724, -110004452399686034534400), (736, -110004452399686034534400), (806, -110004452399686034534400), (810, -55002226199843017267200), (829, -55002226199843017267200), (990, -10314788051937890304000), (992, -5157394025968945152000), (996, -5157394025968945152000), (1009, -5157394025968945152000), (2270, -10314788051937890304000), (2272, -10314788051937890304000), (2274, -10314788051937890304000), (2276, -10314788051937890304000), (2282, -10314788051937890304000), (2285, -5157394025968945152000), (2286, -5157394025968945152000), (2301, -10314788051937890304000), (2303, -10314788051937890304000), (2308, -5157394025968945152000), (2311, -5157394025968945152000), (2312, -5157394025968945152000), (2315, -5157394025968945152000), (2438, -10314788051937890304000), (2502, -5157394025968945152000)]

def merged1108 : Integer.Sparse (Fin 3237) := [(0, 3972383003321995691520), (3, -3055679233324612070400), (4, 1527839616662306035200), (32, 4583518849986918105600), (261, -1527839616662306035200), (315, -110004452399686034534400), (318, -55002226199843017267200), (323, -55002226199843017267200), (340, -55002226199843017267200), (716, -110004452399686034534400), (719, -110004452399686034534400), (724, -110004452399686034534400), (735, 10314526502955515904000), (736, -110004452399686034534400), (744, 5157263251477757952000), (748, 5157263251477757952000), (806, -110004452399686034534400), (810, -55002226199843017267200), (822, 10314526502955515904000), (829, -55002226199843017267200), (832, 5157263251477757952000), (866, 5157263251477757952000), (990, -10314788051937890304000), (992, -5157394025968945152000), (996, -5157394025968945152000), (1009, -5157394025968945152000), (1755, 10314526502955515904000), (1936, 5157263251477757952000), (2270, -10314788051937890304000), (2272, -10314788051937890304000), (2274, -261548982374400000), (2276, -10314788051937890304000), (2282, -10314788051937890304000), (2285, -130774491187200000), (2286, -130774491187200000), (2301, -10314788051937890304000), (2303, -261548982374400000), (2308, -5157394025968945152000), (2311, -130774491187200000), (2312, -5157394025968945152000), (2315, -130774491187200000), (2438, -261548982374400000), (2502, -130774491187200000), (2845, -41258106011822063616000), (2848, -20629053005911031808000), (2853, -20629053005911031808000), (2860, -20629053005911031808000), (2942, -41258106011822063616000), (2945, -41258106011822063616000), (2949, -41258106011822063616000), (2954, -41258106011822063616000), (2961, -41258106011822063616000), (2964, -20629053005911031808000), (2969, -20629053005911031808000)]

def merged1109 : Integer.Sparse (Fin 3237) := [(0, 3972383003321995691520), (3, -3055679233324612070400), (4, 1527839616662306035200), (32, 4583518849986918105600), (261, -1527839616662306035200), (315, -110004452399686034534400), (318, -55002226199843017267200), (323, -55002226199843017267200), (340, -55002226199843017267200), (689, -11367993179963788300800), (716, -110004452399686034534400), (719, -110004452399686034534400), (724, -110004452399686034534400), (735, 10314526502955515904000), (736, -110004452399686034534400), (744, 5157263251477757952000), (748, 5157263251477757952000), (806, -110004452399686034534400), (810, -55002226199843017267200), (822, 10314526502955515904000), (829, -55002226199843017267200), (832, 5157263251477757952000), (862, -20011601790024768000), (866, 5157263251477757952000), (990, -10314788051937890304000), (992, -5157394025968945152000), (996, -5157394025968945152000), (1009, -5157394025968945152000), (1091, -34103979539891364902400), (1101, -60034805370074304000), (1167, -20011601790024768000), (1630, -11367993179963788300800), (1755, 10314526502955515904000), (1936, 5157263251477757952000), (1977, -20011601790024768000), (2270, -10314788051937890304000), (2272, -10314788051937890304000), (2274, -261548982374400000), (2276, -10314788051937890304000), (2282, -10314788051937890304000), (2285, -130774491187200000), (2286, -130774491187200000), (2301, -10314788051937890304000), (2303, -261548982374400000), (2308, -5157394025968945152000), (2311, -130774491187200000), (2312, -5157394025968945152000), (2315, -130774491187200000), (2438, -261548982374400000), (2502, -130774491187200000), (2818, 11367993179963788300800), (2819, 20011601790024768000), (2845, -41258106011822063616000), (2848, -20629053005911031808000), (2853, -20629053005911031808000), (2860, -20629053005911031808000), (2942, -41258106011822063616000), (2945, -41258106011822063616000), (2949, -41258106011822063616000), (2954, -41258106011822063616000), (2961, -41258106011822063616000), (2964, -20629053005911031808000), (2969, -20629053005911031808000)]

def merged1110 : Integer.Sparse (Fin 3237) := [(0, 3769463481952028752080), (3, -3477916633934916734400), (4, 1543524529363997644800), (32, 4701858250895196274800), (66, -1691602409233775404800), (68, 49130597928390451200), (160, -1691602409233775404800), (165, -2652806792556748800), (261, -2576210736170912047200), (315, -110004452399686034534400), (318, -55002226199843017267200), (323, -55002226199843017267200), (328, 45673265049311935929600), (330, 15224421683103978643200), (340, -55002226199843017267200), (352, 15224421683103978643200), (438, 45673265049311935929600), (507, 15224421683103978643200), (510, -430855505773056000), (513, -143618501924352000), (521, -143618501924352000), (588, 606438917347737600000), (651, 71625783399032217600), (660, 663263072033271091200), (689, -11344117918830777561600), (697, 221087690677757030400), (698, 221087690677757030400), (716, -110004452399686034534400), (719, -110004452399686034534400), (724, -110004452399686034534400), (727, 91346530098623871859200), (735, 10314526502955515904000), (736, -110004452399686034534400), (744, 5157263251477757952000), (747, 45673265049311935929600), (748, 5157263251477757952000), (761, 1212877834695475200000), (767, 606438917347737600000), (780, 45673265049311935929600), (800, 143251566798064435200), (806, -110004452399686034534400), (807, 1326526144066542182400), (810, -55002226199843017267200), (818, 71625783399032217600), (822, 10314526502955515904000), (825, 71625783399032217600), (829, -54338963127809746176000), (830, 663263072033271091200), (832, 5157263251477757952000), (841, 71625783399032217600), (847, 71625783399032217600), (850, 663263072033271091200), (862, 3863659342985971200), (866, 50830528300789693881600), (869, 606438917347737600000), (872, 221087690677757030400), (938, 71625783399032217600), (950, 23875261133010739200), (975, -430855505773056000), (990, -10314788051937890304000), (992, -5157394025968945152000), (996, -5157394025968945152000), (1003, -143618501924352000), (1009, -5157394025968945152000), (1091, -34103979539891364902400), (1101, -60034805370074304000), (1167, -20011601790024768000), (1322, -861711011546112000), (1332, -430855505773056000), (1470, 606438917347737600000), (1473, 45673265049311935929600), (1526, -430855505773056000), (1622, 15224421683103978643200), (1628, -430855505773056000), (1630, -11367993179963788300800), (1632, -143618501924352000), (1755, 10314526502955515904000), (1936, 5157263251477757952000), (1977, -20011601790024768000), (2270, -10314788051937890304000), (2272, -10314788051937890304000), (2274, -261548982374400000), (2276, -10314788051937890304000), (2282, -10314788051937890304000), (2285, -130774491187200000), (2286, -130774491187200000), (2301, -10314788051937890304000), (2303, -261548982374400000), (2308, -5157394025968945152000), (2311, -130774491187200000), (2312, -5157394025968945152000), (2315, -561629996960256000), (2321, -143618501924352000), (2438, -261548982374400000), (2502, -130774491187200000), (2579, -143618501924352000), (2818, 11367993179963788300800), (2819, 20011601790024768000), (2832, -606438917347737600000), (2845, -41258106011822063616000), (2848, -20629053005911031808000), (2853, -20629053005911031808000), (2860, -20629053005911031808000), (2942, -41258106011822063616000), (2945, -41258106011822063616000), (2949, -41258106011822063616000), (2954, -41258106011822063616000), (2961, -41258106011822063616000), (2964, -20629053005911031808000), (2969, -20629053005911031808000)]

def merged1111 : Integer.Sparse (Fin 3237) := [(0, 2456270185760944635600), (3, -4823827379238688228800), (4, 3217268438955586713600), (32, 6755302457003354713200), (66, -1691602409233775404800), (68, 187442950538395238400), (160, -1691602409233775404800), (165, -2652806792556748800), (261, -1152499292524012860000), (315, -110004452399686034534400), (318, -55002226199843017267200), (323, -55002226199843017267200), (328, 45673265049311935929600), (330, 15224421683103978643200), (340, -55002226199843017267200), (346, 1867216760235064627200), (351, 622405586745021542400), (352, 15224421683103978643200), (355, 622405586745021542400), (373, 9515235662612805888000), (377, 2423026464653120256000), (380, 2423026464653120256000), (438, 45673265049311935929600), (507, 15224421683103978643200), (510, -430855505773056000), (513, -143618501924352000), (521, -143618501924352000), (588, 606438917347737600000), (651, 71625783399032217600), (659, 48452786830935773798400), (660, 663263072033271091200), (664, 185804558775779328000), (689, -11344117918830777561600), (697, 16372016634323014963200), (698, 221087690677757030400), (716, -110004452399686034534400), (719, -110004452399686034534400), (724, -110004452399686034534400), (727, 91346530098623871859200), (735, 10314526502955515904000), (736, -110004452399686034534400), (741, 3734433520470129254400), (744, 5157263251477757952000), (746, 1867216760235064627200), (747, 45673265049311935929600), (748, 5157263251477757952000), (750, 1867216760235064627200), (761, 5705190372002365440000), (767, 606438917347737600000), (780, 45673265049311935929600), (800, 143251566798064435200), (806, -13098878737814486937600), (807, 1326526144066542182400), (810, -55002226199843017267200), (818, 71625783399032217600), (822, 10314526502955515904000), (825, 2875195728379815321600), (828, 48452786830935773798400), (829, -5886176296873972377600), (830, 663263072033271091200), (832, 5157263251477757952000), (841, 71625783399032217600), (847, 71625783399032217600), (850, 663263072033271091200), (862, 3863659342985971200), (864, 2246156268653445120000), (866, 50830528300789693881600), (869, 5275621650654302976000), (871, 1867216760235064627200), (872, 221087690677757030400), (873, 622405586745021542400), (938, 71625783399032217600), (950, 23875261133010739200), (975, -430855505773056000), (990, -10314788051937890304000), (992, -5157394025968945152000), (996, -5157394025968945152000), (1003, -143618501924352000), (1006, -557336653721809920000), (1007, -185778884573936640000), (1009, -5157394025968945152000), (1016, -185778884573936640000), (1091, -34103979539891364902400), (1101, -60034805370074304000), (1154, -557336653721809920000), (1157, -90642338923884066345600), (1167, -20011601790024768000), (1176, -79426946452294308168000), (1178, 25674201842688000), (1179, -26475648817431436056000), (1322, -861711011546112000), (1332, -430855505773056000), (1470, 1163852593675075584000), (1473, 45673265049311935929600), (1526, -430855505773056000), (1558, -1114673307443619840000), (1579, 77022605528064000), (1606, -557336653721809920000), (1609, 77022605528064000), (1622, 15224421683103978643200), (1628, -430855505773056000), (1630, -11367993179963788300800), (1632, -143618501924352000), (1755, 10314526502955515904000), (1936, 5157263251477757952000), (1946, -557336653721809920000), (1977, -205790486363961408000), (1980, 185830232977622016000), (2270, -10314788051937890304000), (2272, -10314788051937890304000), (2274, -261548982374400000), (2276, -10314788051937890304000), (2282, -10314788051937890304000), (2285, -130774491187200000), (2286, -130774491187200000), (2301, -10314788051937890304000), (2303, -261548982374400000), (2308, -5157394025968945152000), (2310, 70537308464072024366400), (2311, -130774491187200000), (2312, -5157394025968945152000), (2315, -561629996960256000), (2320, -9664889482678108593600), (2321, -143618501924352000), (2438, -261548982374400000), (2502, -130774491187200000), (2579, -143618501924352000), (2818, 44545318817332571683200), (2819, 20011601790024768000), (2832, -5275621650654302976000), (2845, -41258106011822063616000), (2848, -20629053005911031808000), (2853, -20629053005911031808000), (2860, -20629053005911031808000), (2862, -2229654705309351936000), (2864, -743218235103117312000), (2865, -743218235103117312000), (2889, -2229654705309351936000), (2942, -41258106011822063616000), (2945, -41258106011822063616000), (2949, -41258106011822063616000), (2954, -41258106011822063616000), (2956, -4459309410618703872000), (2958, -2229654705309351936000), (2961, -41258106011822063616000), (2964, -20629053005911031808000), (2969, -20629053005911031808000), (2972, -2229654705309351936000), (2974, -743218235103117312000)]

def merged1112 : Integer.Sparse (Fin 3237) := [(360, -371521819290163807641600), (367, -185760909645081903820800), (369, -185760909645081903820800), (375, -185760909645081903820800), (719, -470199129949768026931200), (752, -470199129949768026931200), (758, -470199129949768026931200), (763, -470199129949768026931200), (828, -655960039594849930752000), (1755, -470199129949768026931200), (2840, 655960039594849930752000)]

def merged1113 : Integer.Sparse (Fin 3237) := [(0, 2997458560051200), (3, -2366414652672000), (4, -394402442112000), (32, 2366414652672000), (71, -3155219536896000), (261, -394402442112000), (306, -170381854992384000), (308, -85190927496192000), (310, -85190927496192000), (339, -85190927496192000), (529, -170381854992384000), (541, -85190927496192000), (664, -85190927496192000), (705, -170381854992384000), (708, -85190927496192000), (711, -170381854992384000), (714, -170381854992384000), (735, -289348389816026268672000), (744, -144674109717085638144000), (748, -144674109717085638144000), (826, -170381854992384000), (828, -144674280098940630528000), (832, -85190927496192000), (968, -170381854992384000), (970, -85190927496192000), (972, -85190927496192000), (994, -85190927496192000), (1032, -170381854992384000), (1038, -85190927496192000), (1178, -85190927496192000), (1758, -170381854992384000), (1786, -85190927496192000), (2245, -170381854992384000), (2247, -85190927496192000), (2260, -170381854992384000), (2262, -170381854992384000), (2274, -170381854992384000), (2309, -170381854992384000), (2310, -170381854992384000), (2311, -85190927496192000), (2319, -85190927496192000), (2320, -85190927496192000), (2449, -170381854992384000), (2451, -85190927496192000), (2575, -85190927496192000), (2580, -85190927496192000), (2840, 144674109717085638144000)]

def merged1114 : Integer.Sparse (Fin 3237) := [(0, 2997458560051200), (3, -2366414652672000), (4, -394402442112000), (32, 2366414652672000), (71, -3155219536896000), (261, -394402442112000), (306, -170381854992384000), (308, -85190927496192000), (310, -85190927496192000), (339, -85190927496192000), (360, -371521819290163807641600), (367, -185760909645081903820800), (369, -185760909645081903820800), (375, -185760909645081903820800), (529, -170381854992384000), (541, -85190927496192000), (664, -85190927496192000), (705, -170381854992384000), (708, -85190927496192000), (711, -170381854992384000), (714, -170381854992384000), (719, -470199129949768026931200), (735, -289348389816026268672000), (744, -144674109717085638144000), (748, -144674109717085638144000), (752, -470199129949768026931200), (758, -470199129949768026931200), (763, -470199129949768026931200), (826, -170381854992384000), (828, -800634319693790561280000), (832, -85190927496192000), (968, -170381854992384000), (970, -85190927496192000), (972, -85190927496192000), (994, -85190927496192000), (1032, -170381854992384000), (1038, -85190927496192000), (1178, -85190927496192000), (1755, -470199129949768026931200), (1758, -170381854992384000), (1786, -85190927496192000), (2245, -170381854992384000), (2247, -85190927496192000), (2260, -170381854992384000), (2262, -170381854992384000), (2274, -170381854992384000), (2309, -170381854992384000), (2310, -170381854992384000), (2311, -85190927496192000), (2319, -85190927496192000), (2320, -85190927496192000), (2449, -170381854992384000), (2451, -85190927496192000), (2575, -85190927496192000), (2580, -85190927496192000), (2840, 800634149311935568896000)]

def merged1115 : Integer.Sparse (Fin 3237) := [(0, -16903884307968000), (3, 13345171822080000), (4, 2224195303680000), (32, -13345171822080000), (71, 17793562429440000), (261, 2224195303680000), (306, 960852371189760000), (308, 480426185594880000), (310, 480426185594880000), (339, 480426185594880000), (529, 960852371189760000), (541, 480426185594880000), (664, 480426185594880000), (705, 960852371189760000), (708, 480426185594880000), (711, 960852371189760000), (714, 960852371189760000), (735, 960852371189760000), (826, 960852371189760000), (828, 960852371189760000), (832, 480426185594880000), (1065, -72994509093300876547200), (1075, -36497254546650438273600), (1758, 960852371189760000), (1786, 480426185594880000), (2310, -36497254546650438273600), (2818, 36497254546650438273600)]

def merged1116 : Integer.Sparse (Fin 3237) := [(0, -2428246697584021896960), (3, 852016385117200665600), (4, -852016385117200665600), (32, 2982057347910202329600), (68, -3408065540468802662400), (261, 2343045059072301830400), (319, 61345179728438447923200), (321, 30672589864219223961600), (324, 30672589864219223961600), (346, 30672589864219223961600), (720, 61345179728438447923200), (722, 61345179728438447923200), (725, 61345179728438447923200), (741, 61345179728438447923200), (849, 61345179728438447923200), (851, 30672589864219223961600), (871, 30672589864219223961600), (1004, 3223243787419772928000), (1005, 1611621893709886464000), (1006, 1611621893709886464000), (1008, 1611621893709886464000), (1112, 3223243787419772928000), (1132, 1611621893709886464000), (1178, 1611621893709886464000), (1508, 3223243787419772928000), (1526, 1611621893709886464000), (1531, 3223243787419772928000), (1543, 3223243787419772928000), (1558, 3223243787419772928000), (1561, 3223243787419772928000), (1579, 3223243787419772928000), (1630, 1611621893709886464000), (1906, 1611621893709886464000), (1917, 3223243787419772928000), (1946, 1611621893709886464000), (1949, 1611621893709886464000)]

def merged1117 : Integer.Sparse (Fin 3237) := [(0, -2428246697584021896960), (3, 852016385117200665600), (4, -852016385117200665600), (32, 2982057347910202329600), (68, -3408065540468802662400), (261, 2343045059072301830400), (319, 61345179728438447923200), (321, 30672589864219223961600), (324, 30672589864219223961600), (346, 30672589864219223961600), (574, -1611649167397355520000), (664, -1611649167397355520000), (720, 61345179728438447923200), (722, 61345179728438447923200), (725, 61345179728438447923200), (732, -3223298334794711040000), (741, 61345179728438447923200), (747, -1611649167397355520000), (825, -3223298334794711040000), (849, 61345179728438447923200), (851, 30672589864219223961600), (869, -1611649167397355520000), (871, 30672589864219223961600), (1004, 3223243787419772928000), (1005, 1611621893709886464000), (1006, 1611621893709886464000), (1008, 1611621893709886464000), (1112, 3223243787419772928000), (1132, -27273687469056000), (1178, -27273687469056000), (1391, -3223298334794711040000), (1508, 3223243787419772928000), (1526, -27273687469056000), (1531, 3223243787419772928000), (1543, -54547374938112000), (1558, 3223243787419772928000), (1561, -54547374938112000), (1579, -54547374938112000), (1630, -27273687469056000), (1906, 1611621893709886464000), (1917, 3223243787419772928000), (1946, 1611621893709886464000), (1949, -1611676441084824576000), (2849, 12893193339178844160000), (2851, 6446596669589422080000), (2854, 6446596669589422080000), (2862, 6446596669589422080000), (2868, 12893193339178844160000), (2946, 12893193339178844160000), (2950, 12893193339178844160000), (2956, 12893193339178844160000), (2966, 12893193339178844160000), (2970, 6446596669589422080000), (2972, 6446596669589422080000)]

def merged1118 : Integer.Sparse (Fin 3237) := [(0, -2428263601468329864960), (3, 852029730289022745600), (4, -852014160921896985600), (32, 2982044002738380249600), (68, -3408065540468802662400), (71, 17793562429440000), (261, 2343047283267605510400), (306, 960852371189760000), (308, 480426185594880000), (310, 480426185594880000), (319, 61345179728438447923200), (321, 30672589864219223961600), (324, 30672589864219223961600), (339, 480426185594880000), (346, 30672589864219223961600), (529, 960852371189760000), (541, 480426185594880000), (574, -1611649167397355520000), (664, -1611168741211760640000), (705, 960852371189760000), (708, 480426185594880000), (711, 960852371189760000), (714, 960852371189760000), (720, 61345179728438447923200), (722, 61345179728438447923200), (725, 61345179728438447923200), (732, -3223298334794711040000), (735, 960852371189760000), (741, 61345179728438447923200), (747, -1611649167397355520000), (825, -3223298334794711040000), (826, 960852371189760000), (828, 960852371189760000), (832, 480426185594880000), (849, 61345179728438447923200), (851, 30672589864219223961600), (869, -1611649167397355520000), (871, 30672589864219223961600), (1004, 3223243787419772928000), (1005, 1611621893709886464000), (1006, 1611621893709886464000), (1008, 1611621893709886464000), (1065, -72994509093300876547200), (1075, -36497254546650438273600), (1112, 3223243787419772928000), (1132, -27273687469056000), (1178, -27273687469056000), (1391, -3223298334794711040000), (1508, 3223243787419772928000), (1526, -27273687469056000), (1531, 3223243787419772928000), (1543, -54547374938112000), (1558, 3223243787419772928000), (1561, -54547374938112000), (1579, -54547374938112000), (1630, -27273687469056000), (1758, 960852371189760000), (1786, 480426185594880000), (1906, 1611621893709886464000), (1917, 3223243787419772928000), (1946, 1611621893709886464000), (1949, -1611676441084824576000), (2310, -36497254546650438273600), (2818, 36497254546650438273600), (2849, 12893193339178844160000), (2851, 6446596669589422080000), (2854, 6446596669589422080000), (2862, 6446596669589422080000), (2868, 12893193339178844160000), (2946, 12893193339178844160000), (2950, 12893193339178844160000), (2956, 12893193339178844160000), (2966, 12893193339178844160000), (2970, 6446596669589422080000), (2972, 6446596669589422080000)]

def merged1119 : Integer.Sparse (Fin 3237) := [(0, -2428260604009769813760), (3, 852027363874370073600), (4, -852014555324339097600), (32, 2982046369153032921600), (68, -3408065540468802662400), (71, 14638342892544000), (261, 2343046888865163398400), (306, 790470516197376000), (308, 395235258098688000), (310, 395235258098688000), (319, 61345179728438447923200), (321, 30672589864219223961600), (324, 30672589864219223961600), (339, 395235258098688000), (346, 30672589864219223961600), (360, -371521819290163807641600), (367, -185760909645081903820800), (369, -185760909645081903820800), (375, -185760909645081903820800), (529, 790470516197376000), (541, 395235258098688000), (574, -1611649167397355520000), (664, -1611253932139256832000), (705, 790470516197376000), (708, 395235258098688000), (711, 790470516197376000), (714, 790470516197376000), (719, -470199129949768026931200), (720, 61345179728438447923200), (722, 61345179728438447923200), (725, 61345179728438447923200), (732, -3223298334794711040000), (735, -289347428963655078912000), (741, 61345179728438447923200), (744, -144674109717085638144000), (747, -1611649167397355520000), (748, -144674109717085638144000), (752, -470199129949768026931200), (758, -470199129949768026931200), (763, -470199129949768026931200), (825, -3223298334794711040000), (826, 790470516197376000), (828, -800633358841419371520000), (832, 395235258098688000), (849, 61345179728438447923200), (851, 30672589864219223961600), (869, -1611649167397355520000), (871, 30672589864219223961600), (968, -170381854992384000), (970, -85190927496192000), (972, -85190927496192000), (994, -85190927496192000), (1004, 3223243787419772928000), (1005, 1611621893709886464000), (1006, 1611621893709886464000), (1008, 1611621893709886464000), (1032, -170381854992384000), (1038, -85190927496192000), (1065, -72994509093300876547200), (1075, -36497254546650438273600), (1112, 3223243787419772928000), (1132, -27273687469056000), (1178, -112464614965248000), (1391, -3223298334794711040000), (1508, 3223243787419772928000), (1526, -27273687469056000), (1531, 3223243787419772928000), (1543, -54547374938112000), (1558, 3223243787419772928000), (1561, -54547374938112000), (1579, -54547374938112000), (1630, -27273687469056000), (1755, -470199129949768026931200), (1758, 790470516197376000), (1786, 395235258098688000), (1906, 1611621893709886464000), (1917, 3223243787419772928000), (1946, 1611621893709886464000), (1949, -1611676441084824576000), (2245, -170381854992384000), (2247, -85190927496192000), (2260, -170381854992384000), (2262, -170381854992384000), (2274, -170381854992384000), (2309, -170381854992384000), (2310, -36497424928505430657600), (2311, -85190927496192000), (2319, -85190927496192000), (2320, -85190927496192000), (2449, -170381854992384000), (2451, -85190927496192000), (2575, -85190927496192000), (2580, -85190927496192000), (2818, 36497254546650438273600), (2840, 800634149311935568896000), (2849, 12893193339178844160000), (2851, 6446596669589422080000), (2854, 6446596669589422080000), (2862, 6446596669589422080000), (2868, 12893193339178844160000), (2946, 12893193339178844160000), (2950, 12893193339178844160000), (2956, 12893193339178844160000), (2966, 12893193339178844160000), (2970, 6446596669589422080000), (2972, 6446596669589422080000)]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def merged1135 : Integer.Sparse (Fin 3237) := [(788, 13260950362186329600), (795, 13260950362186329600), (817, 26521900724372659200), (1683, -26521900724372659200), (1890, -13260950362186329600)]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1000 : Sparse Master := [(Sum.inr 1000, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


