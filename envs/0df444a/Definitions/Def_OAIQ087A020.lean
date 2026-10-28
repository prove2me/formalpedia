-- Prove2me | Definitions.Def_OAIQ087A020
-- name    : OAIQ087A020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:29:09.584994+00:00
-- url     : https://prove2.me/theorems/986499f8-ad95-40a5-888e-f1021fee2091
-- title:
--   Definitions bundle OAIQ087A020 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 10 definitions. The definitions and types are `OAI.MaxCutGames.Decoder.ActualMatrixContradiction.expectationOf_inline_ActualMatrixContradiction`, `OAI.OptimalMaxCut.RawGrid.degree`, `OAI.OptimalMaxCut.RawGrid.edges`, `OAI.OptimalMaxCut.RawGrid.gridSize`, `OAI.OptimalMaxCut.RawGrid.length`, `OAI.OptimalMaxCut.RawGrid.param`, `OAI.OptimalMaxCut.RawGrid.row`, `OAI.OptimalMaxCut.RawGrid.scale`, `OAI.OptimalMaxCut.RawGrid.size`, `OAI.OptimalMaxCut.RawGrid.vertices`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`MaxCut_Encoding_ActualAdviceSampling`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Encoding/ActualAdviceSampling.lean), [`MaxCut_Estimates_ListSum`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/ListSum.lean), [`MaxCut_Estimates_Param`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/Param.lean).
--
--   **Imports.** It imports the bundles `OAIQ087A008`, `OAIQ087A001`, `OAIQ087A001`, `OAIQ087A005` and `OAIQ087A006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ087A028`; the proof of `OAI.MaxCutGames.Decoder.ActualMatrixContradiction.contradiction`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A008
import Definitions.Def_OAIQ087A001
import Definitions.Def_OAIQ087A001
import Definitions.Def_OAIQ087A005
import Definitions.Def_OAIQ087A006

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_ActualAdviceSampling
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The stochastic clean upper bound applies to the literal agreement of the two
actual local decoders.  The equality below retains every sampled mask, all
occurrence/position draws, and both independently uniform target maps.
-/

/-!
Pointwise and uniform-law identification of the retained projection seed with
the actual decoder draw. Auxiliary slots at full positions affect neither the
projection nor the displayed target question. The entire target map is retained
when it is repacked into its independent hidden and complement components.
-/

/-!
The complete seed used for the lower-bound conditioning argument and the
mask/slot/map experiment used for the clean upper bound have exactly the same
actual decoder success. Unused positions are removed only by the pointwise
observation equality; occurrence IDs and their ordered local copies remain.
-/

/-! The contradiction uses the same actual seed and local decoder on both
sides. Its lower bound comes from full-table variation followed by visible
conditioning; its upper bound comes from the exact incidence sampler. -/

namespace MaxCutGames.Decoder.ActualMatrixContradiction

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

def expectationOf_inline_ActualMatrixContradiction {X : Type*} {i : Fintype X}
    (μ : @FiniteDistribution X i) (f : X → ℝ) : ℝ :=
  @FiniteDistribution.expectation X i μ f

end
end MaxCutGames.Decoder.ActualMatrixContradiction

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_ListSum
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace OptimalMaxCut.RawGrid
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open CounterMachine.Expr LongCode
attribute [local instance] Classical.propDecidable

def vertices (s : List Bool) : ℕ := wordValue s 0
def edges (s : List Bool) : ℕ := wordValue s 2
def row (q : ℕ) (s : List Bool) (e j : ℕ) := wordValue s (3+e*(q+2)+j)
def degree (q : ℕ) (s : List Bool) (y : ℕ) :=
  ∑ e ∈ range (edges s), if row q s e 1=y then 1 else 0
def gridSize (q K : ℕ) (s : List Bool) : ℕ :=
  (K+1)*(vertices s * (edges s * (edges s * (2^q*2^q)))+1)
end OptimalMaxCut.RawGrid

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Param
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.RawGrid
open scoped BigOperators
open Finset CounterMachine.Expr
attribute [local instance] Classical.propDecidable

def param (q K : ℕ) (s : List Bool) : ℕ := Unweighted.searchPrime (K*(vertices s*2^q+1)^2)
def size (q K : ℕ) (s : List Bool) : ℕ := vertices s*2^q*(param q K s)^6
def scale (q K : ℕ) (s : List Bool) : ℕ := (param q K s)^12
def length (q L : ℕ) (s : List Bool) : ℕ :=
  (2*(size q L s).size+1)+(2*(scale q L s).size+1)+(size q L s)^2
end OptimalMaxCut.RawGrid

end

end OAI
end


