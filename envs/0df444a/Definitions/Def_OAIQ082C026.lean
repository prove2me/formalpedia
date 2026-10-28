-- Prove2me | Definitions.Def_OAIQ082C026
-- name    : OAIQ082C026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:57:51.173411+00:00
-- url     : https://prove2.me/theorems/c1b29a2c-9b34-4266-bd50-3a8ce00761ff
-- title:
--   Definitions bundle OAIQ082C026 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 5 definitions and 1 theorem. The definitions and types are `OAI.BinPackingGap.SearchUpdateMachine.initialTarget`, `OAI.BinPackingGap.graphPackingOutputInstance`, `OAI.BinPackingGap.graphPackingOutputReindexing`, `OAI.BinPackingGap.leftIncidencePosition`, `OAI.BinPackingGap.rightIncidencePosition`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`BinPacking_Configurations_K4Soundness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Configurations/K4Soundness.lean), [`BinPacking_Machines_GraphPackingOutput`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/GraphPackingOutput.lean), [`BinPacking_Search_SearchUpdateMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Search/SearchUpdateMachine.lean).
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C021` and `OAIQ082C022` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ082C028`; the proofs of `OAI_BinPackingGap_PCPFoundation_packingOutput_sound` and `OAI.BinPackingGap.PCPFoundation.packingOutput_sound_oaiq082`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C021
import Definitions.Def_OAIQ082C022

section
-- module Solutions.OAIQ082_BP.BinPacking_Configurations_K4Soundness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinPackingGap

def leftIncidencePosition (G : GraphInput) (R : ℕ) (edge : G.Edge) (j : Fin R) :
    G.IncidencePosition R (G.left edge) :=
  (⟨(edge, 0), G.endpoint_zero edge⟩, j)

def rightIncidencePosition (G : GraphInput) (R : ℕ) (edge : G.Edge) (j : Fin R) :
    G.IncidencePosition R (G.right edge) :=
  (⟨(edge, 1), G.endpoint_one edge⟩, j)

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

def graphPackingOutputInstance (c : ℕ) (ρ : ℝ) (x : GraphReductionInput) : Instance :=
  (graphPackingOutput c ρ x).2.toInstance (graphPackingOutput_valid c ρ x)

def graphPackingOutputReindexing (c : ℕ) (ρ : ℝ) (x : GraphReductionInput) :
    Instance.Reindexing (graphPackingOutputInstance c ρ x)
      (reductionInstance c ρ x.graph x.k) :=
  (reductionInventory c ρ x.graph x.k).rawItemListReindexing x.k_le
    (reductionInventory_plus_height c ρ x.graph x.k).le
    (reductionInventory_minus_height c ρ x.graph x.k).le

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchUpdateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchUpdateMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open SearchSemantics SearchEncoding BinaryEncoding

def initialTarget (phase : Phase) (answer : Bool) : Label × Ambient × List Bool :=
  match phase, answer with
  | .find, false => (.copyRest, ambient .find, [true])
  | .find, true => (.findBins, ambient .fill, [])
  | .fill, false => (.fillNoBins, ambient .fill, [])
  | .fill, true => (.fillYesBins, ambient .fill, [])
  | .done, answer => (.copyRest, ambient .done answer, [])
  | .invalid, answer => (.copyRest, ambient .invalid answer, [])

theorem copyBudget_le (s : State) (extra : Nat) (small : extra ≤ 1) :
    1 + (2 * (bodyBits s).length + extra + 3) ≤
      rawTime.eval ((stateBits s).length + 1) := by
  have lengths := stateBits_length s
  simp only [bodyBits_length, rawTime, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

end BinPackingGap.SearchUpdateMachine

end OAI
end


