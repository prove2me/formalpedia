-- Prove2me | Definitions.Def_OAIQ106D003
-- name    : OAIQ106D003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T11:55:32.675394+00:00
-- url     : https://prove2.me/theorems/742b384f-15c4-4284-826a-48624cdee874
-- title:
--   Definitions bundle OAIQ106D003 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5592 declarations of OpenAI's Lean: 5592 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.node2556`, `OAI.MUB6.Certificate.MixedSemantics.node2557`, `OAI.MUB6.Certificate.MixedSemantics.node2557Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2558`, `OAI.MUB6.Certificate.MixedSemantics.node2558Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2559`, `OAI.MUB6.Certificate.MixedSemantics.node2559Labels`, `OAI.MUB6.Certificate.MixedSemantics.node256`, `OAI.MUB6.Certificate.MixedSemantics.node2560`, `OAI.MUB6.Certificate.MixedSemantics.node2561`, `OAI.MUB6.Certificate.MixedSemantics.node2561Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2562`, `OAI.MUB6.Certificate.MixedSemantics.node2562Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2563`, `OAI.MUB6.Certificate.MixedSemantics.node2563Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2564`, `OAI.MUB6.Certificate.MixedSemantics.node2564Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2565`, `OAI.MUB6.Certificate.MixedSemantics.node2565Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2566`, `OAI.MUB6.Certificate.MixedSemantics.node2566Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2567`, `OAI.MUB6.Certificate.MixedSemantics.node2567Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2568`, `OAI.MUB6.Certificate.MixedSemantics.node2568Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2569`, `OAI.MUB6.Certificate.MixedSemantics.node2569Labels`, `OAI.MUB6.Certificate.MixedSemantics.node256Labels`, `OAI.MUB6.Certificate.MixedSemantics.node257`, `OAI.MUB6.Certificate.MixedSemantics.node2570`, `OAI.MUB6.Certificate.MixedSemantics.node2570Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2571`, `OAI.MUB6.Certificate.MixedSemantics.node2571Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2572`, `OAI.MUB6.Certificate.MixedSemantics.node2572Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2573`, `OAI.MUB6.Certificate.MixedSemantics.node2573Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2574`, `OAI.MUB6.Certificate.MixedSemantics.node2574Labels`, `OAI.MUB6.Certificate.MixedSemantics.node2575` and 5552 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical78`, `MutuallyUnbiased_MixedSemantics_Nodes39`, `MutuallyUnbiased_MixedSemantics_Nodes4`, `MutuallyUnbiased_MixedSemantics_Nodes40`, `MutuallyUnbiased_MixedSemantics_Nodes41`, `MutuallyUnbiased_MixedSemantics_Nodes42`, `MutuallyUnbiased_MixedSemantics_Nodes43`, `MutuallyUnbiased_MixedSemantics_Nodes44`, `MutuallyUnbiased_MixedSemantics_Nodes45`, `MutuallyUnbiased_MixedSemantics_Nodes46`, `MutuallyUnbiased_MixedSemantics_Nodes47`, `MutuallyUnbiased_MixedSemantics_Nodes48`, `MutuallyUnbiased_MixedSemantics_Nodes49`, `MutuallyUnbiased_MixedSemantics_Nodes5`, `MutuallyUnbiased_MixedSemantics_Nodes50`, `MutuallyUnbiased_MixedSemantics_Nodes51`, `MutuallyUnbiased_MixedSemantics_Nodes52`, `MutuallyUnbiased_MixedSemantics_Nodes53`, `MutuallyUnbiased_MixedSemantics_Nodes54`, `MutuallyUnbiased_MixedSemantics_Nodes55`, `MutuallyUnbiased_MixedSemantics_Nodes56`, `MutuallyUnbiased_MixedSemantics_Nodes57`, `MutuallyUnbiased_MixedSemantics_Nodes58`, `MutuallyUnbiased_MixedSemantics_Nodes59`, `MutuallyUnbiased_MixedSemantics_Nodes6`, `MutuallyUnbiased_MixedSemantics_Nodes60`, `MutuallyUnbiased_MixedSemantics_Nodes61`, `MutuallyUnbiased_MixedSemantics_Nodes62`, `MutuallyUnbiased_MixedSemantics_Nodes63`, `MutuallyUnbiased_MixedSemantics_Nodes64`, `MutuallyUnbiased_MixedSemantics_Nodes65`, `MutuallyUnbiased_MixedSemantics_Nodes66`, `MutuallyUnbiased_MixedSemantics_Nodes67`, `MutuallyUnbiased_MixedSemantics_Nodes68`, `MutuallyUnbiased_MixedSemantics_Nodes69`, `MutuallyUnbiased_MixedSemantics_Nodes7`, `MutuallyUnbiased_MixedSemantics_Nodes70`, `MutuallyUnbiased_MixedSemantics_Nodes71`, `MutuallyUnbiased_MixedSemantics_Nodes72`, `MutuallyUnbiased_MixedSemantics_Nodes73`, `MutuallyUnbiased_MixedSemantics_Nodes74`, `MutuallyUnbiased_MixedSemantics_Nodes75`, `MutuallyUnbiased_MixedSemantics_Nodes76`, `MutuallyUnbiased_MixedSemantics_Nodes77`, `MutuallyUnbiased_MixedSemantics_Nodes78`, `MutuallyUnbiased_MixedSemantics_Nodes79`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D131`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def node2557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2558 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def node2558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2559 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def node2559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2560 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]

def node2561 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node2561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def node2562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node2563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def node2564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def node2565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node2566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node2567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def node2568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2569 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node2569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node2570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def node2571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2572 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node2572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node2573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2574 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node2574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2575 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node2575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2576 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node2576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def node2577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def node2578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2579 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def node2579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def node2580Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2581 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def node2581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2582 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def node2582Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2583Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2584 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def node2584Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2585 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def node2585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node2586Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2588 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node2588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2589Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2590 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node2590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2591 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node2591Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2592 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def node2592Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2593Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2594 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2594Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2595 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2595Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2596 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node2596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2597 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def node2597Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2598 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def node2598Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2599 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2600 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node2600Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2601 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def node2601Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2602 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def node2602Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2603 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def node2603Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2604 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def node2604Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2605 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def node2605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2606Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2607Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2608 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def node2608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node2609Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node2610Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node2611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node2612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node2613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node2616Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2618 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def node2618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2619 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def node2619Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2620 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def node2620Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2621 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def node2621Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def node2622Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def node2623Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2624 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def node2624Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def node2625Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2626 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node2626Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2627 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def node2627Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2628Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2629 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def node2629Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node2630Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2631Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2632 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node2632Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2633 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node2633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2634 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def node2634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2635 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def node2635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node2636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2637 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node2637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2638 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node2638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2639 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def node2639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2640 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def node2640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2641 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node2641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2642 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def node2642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2643 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def node2643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2644 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def node2644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node2645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node2646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2647 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def node2647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2648 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -3, 0]]
def node2648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2649 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def node2649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2650 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def node2650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2651 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def node2651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def node2652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node2653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node2654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node2655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node2656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2657 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def node2657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2658 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def node2658Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2659 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def node2659Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node2660Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node2661Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node2662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node2663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2664 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def node2664Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node2665Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node2666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2667 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def node2667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node2668Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2670 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node2670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2671Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2672 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node2672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2673 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node2673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2674 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def node2674Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node2675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2677 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node2677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2678 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node2678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2679 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def node2679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2680 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def node2680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2681 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node2681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2682 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node2682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2683 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def node2683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2684 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2685 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def node2685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2686 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def node2686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2687 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def node2687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def node2688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def node2689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def node2690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def node2691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def node2692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node2693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node2694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node2695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def node2696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node2697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node2698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def node2699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node2700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node2701Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2702 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def node2702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2704 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def node2704Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2705 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def node2705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2706 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def node2706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def node2707Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node2708Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node2709Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node2710Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def node2711Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2712 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node2712Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def node2713Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node2714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def node2715Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2716 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def node2716Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def node2717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node2718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2719 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def node2719Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node2720Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2721Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2722 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node2722Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2723 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node2723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2724 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node2724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2725 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def node2725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2726 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def node2726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node2727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node2728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2729 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node2729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node2730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2731 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node2731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node2732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2733 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def node2733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2734 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def node2734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2735 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def node2735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2736 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node2736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2737 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def node2737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2738 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node2738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2739 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2740 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def node2740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2741 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2742 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def node2742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2743 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def node2743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2744 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def node2744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def node2745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -3, 1]]
def node2746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def node2747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2748 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def node2748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def node2749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node2750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2751 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node2751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2816 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node2816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2817 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node2817Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2818 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node2818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2819 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node2819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2820 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def node2820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2821 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 1, -3], ![3, -3, 0]]
def node2821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node2822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node2823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node2824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node2825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2827 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node2827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2828 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node2828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2829 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node2829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2830 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node2830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2831 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node2831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2832 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def node2832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2835 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node2835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2837 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node2837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2838 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node2838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2840 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2841 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node2841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2842 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def node2842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2843 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, 0, -2], ![2, 0, -2]]
def node2843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node2844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node2845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node2846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node2847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node2848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node2849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node2850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node2851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node2852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node2854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2855 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node2855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2856 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node2856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node2857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node2858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node2859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node2860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node2863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2865 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node2865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2866 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node2866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2867 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node2867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2868 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node2868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node2869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node2870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2871 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node2871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2872 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node2872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node2873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2875 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node2875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2876 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node2876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node2877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2879 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node2879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2881 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2882 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node2882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2883 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node2883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2884 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2885 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2886 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def node2886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2887 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 2, -3], ![3, -3, 0]]
def node2887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2888 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def node2888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2889 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def node2889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node2890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node2891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node2892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node2893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node2894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node2895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node2896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node2897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node2898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2899 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def node2899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node2900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node2901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node2902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node2903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2904 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def node2904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node2905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node2906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node2907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node2909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2910 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def node2910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2911 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def node2911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node2912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node2913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node2914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node2915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node2916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node2917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node2918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node2919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node2920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node2921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node2922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node2923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node2925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node2926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2929 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def node2929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2930 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def node2930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2931 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node2931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node2932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node2933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node2934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def node2935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node2936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node2937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def node2938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2939 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node2939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node2940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2941 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node2941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2942 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node2942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2943 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node2943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def node2944Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def node2945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2946 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def node2946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def node2947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2948 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def node2948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2949 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def node2949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node2950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2952 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node2952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2953Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2954 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node2954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2955 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node2955Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2956 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def node2956Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node2957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2959 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2960 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2961 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node2961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2962 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def node2962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2963 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2964 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node2964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2965 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def node2965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2966 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def node2966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2967 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def node2967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2968 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def node2968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2969 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def node2969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node2970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node2971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node2972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node2973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node2975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2978 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def node2978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2979 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def node2979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def node2980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node2981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node2982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node2983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node2984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node2985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2989 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def node2989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2990 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def node2990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2991 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def node2991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def node2992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2993 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node2993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node2994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2995 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def node2995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2997 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node2997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2998 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node2998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node2999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3000 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node3000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3001 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node3001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3002 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def node3002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3003 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node3003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3004 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def node3004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3005 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def node3005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3006 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def node3006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node3007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3072 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def node3072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node3073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3075 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def node3075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3077 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def node3077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3078 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def node3078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3079 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def node3079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node3080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node3081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3082 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def node3082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def node3083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node3084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node3085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3086 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node3086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node3087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3088 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node3088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3089 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node3089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3090 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def node3090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node3091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3092 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def node3092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node3093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3094 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node3094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3095 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def node3095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3096 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def node3096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3097 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node3097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3098 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def node3098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3099 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node3099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3100 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3101 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def node3101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3102 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def node3102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3103 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def node3103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def node3104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def node3105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3106 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def node3106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, -1, 0]]
def node3107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3108 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def node3108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3109 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node3109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3110 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node3110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3111 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node3111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3112 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node3112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3113 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def node3113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3114 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def node3114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3115 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def node3115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3116 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def node3116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3117 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def node3117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3118 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def node3118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3119 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node3119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3120 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node3120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3121 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def node3121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3122 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node3122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3123 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def node3123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3124 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def node3124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3125 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def node3125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3126 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 2, 1], ![3, -2, -1]]
def node3126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3129 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node3129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3131 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node3131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3132 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node3132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node3133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node3134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node3135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3264 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def node3264Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3265 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node3265Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3266 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def node3266Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3268 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def node3268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3270 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node3270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3271 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def node3271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3272 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def node3272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3273 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node3273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3274 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node3274Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3275 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def node3275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3276 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def node3276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3277 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def node3277Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node3278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node3279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node3280Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node3281Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node3282Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3283 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def node3283Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3284 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def node3284Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3285Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3286Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3287 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def node3287Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node3288Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node3289Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3290Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3291 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node3291Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3292Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3293 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node3293Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3294 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node3294Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3295 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node3295Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3296 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node3296Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3297 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node3297Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3298 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def node3298Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3299 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3300 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def node3300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3301 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def node3301Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3302 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def node3302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3303 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node3303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3304 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3304Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3305 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def node3305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3306 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def node3306Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3307 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def node3307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3308 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def node3308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3309 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def node3309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3310 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]
def node3310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3311 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]
def node3311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3312 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]
def node3312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3313 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -2, 4], ![2, 2, -4]]
def node3313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node3314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node3315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node3316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node3317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3318 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def node3318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3319 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node3319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3322 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def node3322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node3323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node3324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3325 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def node3325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3326 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def node3326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3327 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node3327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node3456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3457 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def node3457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def node3458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node3459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node3460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node3461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node3462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node3463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node3464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node3465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node3466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3468 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node3468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3470 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node3470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3471 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node3471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3472 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def node3472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node3473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node3474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3475 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def node3475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node3476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3478 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node3478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3479 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node3479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3480 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def node3480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3481 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node3481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3482 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node3482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3483 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3484 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def node3484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3485 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def node3485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3486 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def node3486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node3487Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node3488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node3489Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node3490Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node3491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node3492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node3494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node3495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node3497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3498 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def node3498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node3499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node3500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node3501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node3502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node3504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3506 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def node3506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3507 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def node3507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node3508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node3509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node3510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node3511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3512 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def node3512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node3513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node3514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node3515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node3516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node3517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def node3518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node3519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node3520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3522 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def node3522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3523 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def node3523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node3524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node3525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node3526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def node3527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node3528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node3529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3530 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def node3530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node3531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3533 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node3533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3534 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node3534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3535 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node3535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node3536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node3537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3538 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node3538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node3539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3540 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node3540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3541 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node3541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3542 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node3542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3543 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node3543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3544 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3545 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def node3545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3546 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3547 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3548 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def node3548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3549 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def node3549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node3550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node3551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3552 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def node3552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node3553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3555 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def node3555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def node3556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node3557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node3558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node3559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node3560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node3561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3564 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def node3564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3565 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def node3565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node3566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node3567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node3568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node3569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3570 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node3570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node3571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3572 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node3572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3573 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node3573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node3574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3575 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def node3575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node3576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3577 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node3577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3578 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node3578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3579 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def node3579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3580 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node3580Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3581 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3582 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def node3582Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3583 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def node3583Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node3776Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node3777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node3778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node3779Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node3780Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node3781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node3782Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node3783Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node3784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node3785Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node3786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node3788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3790 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def node3790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node3791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node3792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node3793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node3794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node3795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node3796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node3797Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node3799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node3800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node3801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def node3802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node3803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node3804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node3805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3807 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node3807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3808 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node3808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3809 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node3809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node3810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3811 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node3811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node3812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3813 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node3813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3814 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node3814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3815 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node3815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3816 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3817 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def node3817Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node3818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node3819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node3820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node3822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3824 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def node3824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def node3825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node3826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node3827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def node3828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node3829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node3830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3831 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def node3831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node3832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node3833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node3834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node3835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node3837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node3838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node3839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node3840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node3841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node3842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3845 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def node3845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node3846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node3847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node3848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node3849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3850 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node3850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node3851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3852 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node3852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3853 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node3853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3854 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def node3854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node3855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3856 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node3856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3857 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node3857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3858 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node3858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3859 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3860 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def node3860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3861 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3862 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def node3862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def node3863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def node3864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def node3865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node3866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3868 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def node3868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def node3869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node3870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node3871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node3872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node3873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node3874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3876 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def node3876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3877 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def node3877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def node3878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def node3879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node3880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3881 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node3881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node3882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3883 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node3883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3884 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node3884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3885 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node3885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3886 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def node3886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3887 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node3887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3888 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def node3888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3889 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def node3889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def node3890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3891 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def node3891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3892 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def node3892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3893 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]
def node3893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3894 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def node3894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def node3895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def node3896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def node3897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3898 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def node3898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def node3899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def node3900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node3901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3902 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def node3902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3903 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def node3903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3904 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def node3904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3905 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def node3905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3906 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def node3906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3907 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def node3907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3908 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def node3908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def node3909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3910 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def node3910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3911 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def node3911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3912 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def node3912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3913 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def node3913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3914 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node3914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3915 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def node3915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3916 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def node3916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node3917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node3918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node3919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node3920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node3922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node3923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def node3924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node3925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node3926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3929 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node3929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3931 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3932 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node3932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3933 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3934 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def node3934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node3935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3939 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node3939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3940 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node3940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3941 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node3941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node3942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node3943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node3944Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node3946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node3948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node3950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node3951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node3953Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node3954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node3955Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node3956Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3958 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node3958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3959 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node3959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3960 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node3960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3961 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3962 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3963 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def node3963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node3964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node3966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node3968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node3969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node3970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node3971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node3972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node3973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node3976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node3977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node3978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node3979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node3980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3981 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node3981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3982 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node3982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3983 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node3983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3984 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node3984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3985 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3986 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def node3986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3987 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def node3987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node3988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node3989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node3990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node3991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3993 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def node3993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node3994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3995 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node3995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3996 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node3996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3997 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node3997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3998 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node3998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3999 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node3999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4000 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def node4000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4001 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def node4001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node4002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4003 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def node4003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4004 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def node4004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4005 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node4005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4006 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def node4006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def node4007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def node4008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def node4009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4010 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def node4010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def node4011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4012 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def node4012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4013 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node4013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4014 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def node4014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4015 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def node4015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4016 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def node4016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4017 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def node4017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4018 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def node4018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4019 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def node4019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4020 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def node4020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4021 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def node4021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node4024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node4025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node4026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4027 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node4027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4028 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node4028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4029 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node4029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4030 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def node4030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node4032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node4033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node4034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4035 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node4035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4036 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node4036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4037 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def node4037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node4038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4039 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def node4039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4040 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def node4040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def node4041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4042 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def node4042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4043 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]
def node4043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node4044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def node4045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node4046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4047 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def node4047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4048 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def node4048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4049 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2]]
def node4049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4050 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node4050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def node4051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4052 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node4052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node4053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4054 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def node4054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4055 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def node4055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node4056 : Matrix (Fin 6) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def node4056Labels : Fin 2 → Fin 2 := ![0, 1]

def node4057 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def node4057Labels : Fin 2 → Fin 2 := ![0, 1]

def node4058 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]
def node4058Labels : Fin 2 → Fin 2 := ![0, 1]

def node4059 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]
def node4059Labels : Fin 2 → Fin 2 := ![0, 1]

def node4060 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def node4060Labels : Fin 2 → Fin 2 := ![0, 1]

def node4061 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]
def node4061Labels : Fin 2 → Fin 2 := ![0, 1]

def node4062 : Matrix (Fin 2) (Fin 2) ℤ := ![![-5, 5], ![5, -5]]
def node4062Labels : Fin 2 → Fin 2 := ![0, 1]

def node4063 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def node4063Labels : Fin 2 → Fin 2 := ![0, 1]

def node4064 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def node4064Labels : Fin 2 → Fin 2 := ![0, 1]

def node4065 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def node4065Labels : Fin 2 → Fin 2 := ![0, 1]

def node4066 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def node4066Labels : Fin 2 → Fin 2 := ![0, 1]

def node4067 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def node4067Labels : Fin 2 → Fin 2 := ![0, 1]

def node4068 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def node4068Labels : Fin 2 → Fin 2 := ![0, 1]

def node4069 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def node4069Labels : Fin 2 → Fin 2 := ![0, 1]

def node4070 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def node4070Labels : Fin 2 → Fin 2 := ![0, 1]

def node4071 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def node4071Labels : Fin 2 → Fin 2 := ![0, 1]

def node4072 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]
def node4072Labels : Fin 2 → Fin 2 := ![0, 1]

def node4073 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def node4073Labels : Fin 2 → Fin 2 := ![0, 1]

def node4074 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def node4074Labels : Fin 2 → Fin 2 := ![0, 1]

def node4075 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def node4075Labels : Fin 2 → Fin 2 := ![0, 1]

def node4076 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]
def node4076Labels : Fin 2 → Fin 2 := ![0, 1]

def node4077 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def node4077Labels : Fin 2 → Fin 2 := ![0, 1]

def node4078 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def node4078Labels : Fin 2 → Fin 2 := ![0, 1]

def node4079 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def node4079Labels : Fin 2 → Fin 2 := ![0, 1]

def node4080 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def node4080Labels : Fin 2 → Fin 2 := ![0, 1]

def node4081 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def node4081Labels : Fin 2 → Fin 2 := ![0, 1]

def node4082 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def node4082Labels : Fin 2 → Fin 2 := ![0, 1]

def node4083 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def node4083Labels : Fin 2 → Fin 2 := ![0, 1]

def node4084 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def node4084Labels : Fin 2 → Fin 2 := ![0, 1]

def node4085 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def node4085Labels : Fin 2 → Fin 2 := ![0, 1]

def node4086 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def node4086Labels : Fin 2 → Fin 2 := ![0, 1]

def node4087 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def node4087Labels : Fin 2 → Fin 2 := ![0, 1]

def node4088 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def node4088Labels : Fin 2 → Fin 2 := ![0, 1]

def node4089 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def node4089Labels : Fin 2 → Fin 2 := ![0, 1]

def node4090 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def node4090Labels : Fin 2 → Fin 2 := ![0, 1]

def node4091 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def node4091Labels : Fin 2 → Fin 2 := ![0, 1]

def node4092 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def node4092Labels : Fin 2 → Fin 2 := ![0, 1]

def node4093 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def node4093Labels : Fin 2 → Fin 2 := ![0, 1]

def node4094 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def node4094Labels : Fin 2 → Fin 2 := ![0, 1]

def node4095 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def node4095Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4352 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node4352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4353 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node4353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4354 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node4354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4355 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node4355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4356 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def node4356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4357 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node4357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4358 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def node4358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4359 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def node4359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4360 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def node4360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4361 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def node4361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4362 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def node4362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node4363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node4364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4365 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node4365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4367 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node4367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4368 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node4368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4369 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node4369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4370 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def node4370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4371 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node4371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4372 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node4372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4373 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def node4373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4374 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def node4374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4375 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def node4375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4377 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node4377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4378 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node4378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node4379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4380 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node4380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4381 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node4381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4382 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def node4382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4383 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def node4383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node4384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node4385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node4386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node4387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4388 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def node4388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4389 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node4389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node4390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node4391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node4392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node4393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4394 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def node4394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node4395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node4397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4398 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node4398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4401 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node4401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4402 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node4402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4403 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node4403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4404 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node4404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4405 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def node4405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node4406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node4407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4408 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node4408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4410 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node4410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4411 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node4411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4412 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node4412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4413 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def node4413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node4414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node4415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4416 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node4416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node4417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4418 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node4418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4419 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node4419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4420 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node4420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4421 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def node4421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node4422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4423 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4424 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node4424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4425 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node4425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4426 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def node4426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4427 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node4427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4428 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def node4428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4429 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def node4429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4430 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def node4430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4431 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node4431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4432 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node4432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node4433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node4434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node4435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node4436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4437 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node4437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node4438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node4439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4440 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node4440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node4441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4442 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node4442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4443 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node4443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4444 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node4444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4445 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def node4445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node4446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4447 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def node4447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4448 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node4448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node4449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4450 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node4450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node4451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4452 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node4452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4453 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node4453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4454 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node4454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node4455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node4456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4457 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node4457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4458 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node4458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4459 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node4459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4460 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node4460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4461 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4462 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node4462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4463 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node4463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4464 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node4464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4465 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def node4465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4466 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node4466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4467 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node4467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4468 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def node4468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node4469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4470 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node4470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4471 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node4471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4472 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def node4472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node4473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4474 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node4474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4475 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node4475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4476 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node4476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4477 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node4477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4478 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node4478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4479 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def node4479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4546 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4547 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node4547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4548 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node4548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4549 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4551 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node4551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4552 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node4552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4553 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node4553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4554 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node4554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4555 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def node4555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4556 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node4556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4557 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def node4557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4558 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def node4558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4559 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def node4559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4560 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def node4560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4562 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node4562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4564 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node4564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4565 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node4565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node4566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4567 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node4567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4568 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node4568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node4569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4570 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4571 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node4571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4572 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def node4572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4573 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def node4573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4574 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def node4574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4575 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def node4575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node4576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node4577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node4578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node4579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node4580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node4582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4583 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def node4583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4584 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def node4584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4585 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node4585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4586 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node4586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node4587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4588 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node4588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node4589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node4590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4591 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node4591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4592 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node4592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4593 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node4593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4594 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def node4594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node4595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4596 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node4596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4597 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node4597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node4598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node4599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4600 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node4600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node4601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4602 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4603 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node4603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4604 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node4604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4605 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def node4605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4606 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4607 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4800 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node4800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node4801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node4802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node4803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4804 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node4804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node4806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4807 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node4807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4808 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node4808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4809 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def node4809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4810 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node4810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4811 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node4811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node4812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node4813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4814 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def node4814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node4815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node4816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4817 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node4817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node4818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4819 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node4819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4820 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def node4820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4821 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node4821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node4822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4823 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def node4823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node4824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node4825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node4826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4827 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node4827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4828 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node4828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4829 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def node4829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node4830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node4831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4832 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node4832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node4833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4834 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4835 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node4835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4836 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node4836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4837 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def node4837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4838 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4839 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4840 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def node4840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4841 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4842 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def node4842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4843 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def node4843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4844 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def node4844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4845 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def node4845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4846 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node4847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node4848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node4849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4850 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node4850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node4851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node4852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4853 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node4853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node4854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4855 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node4855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4856 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node4856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node4857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4858 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node4858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node4859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4860 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node4860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4861 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node4861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4862 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def node4862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node4863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node4992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node4993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node4994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node4995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node4997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5000 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node5000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5001 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node5001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5002 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node5002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5003 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node5003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node5004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node5005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5006 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node5006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node5007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5008 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node5008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5009 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node5009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5010 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node5010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node5011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node5012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node5013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5014 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node5014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5015 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node5015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5016 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node5016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5017 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node5017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5018 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node5018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5019 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node5019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5020 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node5020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5021 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def node5021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5022 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def node5022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5023 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def node5023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5024 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def node5024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node5025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node5026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node5027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node5028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node5029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node5030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node5031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node5032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node5033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node5034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node5035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node5036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node5037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node5038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node5039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node5040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node5041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node5042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node5043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node5044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node5045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node5046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node5047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node5048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node5049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node5050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node5051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node5052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node5053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node5054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node5055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node5056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node5056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node5057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node5058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node5059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node5060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node5061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5062 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def node5062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5063 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node5063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node5064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node5065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node5066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node5067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node5068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node5069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node5070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node5071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node5072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node5073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node5074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5075 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node5075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node5076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node5077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5078 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node5078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5079 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def node5079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5080 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node5080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5081 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node5081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node5082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node5083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5084 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def node5084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node5085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node5086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5087 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node5087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node5088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5089 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def node5089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5090 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node5090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node5091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node5092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node5093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5094 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node5094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5095 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node5095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5096 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10000Labels : Fin 3 → Fin 2 := ![0, 1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node256 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def node256Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node257Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node258 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def node258Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node259Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node260 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node260Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node261 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node261Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node262 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node262Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node263 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node263Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node264 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def node264Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node265 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node265Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node266 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node266Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node267 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node267Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node268 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node268Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node269 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node269Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node270 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def node270Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node271 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def node271Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node272 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def node272Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node273 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node273Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node274 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node274Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node275 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node275Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node276 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node276Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node277 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def node277Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node278Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node279 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def node279Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node280Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node281 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def node281Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node282 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node282Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node283Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node284 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node284Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node285 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node285Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node286 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node286Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node287 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node287Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node288 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node288Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node289 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node289Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node290 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def node290Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node291Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node292Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node293Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node294Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node295Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node296Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node297Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node298Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node299Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node300Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node301Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node302Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node303 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node303Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node304Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node305 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node305Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node306 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node306Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node307 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node307Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node308 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node308Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node309 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node309Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node310Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node311 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node311Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node312 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node312Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node313 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node313Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node314 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node314Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node315 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def node315Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node316 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def node316Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node317Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node318Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node319Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node2752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2753 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node2753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2754 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def node2754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2755 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def node2755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def node2756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def node2757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2758 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def node2758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2759 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def node2759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2760 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def node2760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2761 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def node2761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2762 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def node2762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2763 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node2763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2764 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node2764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2765 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node2765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2766 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node2766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2767 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node2767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2768 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node2768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2769 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def node2769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2770 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def node2770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2771 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def node2771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2772 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def node2772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2773 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node2773Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2774 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def node2774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2775 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node2775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2776 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node2776Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2777 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def node2777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2778 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def node2778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2779 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def node2779Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2780 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def node2780Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2781 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def node2781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2782 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node2782Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2783 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def node2783Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2784 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node2784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2785 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2785Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2786 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def node2786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2787 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def node2787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2788 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def node2788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2789 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def node2789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2790 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def node2790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2792 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node2792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2794 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node2794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node2795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node2796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node2797Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node2798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node2799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node2800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node2801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2802 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node2802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2803 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node2803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2805 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node2805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node2806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node2808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2811 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node2811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2812 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node2812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2813 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node2813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2815 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node2815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3010 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def node3010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3011 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def node3011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def node3012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node3013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3014 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def node3014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node3015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node3016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node3017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node3018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node3019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node3020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node3021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3022 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def node3022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3024 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def node3024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3025 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def node3025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3026 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def node3026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def node3027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node3028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node3029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node3030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3031 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node3031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node3032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3033 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def node3033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node3034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3035 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def node3035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node3036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3038 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node3038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3039 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node3039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3040 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node3040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node3041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3042 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node3042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node3043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3044 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node3044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3045 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node3045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3046 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def node3046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3047 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def node3047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3048 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node3048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3049 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![2, 2, -4]]
def node3049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3050 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node3050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3051 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3052 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def node3052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3053 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3054 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def node3054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3055 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def node3055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3056 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def node3056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def node3057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def node3058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def node3059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def node3060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node3061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def node3062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def node3063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node3064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node3065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node3066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node3067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node3068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node3069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def node3070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node3071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3136Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3138 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node3138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3139Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3141 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node3141Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3142 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node3142Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3143 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node3143Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3144 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node3144Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3145 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, 0, -2], ![3, -3, 0]]
def node3145Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node3146Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3147 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node3147Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node3148Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3149Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3150Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3151 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node3151Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3152 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node3152Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3153Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3154 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node3154Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3155Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3156 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3156Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3157 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node3157Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3158 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3158Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3159 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node3159Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3160 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -2, 0], ![2, 1, -3]]
def node3160Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3161 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def node3161Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node3162Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node3163Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node3164Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node3165Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3166 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def node3166Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node3167Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node3168Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node3169Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node3171Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3172Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node3173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3174 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node3174Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node3175Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node3176Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3177 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node3177Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3178 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node3178Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3180 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node3180Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3181 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node3181Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3183 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node3183Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3184 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3184Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3185 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3185Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3186 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -3, 0]]
def node3186Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3187 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def node3187Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3188 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def node3188Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node3189Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node3190Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node3191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node3192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node3193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node3194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node3195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3198 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def node3198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node3199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node320Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node321Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node322Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node323 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def node323Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node324 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def node324Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node325 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node325Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node326Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node327Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node328 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node328Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node329 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node329Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node330Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node331Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node332 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node332Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node333 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node333Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node334Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node335 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node335Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node336 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node336Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node337 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node337Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node338 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def node338Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node339 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node339Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node340 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node340Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node341 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def node341Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node342 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def node342Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node343 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def node343Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node344 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def node344Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node345Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node346 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def node346Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node347Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node348 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node348Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node349 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node349Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node350 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def node350Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node351Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node352 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node352Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node353 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node353Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node354 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def node354Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node355 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def node355Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node356Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node357Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node358Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node359Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node360Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node361 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node361Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node362 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node362Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node363Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node364 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node364Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node365 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node365Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node366 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def node366Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node367 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node367Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node368 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node368Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node369 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def node369Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node370Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node371Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node372 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def node372Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node373Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node374 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node374Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node375Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node376Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node377 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node377Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node378 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node378Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node379 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def node379Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node380Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node381 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node381Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node382Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node383 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node383Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node3200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node3201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node3202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node3203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3206 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def node3206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3207 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def node3207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3208 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node3208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3210 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node3210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3211 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node3211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node3212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3213 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node3213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3214 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node3214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3215 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -3, 0]]
def node3215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3216 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -2, 0], ![2, -1, -1]]
def node3216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node3217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3219 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def node3219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3220 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def node3220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3222 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def node3222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3223 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3224 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def node3224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3225 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def node3225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3227 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def node3227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3228 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node3228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3229 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def node3229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3230 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def node3230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3231 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def node3231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node3232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3233 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node3233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3235 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node3235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3236 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node3236Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3237 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![2, 0, -2], ![2, 1, -3]]
def node3237Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3238Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3239Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3240 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node3240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3241Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3242 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node3242Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3243 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node3243Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3244Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3245 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node3245Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3246 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node3246Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3247 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, -1, -1], ![2, 1, -3]]
def node3247Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3248 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, 0, -2], ![2, 0, -2]]
def node3248Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node3249Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node3250Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node3251Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3252 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def node3252Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node3253Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3254 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def node3254Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node3255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node3256Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node3257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node3258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node3259Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node3260Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node3261Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3262 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def node3262Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3263Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3328 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node3328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3329 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def node3329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3330 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def node3330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3331 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![2, 0, -2], ![2, 1, -3]]
def node3331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node3332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node3333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node3334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node3335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node3336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node3337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node3338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node3339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node3342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3343 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node3343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3344 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node3344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node3345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3348 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node3348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3349 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node3349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node3350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node3351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3353 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node3353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3354 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node3354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3355 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node3355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3356 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node3356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3357 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node3357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3358 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node3358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3359 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node3359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3360 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![2, -1, -1], ![2, 1, -3]]
def node3360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3361 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![2, 0, -2], ![2, 0, -2]]
def node3361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node3362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node3363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node3364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node3365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node3366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node3367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node3368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node3369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node3370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node3371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3372 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node3372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node3373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node3374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node3375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node3377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3379 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node3379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3380 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node3380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node3381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node3382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3383 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node3383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3385 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node3385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3386 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node3386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node3387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3389 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node3389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3391 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3392 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node3392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3393 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node3393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3394 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3395 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node3395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3396 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -2, 0], ![2, 1, -3]]
def node3396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3397 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def node3397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node3398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node3399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node3400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node3401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3402 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def node3402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node3403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node3404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node3405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node3406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node3407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node3408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node3409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3411 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def node3411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3412 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node3412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3413 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def node3413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3415 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def node3415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3417 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node3417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3418 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def node3418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3419 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def node3419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3420 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node3420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3421 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node3421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3422 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def node3422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3423 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def node3423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node3424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def node3425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def node3426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def node3427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def node3428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node3429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node3430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node3431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node3432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node3433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node3434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node3435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node3436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node3437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node3438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3439 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def node3439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node3440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node3441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node3442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node3443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node3445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node3447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3448 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def node3448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def node3449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node3450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def node3451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def node3452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node3453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def node3454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node3455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3584 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def node3584Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def node3585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def node3586Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def node3587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3588 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def node3588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def node3589Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def node3590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3591 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def node3591Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3592 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def node3592Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def node3593Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3594 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]
def node3594Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3595 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def node3595Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3596 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def node3596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def node3597Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]
def node3598Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def node3599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def node3600Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def node3601Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def node3602Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3603 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def node3603Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def node3604Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def node3605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3606 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def node3606Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3607 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def node3607Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3608 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]
def node3608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def node3609Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def node3610Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3611 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]
def node3611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3612 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def node3612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3613 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def node3613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3614 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]
def node3614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3615 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]
def node3615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3616 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def node3616Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def node3617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def node3618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3619 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def node3619Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def node3620Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3621 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def node3621Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3622 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node3622Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3623 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def node3623Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3624 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def node3624Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3625 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def node3625Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3626 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def node3626Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3627 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def node3627Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3628 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def node3628Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3629 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]
def node3629Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3630 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def node3630Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3631 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def node3631Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3632 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def node3632Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3633 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def node3633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3634 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -1, 0], ![1, 2, -3]]
def node3634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3635 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 0, -1], ![1, 1, -2]]
def node3635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3636 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -1, 3], ![2, 1, -3]]
def node3636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node3637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node3638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node3639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node3640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node3641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node3642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def node3643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node3644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def node3645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node3646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node3647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node3648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node3649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node3651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node3653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3654 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node3654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node3655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node3656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node3658Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3659Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3660 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node3660Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3661 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node3661Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node3662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node3663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3664 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node3664Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3665 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node3665Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3666 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node3666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node3667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node3668Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node3669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node3670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node3671Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node3672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node3673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node3674Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node3675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node3676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node3677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node3678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node3679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node3680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node3681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node3682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node3683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node3684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node3685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node3686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node3687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node3688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node3689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node3691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3693 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node3693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3694 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node3694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node3695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node3696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node3697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node3698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3699 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node3699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node3700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3701Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3702 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node3702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3704 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3704Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3705 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node3705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3706 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node3706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3707 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def node3707Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node3708Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node3709Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node3710Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node3711Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node3712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node3712Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node3713Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node3714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node3715Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node3716Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node3717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node3718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3719Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node3720Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3721Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node3722Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node3723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node3724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def node3725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node3726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node3727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3728 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node3728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def node3729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node3732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3733 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node3733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node3734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3736 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node3736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3737 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node3737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3738 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node3738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3739 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node3739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3740 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def node3740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3741 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def node3741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def node3742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node3743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node3744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node3745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node3746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node3747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node3748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node3749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node3750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node3751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node3752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node3753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node3754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def node3755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node3756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node3757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node3758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node3759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node3760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node3761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node3762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node3763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node3764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node3765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3766 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node3766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3767 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node3767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node3768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node3769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3770 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node3770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3771 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node3771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3772 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def node3772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3773 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node3773Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3774 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node3774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node3775 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def node3775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node384 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node384Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node385 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def node385Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node386 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node386Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node387 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node387Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node388 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def node388Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node389 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def node389Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node390 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def node390Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node391 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def node391Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def node392Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node393 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def node393Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node394Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node395 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node395Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node396Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node397 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node397Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node398 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def node398Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node399 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def node399Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node400 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node400Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node401 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node401Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node402 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node402Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node403 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node403Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node404 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node404Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node405 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node405Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node406 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def node406Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node407 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def node407Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node408 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def node408Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node409 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node409Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node410 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def node410Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node411 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node411Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node412 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node412Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node413 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def node413Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node414 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node414Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node415 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def node415Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node416 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node416Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node417 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node417Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node418 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def node418Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node419 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def node419Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node420 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def node420Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node421 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def node421Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node422 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def node422Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node423Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node424Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node425Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node426Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node427Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node428Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node429Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node430Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node431Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node432 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node432Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node433 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node433Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node434Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node435 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node435Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node436Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node437 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node437Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node438 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node438Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node439Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node440Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node441Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node442Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node443Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node444Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node445Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node446 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node446Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node447 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node447Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4096 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def node4096Labels : Fin 2 → Fin 2 := ![0, 1]

def node4097 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]
def node4097Labels : Fin 2 → Fin 2 := ![0, 1]

def node4098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4099 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node4099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4101 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4102 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4103 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def node4103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4105 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node4105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4106 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node4106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4107 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node4107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4108 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def node4108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4109 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def node4109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4110 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node4110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4111 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node4111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4112 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def node4112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node4113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4114 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node4114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4115 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node4115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4116 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def node4116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node4117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4118 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4119 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node4119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4120 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node4120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4121 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node4121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4122 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node4122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4123 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node4123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4124 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![4, 0, -4]]
def node4124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4125 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4126 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4127 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node4127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4128 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node4128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4129 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node4129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4130 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node4130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4131 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![4, -1, -3]]
def node4131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4132 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node4132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4133 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node4133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4134 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def node4134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4135 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -2, 0], ![3, 1, -4]]
def node4135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4136 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -1, -1], ![3, 0, -3]]
def node4136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4137 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 0, -2], ![3, -1, -2]]
def node4137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4138 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def node4138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4140 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node4140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4141 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node4141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4142 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def node4142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4144 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node4144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4145 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node4145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4146 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def node4146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4147 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def node4147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4148 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def node4148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node4149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node4150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4151 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node4151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4153 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node4153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4154 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node4154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4155 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node4155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4156 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def node4156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4157 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node4157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4158 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node4158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4159 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def node4159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4160 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node4160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4161 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node4161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4162 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node4162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4163 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def node4163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node4164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4165 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4166 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def node4166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4167 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node4167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4168 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def node4168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node4169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4170 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node4170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node4171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4172 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4173 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node4173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4174 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node4174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4175 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4176 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4177 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4177Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4178 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node4178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4179 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node4179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4180 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4181 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def node4181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4182 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4183 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node4183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4184 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node4184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4185 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node4185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4186 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node4186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4187 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def node4187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4188 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node4188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4189 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def node4189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4190 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def node4190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4191 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def node4191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4192 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def node4192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4193 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def node4193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4194 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def node4194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node4195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4198 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def node4198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node4199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node4200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node4201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4202 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def node4202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4203 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def node4203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4204 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node4204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4205 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node4205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node4206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node4207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4208 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def node4208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node4210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4211 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node4211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4212 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node4212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4213 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node4213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4214 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node4214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4215 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![4, 0, -4]]
def node4215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4218 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node4218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4219 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node4219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4220 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node4220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4221 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node4221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4222 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![4, -1, -3]]
def node4222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4223 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node4223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4224 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node4224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4225 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def node4225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4226 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def node4226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4227 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def node4227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4228 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def node4228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4229 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def node4229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4231 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node4231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4233 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4234 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4235 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def node4235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4237 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node4237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4238 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node4238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4239 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node4239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4240 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def node4240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4241 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def node4241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4242 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def node4242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4243 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def node4243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node4244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node4245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node4246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4247 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def node4247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node4248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node4249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node4250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4251 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node4251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4253 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node4253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4254 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node4254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4255 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node4255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4256 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node4256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4257 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def node4257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node4258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4259 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node4259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4260 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node4260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4261 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node4261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4262 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![4, -3, -1]]
def node4262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node4263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4264 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4265 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node4265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4266 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node4266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4267 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4268 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4269 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node4269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4270 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node4270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4271 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def node4271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4272 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node4272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4273 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node4273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4274 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def node4274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4275 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4276 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node4276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4277 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def node4277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4278 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node4278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4279 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node4279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4280 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def node4280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4281 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def node4281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4282 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![4, -3, -1]]
def node4282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4283 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node4283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4284 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def node4284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4285 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def node4285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node4286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4289 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def node4289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node4290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node4291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node4292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4293 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def node4293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4294 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def node4294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4295 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node4295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4296 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node4296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node4297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node4298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4299 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def node4299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node4301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4302 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node4302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4303 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node4303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4304 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node4304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4305 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node4305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4308 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node4308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4309 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node4309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4310 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node4310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4311 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node4311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4312 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def node4312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4313 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node4313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4314 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node4314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4315 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def node4315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4316 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def node4316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4317 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def node4317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4318 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def node4318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4319 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def node4319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node4320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node4321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node4322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node4323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4324 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def node4324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4325 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def node4325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node4326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node4327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node4328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node4329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4330 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def node4330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node4331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node4332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4333 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def node4333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4334 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node4334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4335 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node4335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4336 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node4336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4338 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def node4338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4339 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node4339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node4340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node4342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4343 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node4343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4346 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4347 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node4347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4348 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node4348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4349 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4350 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def node4350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node448Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node449 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node449Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node450 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node450Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node451 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def node451Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node452 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def node452Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node453Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node454Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node455Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node456Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node457Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node458Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node459Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node460 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def node460Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node461Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node462Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node463Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node464Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node465 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node465Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node466 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node466Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node467 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node467Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node468 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node468Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node469 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def node469Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node470Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node471Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node472Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node473Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node474 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def node474Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node475Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node476Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node477Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node478Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node479Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node480Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node481Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node482Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node483 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def node483Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node484Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node485Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node486Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node487 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node487Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node488Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node489 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node489Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node490 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node490Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node491 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def node491Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node492Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node493 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node493Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node494 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node494Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node495 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def node495Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node496 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def node496Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node497Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node498 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node498Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node499Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node500 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node500Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node501 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def node501Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node502 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node502Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node503 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def node503Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node504 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def node504Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node505 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def node505Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node506 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node506Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node507 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def node507Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node508Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node509 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node509Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node510 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def node510Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node511Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4480 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node4480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4481 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def node4481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node4482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4483 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node4483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4484 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def node4484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4485 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def node4485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4486 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node4486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4487 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node4487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4488 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def node4488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4489 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node4489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4490 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node4490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4491 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node4491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4492 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def node4492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4493 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def node4493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4494 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node4494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4495 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node4495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4496 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node4496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4497 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node4497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4498 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4498Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4499 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node4499Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4500 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node4500Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4501 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def node4501Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4502 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4502Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4503 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4503Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4504 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def node4504Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4505 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def node4505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4506 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def node4506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4507 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def node4507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4508 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def node4508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4509 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def node4509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4510 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def node4510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4511 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def node4511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4512 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def node4512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4514 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node4514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4515 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node4515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4517 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node4517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4518 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node4518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4519 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def node4519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4520 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def node4520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node4521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node4522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node4523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node4524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4525 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def node4525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4526 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def node4526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node4527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node4528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node4529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node4530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4531 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def node4531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node4532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node4533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4534 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node4534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4535 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node4535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4536 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node4536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4538 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def node4538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4539 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node4539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node4540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node4542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4543 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node4543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4608 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def node4608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4609 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def node4609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4610 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def node4610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4611 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def node4611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4612 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node4612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4613 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node4613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4614 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def node4614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4615 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def node4615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4616 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node4616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4617 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node4617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4618 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node4618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4619 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node4619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4620 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node4620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4621 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def node4621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4622 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node4622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4623 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node4623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4624 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node4624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4625 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def node4625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4626 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def node4626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4627 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def node4627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4628 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def node4628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4629 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def node4629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node4630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node4633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node4634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node4635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4636 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def node4636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4637 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node4637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4638 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node4638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node4639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node4640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node4642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4643 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node4643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4644 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node4644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4645 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node4645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4646 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node4646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4649 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node4649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4650 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node4650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4651 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node4651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4652 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node4652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4653 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node4653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4654 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node4654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4655 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, -1, -1], ![3, 0, -3]]
def node4655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4656 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 0, -2], ![3, -1, -2]]
def node4656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4657 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def node4657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node4658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node4659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node4660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node4661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4662 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def node4662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node4663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node4664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node4665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node4666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node4667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node4668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4669 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node4669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4670 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node4670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4671 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node4671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4673 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def node4673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4674 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node4674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node4675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node4677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4678 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node4678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4681 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4682 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node4682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4683 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node4683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4684 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4686 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node4686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4687 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node4687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4688 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node4688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4689 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node4689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4690 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node4690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4691 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def node4691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4692 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def node4692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4693 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def node4693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4694 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def node4694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node4695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node4696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4697 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node4697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4699 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node4699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4700 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node4700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4701 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node4701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4702 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node4702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4703 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node4703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4704 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def node4704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4705 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def node4705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node4706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node4707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node4708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node4709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node4710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node4711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node4712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node4713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node4714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node4715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node4716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node4717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4718 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def node4718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4719 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def node4719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node4720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node4723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node4724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node4725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4726 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def node4726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4727 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def node4727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node4728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node4729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node4730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node4731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node4732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node4733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node4734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node4735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node4737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4738 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node4738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4741 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node4741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4742 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node4742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4743 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def node4743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4744 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node4744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4745 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node4745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4747 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node4747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4748 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def node4748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4749 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node4749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4750 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node4750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4751 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def node4751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4752 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node4752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4753 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def node4753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4754 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def node4754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def node4755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node4756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node4757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node4758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node4759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node4761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node4762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node4764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node4765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node4766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node4767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node4768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4769 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def node4769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4770 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def node4770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node4771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node4772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node4773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node4774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node4775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4776 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def node4776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4777 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def node4777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node4778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node4779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node4780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node4781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node4782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node4783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node4784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node4785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node4787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4788 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def node4788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4789 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def node4789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4790 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node4790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node4791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node4792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node4793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node4794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node4795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node4796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node4797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node4798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node4799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node4864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4865 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node4865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4866 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node4866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4867 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node4867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4868 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def node4868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4869 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4870 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node4870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4871 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def node4871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4872 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def node4872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4873 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def node4873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4874 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def node4874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4875 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def node4875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node4876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4877 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node4877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node4878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4879 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node4879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4880 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node4880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4881 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def node4881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4882 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node4882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4883 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def node4883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4884 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def node4884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node4885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4886 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def node4886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node4887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4888 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node4888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4889 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node4889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4890 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node4890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4891 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node4891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4892 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def node4892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4893 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node4893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4894 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node4894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4895 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node4895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4896 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node4896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4897 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def node4897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4898 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node4898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4899 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def node4899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4900 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def node4900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4901 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def node4901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node4904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node4905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node4906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4907 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node4907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4908 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node4908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node4909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node4910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node4912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4913 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node4913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4914 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node4914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4915 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node4915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4918 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node4918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4919 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node4919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4920 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node4920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4921 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node4921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4922 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node4922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4923 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node4923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4924 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 0, -2], ![3, -1, -2]]
def node4924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4925 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def node4925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node4926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node4927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node4928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node4928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node4929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node4930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node4931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node4932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node4933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4934 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node4934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4935 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node4935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node4936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4937 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node4937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node4938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node4940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node4942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4943 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4944 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node4944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4945 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node4945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4946 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4948 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node4948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4949 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node4949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4950 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node4950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4951 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node4951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4952 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def node4952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4953 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def node4953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node4954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node4955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node4956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node4957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node4958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4959 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def node4959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def node4960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def node4961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def node4962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node4963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node4964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4965 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def node4965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4966 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node4966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node4967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node4968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node4969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4970 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node4970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node4971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4972 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node4972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4973 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node4973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4974 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node4974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node4975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4976 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node4976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4977 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node4977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4978 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def node4978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4979 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def node4979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node4980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node4981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4982 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def node4982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4983 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def node4983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4984 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def node4984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node4985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node4986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node4987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node4988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node4989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node4990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node4991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node4991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end


