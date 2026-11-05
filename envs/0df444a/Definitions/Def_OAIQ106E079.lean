-- Prove2me | Definitions.Def_OAIQ106E079
-- name    : OAIQ106E079
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T17:55:55.63317+00:00
-- url     : https://prove2.me/theorems/862a78cd-2bc4-4988-adcc-06dc53b98f2f
-- title:
--   Definitions bundle OAIQ106E079 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7805 declarations of OpenAI's Lean: 7805 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.node1000`, `OAI.MUB6.Certificate.MixedSemantics.node1000Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1001`, `OAI.MUB6.Certificate.MixedSemantics.node1001Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1002`, `OAI.MUB6.Certificate.MixedSemantics.node1002Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1003`, `OAI.MUB6.Certificate.MixedSemantics.node1003Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1004`, `OAI.MUB6.Certificate.MixedSemantics.node1004Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1005`, `OAI.MUB6.Certificate.MixedSemantics.node1005Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1006`, `OAI.MUB6.Certificate.MixedSemantics.node1006Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1007`, `OAI.MUB6.Certificate.MixedSemantics.node1007Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1008`, `OAI.MUB6.Certificate.MixedSemantics.node1008Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1009`, `OAI.MUB6.Certificate.MixedSemantics.node1009Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1010`, `OAI.MUB6.Certificate.MixedSemantics.node1010Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1011`, `OAI.MUB6.Certificate.MixedSemantics.node1011Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1012`, `OAI.MUB6.Certificate.MixedSemantics.node1012Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1013`, `OAI.MUB6.Certificate.MixedSemantics.node1013Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1014`, `OAI.MUB6.Certificate.MixedSemantics.node1014Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1015`, `OAI.MUB6.Certificate.MixedSemantics.node1015Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1016`, `OAI.MUB6.Certificate.MixedSemantics.node1016Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1017`, `OAI.MUB6.Certificate.MixedSemantics.node1017Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1018`, `OAI.MUB6.Certificate.MixedSemantics.node1018Labels`, `OAI.MUB6.Certificate.MixedSemantics.node1019`, `OAI.MUB6.Certificate.MixedSemantics.node1019Labels` and 7765 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Nodes10`, `MutuallyUnbiased_MixedSemantics_Nodes11`, `MutuallyUnbiased_MixedSemantics_Nodes12`, `MutuallyUnbiased_MixedSemantics_Nodes13`, `MutuallyUnbiased_MixedSemantics_Nodes14`, `MutuallyUnbiased_MixedSemantics_Nodes15`, `MutuallyUnbiased_MixedSemantics_Nodes16`, `MutuallyUnbiased_MixedSemantics_Nodes17`, `MutuallyUnbiased_MixedSemantics_Nodes18`, `MutuallyUnbiased_MixedSemantics_Nodes19`, `MutuallyUnbiased_MixedSemantics_Nodes2`, `MutuallyUnbiased_MixedSemantics_Nodes20`, `MutuallyUnbiased_MixedSemantics_Nodes21`, `MutuallyUnbiased_MixedSemantics_Nodes22`, `MutuallyUnbiased_MixedSemantics_Nodes23`, `MutuallyUnbiased_MixedSemantics_Nodes24`, `MutuallyUnbiased_MixedSemantics_Nodes25`, `MutuallyUnbiased_MixedSemantics_Nodes26`, `MutuallyUnbiased_MixedSemantics_Nodes27`, `MutuallyUnbiased_MixedSemantics_Nodes28`, `MutuallyUnbiased_MixedSemantics_Nodes29`, `MutuallyUnbiased_MixedSemantics_Nodes3`, `MutuallyUnbiased_MixedSemantics_Nodes30`, `MutuallyUnbiased_MixedSemantics_Nodes31`, `MutuallyUnbiased_MixedSemantics_Nodes32`, `MutuallyUnbiased_MixedSemantics_Nodes33`, `MutuallyUnbiased_MixedSemantics_Nodes34`, `MutuallyUnbiased_MixedSemantics_Nodes35`, `MutuallyUnbiased_MixedSemantics_Nodes36`, `MutuallyUnbiased_MixedSemantics_Nodes37`, `MutuallyUnbiased_MixedSemantics_Nodes38`, `MutuallyUnbiased_MixedSemantics_Nodes39`, `MutuallyUnbiased_MixedSemantics_Nodes4`, `MutuallyUnbiased_MixedSemantics_Nodes40`, `MutuallyUnbiased_MixedSemantics_Nodes41`, `MutuallyUnbiased_MixedSemantics_Nodes42`, `MutuallyUnbiased_MixedSemantics_Nodes43`, `MutuallyUnbiased_MixedSemantics_Nodes44`, `MutuallyUnbiased_MixedSemantics_Nodes45`, `MutuallyUnbiased_MixedSemantics_Nodes46`, `MutuallyUnbiased_MixedSemantics_Nodes47`, `MutuallyUnbiased_MixedSemantics_Nodes48`, `MutuallyUnbiased_MixedSemantics_Nodes49`, `MutuallyUnbiased_MixedSemantics_Nodes5`, `MutuallyUnbiased_MixedSemantics_Nodes50`, `MutuallyUnbiased_MixedSemantics_Nodes51`, `MutuallyUnbiased_MixedSemantics_Nodes52`, `MutuallyUnbiased_MixedSemantics_Nodes53`, `MutuallyUnbiased_MixedSemantics_Nodes54`, `MutuallyUnbiased_MixedSemantics_Nodes55`, `MutuallyUnbiased_MixedSemantics_Nodes56`, `MutuallyUnbiased_MixedSemantics_Nodes57`, `MutuallyUnbiased_MixedSemantics_Nodes58`, `MutuallyUnbiased_MixedSemantics_Nodes59`, `MutuallyUnbiased_MixedSemantics_Nodes6`, `MutuallyUnbiased_MixedSemantics_Nodes60`, `MutuallyUnbiased_MixedSemantics_Nodes61`, `MutuallyUnbiased_MixedSemantics_Nodes62`, `MutuallyUnbiased_MixedSemantics_Nodes63`, `MutuallyUnbiased_MixedSemantics_Nodes64`, `MutuallyUnbiased_MixedSemantics_Nodes65`, `MutuallyUnbiased_MixedSemantics_Nodes66`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E080` and `OAIQ106E082`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node648 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node649 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node650 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def node650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node651 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node652 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node653 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node654 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def node654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node655 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def node655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node657 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node658Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node659 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node659Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node660 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node660Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node661 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![4, -1, -3]]
def node661Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node663 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node664 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node664Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node665 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def node665Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node667 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node668 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node668Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node669 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node670 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def node670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node671 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def node671Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node672 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node673 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![4, 0, -4]]
def node673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node674Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node675 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node676 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def node676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node677 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node678 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def node678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node679 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def node679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node680 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![4, -1, -3]]
def node680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node681 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node682 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node683 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def node683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node684 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def node684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node685 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def node685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node686 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def node686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node687 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node688 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node689 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node690 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def node690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node691 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![3, 1, -4]]
def node691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node692 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def node692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node693 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 1, -2], ![3, 0, -3]]
def node693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node694 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 2, -3], ![3, -1, -2]]
def node694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node695 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![2, -1, -1], ![2, 2, -4]]
def node695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node696 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![2, 0, -2], ![2, 1, -3]]
def node696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node697 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, -1, 5], ![4, 1, -5]]
def node697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node701 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def node701Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

set_option maxHeartbeats 1000000 in
def node703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node704Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node705 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def node705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node706 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def node706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node707 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node707Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node708 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node708Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node709Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node710Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node711 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def node711Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node712Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node713Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node714 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

set_option maxHeartbeats 1000000 in
def node715 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node715Labels : Fin 3 → Fin 2 := ![0, 0, 1]

set_option maxHeartbeats 1000000 in
def node716 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node716Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node717 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node718 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![4, 0, -4]]
def node718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node719Labels : Fin 3 → Fin 2 := ![0, 0, 1]

set_option maxHeartbeats 1000000 in
def node720 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node720Labels : Fin 3 → Fin 2 := ![0, 0, 1]

set_option maxHeartbeats 1000000 in
def node721 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node721Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node722 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node722Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node723 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![4, -1, -3]]
def node723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node724 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node725 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node726 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def node726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node727 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def node727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node728 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def node728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node729 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def node729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node731 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node733 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node734 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node735 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def node735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node737 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node738 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node739 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node740 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def node740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node741 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def node741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node742 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def node742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node743 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def node743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node747 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -1, -3]]
def node747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node750 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def node750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node752 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def node752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node753 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def node753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node755 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def node755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node757 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def node757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node758 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def node758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node759 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![4, -1, -3]]
def node759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node762 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def node762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node763 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def node763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node764 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def node764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node765 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def node765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node767 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node768 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node769 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def node769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node770 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def node770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node771 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def node771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node772 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def node772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node773 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def node773Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node774 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def node774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node775 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node776Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node779 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def node779Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node780Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node781 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node782Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node783Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node785 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node785Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node787 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node788 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node789 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node790 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node791 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def node791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node794 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node795 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node796 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node797 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![4, -3, -1]]
def node797Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node799 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node800 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node801 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def node801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node804 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node806 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node807 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node808 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node809 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node810 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node811 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node812 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node813 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node814 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def node814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node815 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node816 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node817 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def node817Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node819 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node820 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def node820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node823 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node824 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node825 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node826 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node827 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node828 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node829 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def node829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node830 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node831 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node832 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def node832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node834 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node835 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node836 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def node836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node837 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def node837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node838 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![2, -2, 0], ![2, -1, -1]]
def node838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node839 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![4, -3, -1]]
def node839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node840 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node841 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node842 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def node842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node843 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def node843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node844 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def node844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node845 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![3, 2, -5]]
def node845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node846 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def node846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node847 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node848 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node849 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node850 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node851 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node852 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node853 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node854 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 3, -4], ![2, -2, 0]]
def node854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node855 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![3, 1, -4]]
def node855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node856 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node857 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node858 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node859 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def node859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node860 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def node860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node861 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 3, -4], ![3, -3, 0]]
def node861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node862 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -2, 0], ![2, 2, -4]]
def node862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node863 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -1, -1], ![2, 1, -3]]
def node863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node867 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def node867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node871 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def node871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node872 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def node872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node874 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node877 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def node877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node880 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node881 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node882 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node883 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node886 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node887 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node888 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node889 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node890 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def node890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node891 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node892 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node893 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def node893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node894 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def node894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node895 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def node895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node896 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def node896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node897 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def node897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node902 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def node902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node903 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def node903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node908 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def node908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node911 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def node911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node912 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node913 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node914 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node916 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def node916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node917 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node921 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node924 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node925 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node927 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node928 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def node928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node930 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node931 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node932 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node933 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node934 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def node934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node935 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node936 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def node936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node937 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def node937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node938 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def node938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node939 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def node939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node940 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def node940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node943 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node944Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node945 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node946 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node947 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node948 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def node948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node949 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node950 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node951 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def node951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node952 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def node952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node953 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def node953Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node954 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def node954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node955Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node956 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node956Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node957 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node959 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node960 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node961 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![3, 1, -4]]
def node961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node962 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def node962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node963 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def node963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node968 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def node968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node969 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def node969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node970 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node975 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def node975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node979 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node982 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node983 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node984 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node985 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node986 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def node986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node989 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node991 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node992 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node993 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node994 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def node994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node997 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node999 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1000 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1001 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node1001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1002 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def node1002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1004 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1005 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1006 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node1006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1007 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def node1007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1008 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node1008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1009 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def node1009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1010 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def node1010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1011 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def node1011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1012 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node1012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1013 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node1013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node1014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node1015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1016 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def node1016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node1017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node1018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1019 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node1019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1022 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node1022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node1023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1024 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node1024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1025 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node1025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1026 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node1026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1027 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def node1027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node1028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1029 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def node1029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1030 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node1030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1031 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def node1031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1033 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node1033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1035 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node1035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1036 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node1036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1037 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node1037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node1038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1040 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1041 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1042 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node1042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1043 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node1043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1044 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1045 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node1045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1046 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node1046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1047 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node1047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1048 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def node1048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1049 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node1049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1050 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node1050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1051 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def node1051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1053 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node1053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1054 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node1054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1055 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def node1055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node1056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1057 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1058 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1059 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node1059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1060 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node1060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1061 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node1061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1062 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def node1062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1063 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node1063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1064 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def node1064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node1065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1066 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node1066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1067 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def node1067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1068 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def node1068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1069 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![4, -4, 0]]
def node1069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1070 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node1070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1071 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node1071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1072 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def node1072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1073 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1074 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node1074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1075 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node1075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1076 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def node1076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1077 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def node1077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1078 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node1078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1079 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1080 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1081 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1082 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1083 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1084 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node1084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1085 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def node1085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1086 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1087 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1088 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def node1088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1089 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def node1089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1090 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def node1090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1091 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def node1091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1092 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def node1092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1093 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def node1093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1094 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def node1094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1095 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def node1095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1096 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def node1096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1098 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1099 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1101 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node1101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1102 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node1102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1103 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def node1103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1104 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def node1104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node1107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node1108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1109 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def node1109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1110 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def node1110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node1111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node1112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node1113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node1114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1115 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def node1115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node1116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node1117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1118 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def node1118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1119 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node1119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1120 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node1120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1121 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node1121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1123 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def node1123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1124 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node1124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1128 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1131 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1132 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node1132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1133 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node1133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1134 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1136 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1136Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1137 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node1137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1138 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1139 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1139Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1140 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def node1140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1141 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node1141Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1142 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def node1142Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1143 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def node1143Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1144 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def node1144Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1145 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def node1145Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1146 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def node1146Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1147Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1148Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1149Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1150Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1151Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1152Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1153 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def node1153Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1154 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def node1154Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1155 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def node1155Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1156Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1157 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def node1157Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1158Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1159 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def node1159Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1160 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node1160Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1161Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1162Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1163 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node1163Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1164Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1165 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node1165Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1166 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node1166Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1167 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node1167Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1168 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def node1168Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node1169Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1170 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node1170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1171 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node1171Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1172 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node1172Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1173 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def node1173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1174 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def node1174Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1175 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def node1175Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1176 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def node1176Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1177 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def node1177Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1178Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1179 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node1179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1180Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1181 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node1181Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1182 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node1182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1183Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1184 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1184Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1185 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1185Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1186 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def node1186Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1187Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1188 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1188Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1189 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1189Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1190 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def node1190Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1191 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def node1191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1192 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def node1192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1193 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def node1193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node1194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node1195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node1196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1199 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def node1199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1202 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def node1202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1203 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def node1203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1204 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node1204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1205 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node1205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node1206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node1207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node1208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1209 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def node1209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node1210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1211 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node1211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node1214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1215 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node1215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1217 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node1217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1218 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node1218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1219 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node1219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1220 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node1220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1221 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def node1221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1224 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node1224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1225 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node1225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1226 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node1226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1227 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def node1227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1229 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node1229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1230 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node1230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1231 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def node1231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node1232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1234 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1236 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1236Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1237 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1237Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1238 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node1238Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1239 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def node1239Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1240 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1241 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1241Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1242 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def node1242Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1243 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def node1243Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1244 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def node1244Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1245 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def node1245Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1246 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node1246Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def node1247Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def node1248Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1249 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def node1249Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def node1250Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1251 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node1251Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1252 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def node1252Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1253 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def node1253Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1254 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node1254Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1255 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def node1255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1256Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1257 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def node1257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1258 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def node1258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node1259Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1260Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1261 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node1261Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1262 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node1262Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1263 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def node1263Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1264 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node1264Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node1265Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1266 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1266Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1267 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1268 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def node1268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1269 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node1269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1270 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node1270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1271 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node1271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1272 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def node1272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1273 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node1273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1274 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node1274Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1275 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def node1275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node1276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1277 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def node1277Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1278 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def node1278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1279 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def node1279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node128 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node128Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node129 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def node129Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node130 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node130Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node131 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def node131Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node132 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def node132Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node133 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def node133Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node134 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def node134Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node135 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def node135Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node136 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def node136Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node137 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def node137Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node138 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node138Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node139 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node139Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node140 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def node140Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node141Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node142 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node142Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node143 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def node143Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node144 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node144Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node145 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node145Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node146 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def node146Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node147 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def node147Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node148 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def node148Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node149 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node149Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node150 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node150Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node151 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node151Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node152 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node152Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node153 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node153Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node154 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def node154Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node155 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node155Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node156 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node156Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node157 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node157Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node158 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def node158Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node159 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def node159Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node160 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def node160Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node161 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def node161Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node162 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def node162Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node163Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node164Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node165Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node166Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node167Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node168 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node168Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node169 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node169Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node170 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node170Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node171Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node172Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node173 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node173Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node174Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node175 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node175Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node176 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node176Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node177 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node177Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node178 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node178Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node179Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node180 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node180Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node181 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node181Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node182 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node182Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node183 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node183Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node184 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node184Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node185 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def node185Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node186 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def node186Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node187 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def node187Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node188 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def node188Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node189Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node190 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node190Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node191Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1280 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def node1280Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1281 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def node1281Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1282 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, 0, -1], ![3, -4, 1]]
def node1282Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1283 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def node1283Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1284 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node1284Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1285 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![4, -4, 0]]
def node1285Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1286 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1286Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1287 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def node1287Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1288 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def node1288Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1289 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![3, 1, -4]]
def node1289Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1290 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node1290Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1291 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1291Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1292 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node1292Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1293 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1293Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1294 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node1294Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1295 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node1295Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1296 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def node1296Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1297 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def node1297Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1298 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node1298Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1299 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1300 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1301 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1301Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1302 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node1302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1303 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def node1303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1304 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def node1304Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1305 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1306 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node1306Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1307 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def node1307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1308 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def node1308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1309 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def node1309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1310 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def node1310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1311 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def node1311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1312 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def node1312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1313 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def node1313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1315 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1317 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1318 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1320 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1321 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1322 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1323 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def node1323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1324 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def node1324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1325 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def node1325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1332 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def node1332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1333 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def node1333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1334 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def node1334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1336 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def node1336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1337 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def node1337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1338 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node1338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1340 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node1340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1342 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node1342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1343 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node1343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1344 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node1344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node1345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1346 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node1346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1347 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node1347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1348 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def node1348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1349 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def node1349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1351 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1352 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![3, 0, -3]]
def node1352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1353 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![2, 0, -2], ![2, 0, -2]]
def node1353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1355 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def node1355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1356 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node1356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1359 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node1359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1361 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node1361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1362 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node1362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1363 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node1363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1365 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1367 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1368 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1369 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def node1369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1370 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1371 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1372 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def node1372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1373 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def node1373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1374 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def node1374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1375 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def node1375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def node1376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node1377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node1378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node1379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node1380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node1381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1385 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def node1385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1388 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def node1388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1389 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def node1389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1390 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def node1390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1391 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node1391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node1392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node1393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1394 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node1394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1397 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node1397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node1398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1399 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node1399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1400 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node1400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1401 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node1401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1402 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def node1402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1404 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node1404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1406 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node1406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1407 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node1407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1408 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def node1408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1410 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1411 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1412 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node1412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1413 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def node1413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1414 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1415 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node1415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1416 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def node1416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1417 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def node1417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1418 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def node1418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1419 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def node1419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1420 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def node1420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1422 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def node1422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1423 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def node1423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1424 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![3, -1, -2]]
def node1424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1425 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def node1425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1426 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def node1426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1427 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def node1427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1428 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node1428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1429 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def node1429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1430 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def node1430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1431 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node1431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1432 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![4, -4, 0]]
def node1432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1433 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1434 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, -1, 0], ![2, 1, -3]]
def node1434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1435 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1436 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def node1436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1437 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def node1437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1438 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def node1438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1439 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node1439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1440 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def node1440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1441 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1442 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node1442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1443 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node1443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1444 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def node1444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1445 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def node1445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1446 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node1446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1447 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1448 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1449 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def node1449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1450 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![3, -2, -1]]
def node1450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1451 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node1451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1452 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def node1452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1453 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def node1453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1454 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def node1454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1455 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def node1455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1456 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 3, 1], ![4, -3, -1]]
def node1456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1458 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1459 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![3, 0, -3]]
def node1459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1460 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1461 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, 0, -1], ![3, -1, -2]]
def node1461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1462 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![2, -1, -1], ![2, 0, -2]]
def node1462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1465 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def node1465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1466 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node1466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1468 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1469 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def node1469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1470 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1471 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def node1471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1472 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def node1472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1473 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def node1473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def node1474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1476 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def node1476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1478 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def node1478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1479 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def node1479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1480 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node1480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1481 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def node1481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1482 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1483 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1484 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def node1484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1485 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, 0, -1], ![3, -3, 0]]
def node1485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1486 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def node1486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1487 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![3, -2, -1]]
def node1487Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1489 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node1489Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1490 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node1490Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1492 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node1492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1493 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node1493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1494 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def node1494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1495 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def node1495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1496 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def node1496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1498 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1499 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def node1499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1500 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def node1500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node1501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node1502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1503 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def node1503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1505 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node1505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1507 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node1507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1508 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node1508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1509 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def node1509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1511 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node1511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1512 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node1512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1513 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def node1513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1514 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node1514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1515 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node1515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1516 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def node1516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1517 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1518 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def node1518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1519 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node1519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1520 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def node1520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1521 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def node1521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1522 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1523 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def node1523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1524 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1525 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node1525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1526 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def node1526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1527 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def node1527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1528 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1529 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def node1529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1530 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def node1530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1531 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def node1531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1532 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def node1532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1533 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def node1533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1534 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def node1534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1535 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node1535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1536 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node1536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1537 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def node1537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1538 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def node1538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1539 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def node1539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1540 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def node1540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1541 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def node1541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1543 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1544 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1546 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node1546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1547 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node1547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1548 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, -1, -1], ![3, 0, -3]]
def node1548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1549 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, 0, -2], ![3, -1, -2]]
def node1549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node1550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node1551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node1552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1555 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def node1555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1557 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node1557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1558 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def node1558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1559 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def node1559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1560 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node1560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1562 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def node1562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1564 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def node1564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1565 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def node1565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node1566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node1567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1568 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def node1568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1569 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def node1569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1570 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def node1570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1571 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node1571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1572 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node1572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1573 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def node1573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1574 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![3, 1, -4]]
def node1574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1575 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def node1575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1576 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![3, 0, -3]]
def node1576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1577 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 2, -3], ![3, -1, -2]]
def node1577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1578 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, -1, -1], ![2, 2, -4]]
def node1578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1579 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, 0, -2], ![2, 1, -3]]
def node1579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1580Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node1582Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node1583Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1584 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def node1584Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1585 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def node1585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node1586Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node1587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node1588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node1589Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1590 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def node1590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1591 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node1591Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node1592Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node1593Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node1594Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node1595Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1597Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1598Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1599 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node1599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1600Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1601Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1602 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node1602Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1603 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node1603Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1604 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node1604Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1605 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node1605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1606Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1607Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1608 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node1608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1609Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1610 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node1610Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1611 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node1611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1612 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node1612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node1613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node1614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1615 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node1615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1616Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1617 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1618 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1619 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node1619Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1620 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def node1620Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1621Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1622 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1622Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1623 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1623Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1624 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node1624Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1625 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1625Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1626 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node1626Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1627 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def node1627Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1628 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def node1628Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1629 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def node1629Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1630 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def node1630Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1631 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1631Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1632Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1633 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def node1633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1634 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node1634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1637 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node1637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1639 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node1639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1640 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node1640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1641 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node1641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1643 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1645 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1646 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1647 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def node1647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1648 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1649 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1650 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def node1650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1651 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def node1651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1652 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -2, 0], ![2, 1, -3]]
def node1652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1653 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def node1653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1655 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1656 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1657 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def node1657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1658 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1658Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1659 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def node1659Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1660 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -2, 0], ![2, 0, -2]]
def node1660Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1661 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -1, -1], ![2, -1, -1]]
def node1661Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def node1662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node1663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node1664Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node1665Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1666 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def node1666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node1667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node1668Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1669 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def node1669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node1670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node1671Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1672 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def node1672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1674 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def node1674Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1675 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node1675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1676 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def node1676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1677 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def node1677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1679 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def node1679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1681 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node1681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1682 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def node1682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1683 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def node1683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1685 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def node1685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1686 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def node1686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1687 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def node1687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1688 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def node1688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1689 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def node1689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1690 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node1690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1691 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node1691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1692 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def node1692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1693 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def node1693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1694 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def node1694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1695 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def node1695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def node1696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node1697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node1698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node1699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1700 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node1700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node1701Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1702 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def node1702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node1703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1704 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def node1704Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node1705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1707 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node1707Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1708 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node1708Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1709 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node1709Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1710 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def node1710Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node1711Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1712 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node1712Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node1713Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1714 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node1714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1715 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node1715Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1716 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def node1716Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node1717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1718 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def node1718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1719 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![3, -3, 0]]
def node1719Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1720 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def node1720Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1721 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node1721Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1722 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def node1722Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1723 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node1723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1724 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1725 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node1725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1726 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1727 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node1727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1728 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node1728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1729 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def node1729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1730 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def node1730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node1731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node1732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1733 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![3, -3, 0]]
def node1733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1734 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node1734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1735 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def node1735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1736 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node1736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1737 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1738 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node1738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1739 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node1739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1740 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def node1740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1741 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def node1741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1742 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node1742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1743 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def node1743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1744 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node1744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1745 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def node1745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1746 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def node1746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1747 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def node1747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1748 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def node1748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1749 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def node1749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1750 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node1750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1751 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node1751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1752 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def node1752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1753 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1754 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def node1754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1755 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def node1755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1756 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def node1756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1757 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def node1757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1758 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -1, 4], ![3, 1, -4]]
def node1758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1765 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def node1765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1766 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node1766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1767 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node1767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1772 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1773 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node1773Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1774 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node1774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1775 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1776Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1777 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node1777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1778 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node1778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1779 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node1779Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1780 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node1780Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1781 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node1781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1782 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node1782Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1783 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def node1783Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1785Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node1786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node1787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1788 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def node1788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node1789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node1790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node1791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node1792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node1793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node1794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1795 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node1795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1796 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node1796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1797 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node1797Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1799 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def node1799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1800 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node1800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1804 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1807 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1808 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node1808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1809 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node1809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1810 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1812 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1813 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node1813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1814 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1815 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1816 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node1816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1817 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def node1817Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1818 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def node1818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1819 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def node1819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1820 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def node1820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1823 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node1823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1825 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node1825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1826 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node1826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1827 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node1827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1828 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node1828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1829 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node1829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1830 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def node1830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1831 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def node1831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1832 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, 0, -2], ![3, -3, 0]]
def node1832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node1833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node1834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node1835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1839 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node1839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1840 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def node1840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1841 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def node1841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1843 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def node1843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1845 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def node1845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1846 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def node1846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node1847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node1848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1849 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def node1849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1850 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def node1850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1851 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def node1851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1852 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node1852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1853 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node1853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1854 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def node1854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1855 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def node1855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1856 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 1, -2], ![3, 0, -3]]
def node1856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1857 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 2, -3], ![3, -1, -2]]
def node1857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1858 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![2, -1, -1], ![2, 2, -4]]
def node1858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1859 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![2, 0, -2], ![2, 1, -3]]
def node1859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node1860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node1861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node1863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node1864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node1866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node1867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node1868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node1869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node1870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node1871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1872 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def node1872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def node1873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1880 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def node1880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1881 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def node1881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def node1882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def node1883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def node1884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def node1885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def node1886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def node1887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def node1888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def node1889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node1890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def node1891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def node1892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1893 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def node1893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1894 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def node1894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1895 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node1895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node1896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node1897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node1898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node1899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node1900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node1901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node1902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node1903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node1904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node1905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node1906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node1910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1911 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node1911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1914 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node1914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1915 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node1915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1916 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def node1916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1917 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node1917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1918 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node1918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node1919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node192 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node192Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node193 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node193Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node194 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node194Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node195 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node195Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node196 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def node196Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node197 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def node197Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node198Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node199Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node200Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node201 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node201Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node202 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node202Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node203 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node203Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node204 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node204Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node205Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node206Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node207Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node208Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node209Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node210Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node211 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def node211Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node212Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node213Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node214 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def node214Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node215Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node216Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node217Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node218Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node219 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node219Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node220Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node221Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node222 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node222Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node223Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node224 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node224Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node225 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node225Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node226 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node226Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node227 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node227Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node228 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node228Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node229 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node229Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node230 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node230Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node231 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node231Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node232Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node233 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node233Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node234 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node234Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node235 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node235Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node236 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def node236Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node237 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def node237Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node238Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node239 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node239Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node240 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node240Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node241 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def node241Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node242Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node243Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node244 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node244Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node245 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node245Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node246 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node246Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node247 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def node247Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node248 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node248Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node249 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def node249Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node250 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def node250Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node251 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def node251Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node252 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def node252Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node253Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node254 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node254Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node255 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def node255Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1920 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def node1920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node1923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1924 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node1924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node1926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1927 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def node1927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1928 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node1928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1929 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node1929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1932 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def node1932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1933 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def node1933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1934 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![2, -2, 0], ![2, -1, -1]]
def node1934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node1935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node1936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1937 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def node1937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1938 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def node1938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1939 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def node1939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node1940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node1941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1942 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node1942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1944 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1944Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1945 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1946 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node1946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1947 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1948 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node1948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1949 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node1949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1950 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def node1950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1951 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def node1951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1952 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -2, 0], ![2, 2, -4]]
def node1952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1953 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -1, -1], ![2, 1, -3]]
def node1953Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def node1954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node1955Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node1956Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node1957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node1958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node1961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node1962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node1965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node1968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1969 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def node1969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1970 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def node1970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1971 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def node1971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node1972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node1973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node1974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node1975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node1976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node1977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1978 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def node1978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1979 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def node1979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1980 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def node1980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node1981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node1982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node1983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1984 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def node1984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node1985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node1986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node1987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node1988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node1989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node1990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node1991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node1992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node1993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node1994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node1995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node1998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node2000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node2001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node2002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2003 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def node2003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2004 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def node2004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2005 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def node2005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2006 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node2006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2007 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node2007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node2008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node2009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node2010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node2011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node2012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def node2013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node2014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node2015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node2016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node2017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2018 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node2018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node2021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2022 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node2022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node2024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2025 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node2025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2026 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node2026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2027 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def node2027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2028 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node2028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2029 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node2029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node2030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node2031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2032 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def node2032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node2033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node2034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2035 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node2035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node2036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2037 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node2037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2038 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def node2038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2039 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node2039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node2040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2041 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def node2041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2042 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def node2042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node2043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node2044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2045 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def node2045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2047 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node2047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2048 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node2048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2049 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def node2049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node2050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2052 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node2052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2053 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2054 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node2054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2055 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node2055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2056 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def node2056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2057 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2058 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2059 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def node2059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2060 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def node2060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2061 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def node2061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2062 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def node2062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2063 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def node2063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2064 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -3, 1], ![2, 2, -4]]
def node2064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2065 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def node2065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2066 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def node2066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2068 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def node2068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node2069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node2070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node2071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node2072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node2073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node2074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node2076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2079 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def node2079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2080 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def node2080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2081 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def node2081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2082 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node2082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node2083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node2084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node2085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node2086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2087 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node2087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node2088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node2089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2090 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node2090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node2091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2092 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node2092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2093 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node2093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2094 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node2094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node2095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2096 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def node2096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2097 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node2097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2099 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node2099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2101 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node2101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2102 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node2102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2103 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def node2103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node2104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2106 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2107 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2108 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node2108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2109 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def node2109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2110 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2111 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node2111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2112 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def node2112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2113 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def node2113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2114 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def node2114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2115 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def node2115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2116 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def node2116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2119 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def node2119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2121 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def node2121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2122 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def node2122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2123 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def node2123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node2124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2125 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node2125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2126 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node2126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2128 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node2128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2129 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node2129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2130 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![3, -1, -2]]
def node2130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node2131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2132 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node2132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2133 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node2133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2134 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def node2134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2135 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node2135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2136 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def node2136Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2137 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def node2137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2138 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def node2138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def node2139Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node2140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node2141Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node2142Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2143 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def node2143Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node2144Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node2145Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2146 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def node2146Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node2147Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node2148Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2149 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def node2149Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2150Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2151 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def node2151Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2152 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node2152Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2153 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def node2153Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2154Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2155 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def node2155Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2156Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2157 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node2157Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2158 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def node2158Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2159 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def node2159Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2160Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2161 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def node2161Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2162 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def node2162Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2163 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def node2163Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2164 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def node2164Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2165 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node2165Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2166 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node2166Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2167 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def node2167Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2168 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def node2168Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2169 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def node2169Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def node2170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def node2171Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def node2172Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def node2173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node2174Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def node2175Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def node2176Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node2177Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def node2178Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def node2179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2180 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def node2180Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def node2181Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node2182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node2183Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2184 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def node2184Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2185 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def node2185Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2186 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def node2186Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node2187Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def node2188Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def node2189Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node2190Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node2191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node2192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2193 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def node2193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node2194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node2195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node2196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2197 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def node2197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def node2198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node2199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2200 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def node2200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node2201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2203 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node2203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2205 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node2205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2206 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node2206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2207 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def node2207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2208 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def node2208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node2209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2210 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![3, -3, 0]]
def node2210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node2211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2212 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def node2212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node2213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2215 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node2215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2216 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node2216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2217 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def node2217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2218 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def node2218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node2219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2220 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def node2220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2221 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def node2221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2222 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def node2222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2223 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def node2223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2224 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node2224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2225 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node2225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2226 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def node2226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2227 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2228 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def node2228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2229 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def node2229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2230 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def node2230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def node2231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node2232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node2233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def node2234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2235 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def node2235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def node2236Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def node2237Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def node2238Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2239 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def node2239Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node2240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node2241Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2242 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node2242Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node2243Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2244 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node2244Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2245 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node2245Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2246 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def node2246Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2247 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node2247Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def node2248Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2249 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def node2249Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node2250Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2251 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def node2251Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node2252Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2253 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node2253Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2254 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def node2254Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2255 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def node2255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2256 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def node2256Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2257 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def node2257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2258 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def node2258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2259 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def node2259Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2260 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node2260Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2261 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def node2261Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2262 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node2262Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2263 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2263Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2264 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node2264Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2265 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node2265Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2266 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node2266Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2267 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def node2267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2268 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def node2268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def node2269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2270 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def node2270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2271 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def node2271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2272 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def node2272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2273 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def node2273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2274 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node2274Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2275 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node2275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2276 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node2276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2277 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node2277Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2278 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node2278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2279 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node2279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2280 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def node2280Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2281 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def node2281Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2282 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def node2282Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2283 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node2283Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2284 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def node2284Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2285 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def node2285Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2286 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def node2286Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2287 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def node2287Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2288 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node2288Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2289 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def node2289Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2290 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node2290Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2291 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2291Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2292 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def node2292Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2293 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def node2293Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2294 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def node2294Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node2295Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node2296Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node2297Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node2298Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node2299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2300 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node2300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2301 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node2301Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node2302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node2303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2304Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node2305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2306 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node2306Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2307 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node2307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2309 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node2309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2310 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node2310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2311 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node2311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2312 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node2312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2313 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node2313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2314 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node2314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2315 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def node2315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node2316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node2317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node2318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node2319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node2320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node2321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node2322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node2323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node2324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2325 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node2325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2326 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node2326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2327 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node2327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2329 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node2329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node2331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2334 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node2334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2335 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node2335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2336 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node2336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2337 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node2337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2339 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node2339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2340 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node2340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2341 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node2341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2342 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node2342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2343 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node2343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2344 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def node2344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2345 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def node2345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2346 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def node2346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node2347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node2348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node2349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node2350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node2351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2352 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def node2352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2355 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def node2355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2356 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node2356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2357 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node2357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2358 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node2358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2359 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node2359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2360 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node2360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node2361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2362 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node2362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2363 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def node2363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2365 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node2365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2367 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node2367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2368 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node2368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2369 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![2, 0, -2], ![2, 1, -3]]
def node2369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node2370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node2371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node2372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node2373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node2374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node2375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2376 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node2376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node2377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node2378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node2379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node2380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node2381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2385 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node2385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2386 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node2386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2387 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node2387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2388 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node2388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2391 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node2391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2393 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node2393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2394 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node2394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2395 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node2395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node2396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2397 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node2397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2399 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node2399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2400 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node2400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2401 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node2401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2403 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2404 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node2404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2405 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node2405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2406 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node2406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2407 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def node2407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2408 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def node2408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2409 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -2, 0], ![2, 2, -4]]
def node2409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2410 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def node2410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2411 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def node2411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node2412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node2413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node2414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node2415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node2416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node2417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node2418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node2419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node2420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2421 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def node2421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node2422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node2423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node2424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node2425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node2426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node2427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node2428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node2429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node2430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node2431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node2432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node2433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2434 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def node2434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2435 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def node2435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node2436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node2437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node2438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node2439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node2440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node2441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2442 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def node2442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2443 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def node2443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node2444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node2445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node2446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2447 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def node2447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node2448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node2449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node2450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node2451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node2452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node2453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node2454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node2455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node2456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node2457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node2458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node2459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node2460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node2462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node2463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node2464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2465 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def node2465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2466 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def node2466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2467 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node2467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2468 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node2468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node2469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node2470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node2471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node2472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node2473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def node2474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node2475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node2476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node2477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node2478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node2481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2482 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node2482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node2484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2485 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node2485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2486 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node2486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2487 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def node2487Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2488 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node2488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2489 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node2489Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node2490Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node2491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2492 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def node2492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node2493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node2494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2495 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node2495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node2496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2497 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node2497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2498 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def node2498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2499 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node2499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node2500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node2501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2502 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def node2502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2504 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node2504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2505 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node2505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2506 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def node2506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node2507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2509 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node2509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2511 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2512 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node2512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2513 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node2513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2514 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2515 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2516 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def node2516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2517 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def node2517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2518 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def node2518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2519 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def node2519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2520 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def node2520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2521 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def node2521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2522 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def node2522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2523 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def node2523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def node2524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node2525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node2526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node2527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node2528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node2529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node2530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2531 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def node2531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2532 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def node2532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node2533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node2534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node2535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node2537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2538 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def node2538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2539 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def node2539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node2540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node2541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node2542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node2543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node2544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node2545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node2546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node2547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node2548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node2549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node2550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node2551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node2552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node2554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node2555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2560 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def node2560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def node4230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end


