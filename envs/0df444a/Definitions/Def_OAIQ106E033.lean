-- Prove2me | Definitions.Def_OAIQ106E033
-- name    : OAIQ106E033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:50:27.432902+00:00
-- url     : https://prove2.me/theorems/1369af60-2637-4c1d-b283-e73a667a39fb
-- title:
--   Definitions bundle OAIQ106E033 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block3.rows8_3`, `OAI.MUB6.Certificate.GramEntries.Block3.rows8_6`, `OAI.MUB6.Certificate.GramEntries.Block3.rows9_0`, `OAI.MUB6.Certificate.GramEntries.Block3.rows9_1`, `OAI.MUB6.Certificate.GramEntries.Block3.rows9_2`, `OAI.MUB6.Certificate.GramEntries.Block3.rows9_3`, `OAI.MUB6.Certificate.GramEntries.Block3.rows9_4`, `OAI.MUB6.Certificate.GramEntries.Block3.rows9_5`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block3Row8`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row8.lean), [`MutuallyUnbiased_GramEntries_Block3Row9`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row9.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E018`, `OAIQ106E029` and `OAIQ106E032` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8_e` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E029
import Definitions.Def_OAIQ106E032

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows8_3 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8053, row8054, row8055, row8056, row8057, row8058, row8059, row8060, row8061, row8062, row8063, row8064, row8065, row8066, row8067, row8068, row8069, row8070, row8071, row8072, row8073, row8074, row8075, row8076, row8077, row8078, row8079, row8080, row8081, row8082, row8083, row8084, row8085, row8086, row8087, row8088]

def rows8_6 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8161, row8162, row8163, row8164, row8165, row8166, row8167, row8168, row8169, row8170, row8171, row8172, row8173, row8174, row8175, row8176, row8177, row8178, row8179, row8180, row8181, row8182, row8183, row8184, row8185, row8186, row8187, row8188, row8189, row8190, row8191, row8192, row8193, row8194, row8195, row8196]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_0 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7586, row7587, row7588, row7589, row7590, row7591, row7592, row7593, row7594, row7595, row7596, row7597, row7598, row7599, row7600, row7601, row7602, row7603, row7604, row7605, row7606, row7607, row7608, row7609, row8269, row8270, row8271, row8272, row8273, row8274, row8275, row8276, row8277, row8278, row8279, row8280]

def rows9_1 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7622, row7623, row7624, row7625, row7626, row7627, row7628, row7629, row7630, row7631, row7632, row7633, row7634, row7635, row7636, row7637, row7638, row7639, row7640, row7641, row7642, row7643, row7644, row7645, row8281, row8282, row8283, row8284, row8285, row8286, row8287, row8288, row8289, row8290, row8291, row8292]

def rows9_2 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7658, row7659, row7660, row7661, row7662, row7663, row7664, row7665, row7666, row7667, row7668, row7669, row7670, row7671, row7672, row7673, row7674, row7675, row7676, row7677, row7678, row7679, row7680, row7681, row8293, row8294, row8295, row8296, row8297, row8298, row8299, row8300, row8301, row8302, row8303, row8304]

def rows9_3 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7694, row7695, row7696, row7697, row7698, row7699, row7700, row7701, row7702, row7703, row7704, row7705, row7706, row7707, row7708, row7709, row7710, row7711, row7712, row7713, row7714, row7715, row7716, row7717, row8305, row8306, row8307, row8308, row8309, row8310, row8311, row8312, row8313, row8314, row8315, row8316]

def rows9_4 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7730, row7731, row7732, row7733, row7734, row7735, row7736, row7737, row7738, row7739, row7740, row7741, row7742, row7743, row7744, row7745, row7746, row7747, row7748, row7749, row7750, row7751, row7752, row7753, row8317, row8318, row8319, row8320, row8321, row8322, row8323, row8324, row8325, row8326, row8327, row8328]

def rows9_5 : Fin GramFunctions.Block3.form9.size → Integer.Sparse Key := ![row7766, row7767, row7768, row7769, row7770, row7771, row7772, row7773, row7774, row7775, row7776, row7777, row7778, row7779, row7780, row7781, row7782, row7783, row7784, row7785, row7786, row7787, row7788, row7789, row8329, row8330, row8331, row8332, row8333, row8334, row8335, row8336, row8337, row8338, row8339, row8340]

end MUB6.Certificate.GramEntries.Block3

end OAI
end


