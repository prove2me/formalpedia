-- Prove2me | Definitions.Def_OAIQ106E030
-- name    : OAIQ106E030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:49:57.048002+00:00
-- url     : https://prove2.me/theorems/39d88323-84a7-4fdc-9515-a55605f604bd
-- title:
--   Definitions bundle OAIQ106E030 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 16 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block3.rows17_9`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_0`, `OAI.MUB6.Certificate.GramEntries.Block3.rows18_1`, `OAI.MUB6.Certificate.GramEntries.Block3.rows23_0`, `OAI.MUB6.Certificate.GramEntries.Block3.rows2_0`, `OAI.MUB6.Certificate.GramEntries.Block3.rows2_1`, `OAI.MUB6.Certificate.GramEntries.Block3.rows2_2`, `OAI.MUB6.Certificate.GramEntries.Block3.rows3_0`, `OAI.MUB6.Certificate.GramEntries.Block3.rows3_1`, `OAI.MUB6.Certificate.GramEntries.Block3.rows3_2`, `OAI.MUB6.Certificate.GramEntries.Block3.rows3_3`, `OAI.MUB6.Certificate.GramEntries.Block3.rows4_0`, `OAI.MUB6.Certificate.GramEntries.Block3.rows4_1`, `OAI.MUB6.Certificate.GramEntries.Block3.rows4_2`, `OAI.MUB6.Certificate.GramEntries.Block3.rows4_3`, `OAI.MUB6.Certificate.GramEntries.Block3.rows4_4`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block3Row17`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row17.lean), [`MutuallyUnbiased_GramEntries_Block3Row18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row18.lean), [`MutuallyUnbiased_GramEntries_Block3Row2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row2.lean), [`MutuallyUnbiased_GramEntries_Block3Row23`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row23.lean), [`MutuallyUnbiased_GramEntries_Block3Row3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row3.lean), [`MutuallyUnbiased_GramEntries_Block3Row4`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row4.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E018`, `OAIQ106E025` and `OAIQ106E029` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block3.entryEval17_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3_e` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E025
import Definitions.Def_OAIQ106E029

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows17_9 : Fin GramFunctions.Block3.form17.size → Integer.Sparse Key := ![row9717, row9718, row9719, row9720, row9721, row9722, row9723, row9724, row9725, row9726, row9727, row9728, row9729, row9730, row9731, row9732, row9733, row9734, row9735, row9736, row9737, row9738, row9739, row9740]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows18_0 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row9933, row9934, row9935, row9936, row9937, row9938, row9939, row9940, row9941, row9942, row9943, row9944, row9945, row9946, row9947, row9948, row9949, row9950, row9951, row9952, row9953, row9954, row9955, row9956]

def rows18_1 : Fin GramFunctions.Block3.form18.size → Integer.Sparse Key := ![row9957, row9958, row9959, row9960, row9961, row9962, row9963, row9964, row9965, row9966, row9967, row9968, row9969, row9970, row9971, row9972, row9973, row9974, row9975, row9976, row9977, row9978, row9979, row9980]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block3.form2.size → Integer.Sparse Key := ![row7382, row7383, row7384, row7385, row7386, row7387, row7388, row7389, row7390, row7391, row7392, row7393, row7394, row7395, row7396, row7397]

def rows2_1 : Fin GramFunctions.Block3.form2.size → Integer.Sparse Key := ![row7398, row7399, row7400, row7401, row7402, row7403, row7404, row7405, row7406, row7407, row7408, row7409, row7410, row7411, row7412, row7413]

def rows2_2 : Fin GramFunctions.Block3.form2.size → Integer.Sparse Key := ![row7414, row7415, row7416, row7417, row7418, row7419, row7420, row7421, row7422, row7423, row7424, row7425, row7426, row7427, row7428, row7429]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows23_0 : Fin GramFunctions.Block3.form23.size → Integer.Sparse Key := ![row11786, row11787, row11788, row11789, row11790, row11791, row7348, row7349, row7350, row7351, row7352, row7353, row7354, row7355, row7356, row7357, row7358, row7359]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block3.form3.size → Integer.Sparse Key := ![row7430, row7431, row7432, row7433, row7434, row7435, row7436, row7437, row7438, row7439, row7440, row7441, row7442, row7443, row7444, row7445]

def rows3_1 : Fin GramFunctions.Block3.form3.size → Integer.Sparse Key := ![row7446, row7447, row7448, row7449, row7450, row7451, row7452, row7453, row7454, row7455, row7456, row7457, row7458, row7459, row7460, row7461]

def rows3_2 : Fin GramFunctions.Block3.form3.size → Integer.Sparse Key := ![row7462, row7463, row7464, row7465, row7466, row7467, row7468, row7469, row7470, row7471, row7472, row7473, row7474, row7475, row7476, row7477]

def rows3_3 : Fin GramFunctions.Block3.form3.size → Integer.Sparse Key := ![row7478, row7479, row7480, row7481, row7482, row7483, row7484, row7485, row7486, row7487, row7488, row7489, row7490, row7491, row7492, row7493]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7494, row7495, row7496, row7497, row7498, row7499, row7500, row7501, row7502, row7503, row7504, row7505, row7506, row7507, row7508, row7509]

def rows4_1 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7510, row7511, row7512, row7513, row7514, row7515, row7516, row7517, row7518, row7519, row7520, row7521, row7522, row7523, row7524, row7525]

def rows4_2 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7526, row7527, row7528, row7529, row7530, row7531, row7532, row7533, row7534, row7535, row7536, row7537, row7538, row7539, row7540, row7541]

def rows4_3 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7542, row7543, row7544, row7545, row7546, row7547, row7548, row7549, row7550, row7551, row7552, row7553, row7554, row7555, row7556, row7557]

def rows4_4 : Fin GramFunctions.Block3.form4.size → Integer.Sparse Key := ![row7558, row7559, row7560, row7561, row7562, row7563, row7564, row7565, row7566, row7567, row7568, row7569, row7570, row7571, row7572, row7573]

end MUB6.Certificate.GramEntries.Block3

end OAI
end


