-- Prove2me | Definitions.Def_OAIQ106E020
-- name    : OAIQ106E020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:34:06.566829+00:00
-- url     : https://prove2.me/theorems/e384696c-9577-4248-840e-e6ad81c0a88d
-- title:
--   Definitions bundle OAIQ106E020 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 27 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block1.rows16_0`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_10`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_11`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_12`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_3`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_4`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_5`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_6`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_7`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_8`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_9`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_0`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_10`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_11`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_12`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_3`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_4`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_5`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_6`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_7`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_8`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_9`, `OAI.MUB6.Certificate.GramEntries.Block1.rows20_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block1Row16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row16.lean), [`MutuallyUnbiased_GramEntries_Block1Row18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row18.lean), [`MutuallyUnbiased_GramEntries_Block1Row20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row20.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E013`, `OAIQ106E015` and `OAIQ106E018` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e` and `OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E013
import Definitions.Def_OAIQ106E015
import Definitions.Def_OAIQ106E018

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows16_0 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2086, row2087, row2088, row3476, row3477, row3478, row2095, row2096, row2097, row3479, row3480, row3481, row3482, row3483, row3484, row3485, row3486, row3487]

def rows16_1 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2116, row2117, row2118, row3488, row3489, row3490, row2125, row2126, row2127, row3491, row3492, row3493, row3494, row3495, row3496, row3497, row3498, row3499]

def rows16_2 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2146, row2147, row2148, row3500, row3501, row3502, row2155, row2156, row2157, row3503, row3504, row3505, row3506, row3507, row3508, row3509, row3510, row3511]

def rows16_3 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2176, row2177, row2178, row3512, row3513, row3514, row2185, row2186, row2187, row3515, row3516, row3517, row3518, row3519, row3520, row3521, row3522, row3523]

def rows16_4 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2206, row2207, row2208, row3524, row3525, row3526, row2215, row2216, row2217, row3527, row3528, row3529, row3530, row3531, row3532, row3533, row3534, row3535]

def rows16_5 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2236, row2237, row2238, row3536, row3537, row3538, row2245, row2246, row2247, row3539, row3540, row3541, row3542, row3543, row3544, row3545, row3546, row3547]

def rows16_6 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2266, row2267, row2268, row3548, row3549, row3550, row2275, row2276, row2277, row3551, row3552, row3553, row3554, row3555, row3556, row3557, row3558, row3559]

def rows16_7 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2296, row2297, row2298, row3560, row3561, row3562, row2305, row2306, row2307, row3563, row3564, row3565, row3566, row3567, row3568, row3569, row3570, row3571]

def rows16_8 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2326, row2327, row2328, row3572, row3573, row3574, row2335, row2336, row2337, row3575, row3576, row3577, row3578, row3579, row3580, row3581, row3582, row3583]

def rows16_9 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2356, row2357, row2358, row3584, row3585, row3586, row2365, row2366, row2367, row3587, row3588, row3589, row3590, row3591, row3592, row3593, row3594, row3595]

def rows16_10 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2386, row2387, row2388, row3596, row3597, row3598, row2395, row2396, row2397, row3599, row3600, row3601, row3602, row3603, row3604, row3605, row3606, row3607]

def rows16_11 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2416, row2417, row2418, row3608, row3609, row3610, row2425, row2426, row2427, row3611, row3612, row3613, row3614, row3615, row3616, row3617, row3618, row3619]

def rows16_12 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2446, row2447, row2448, row3620, row3621, row3622, row2455, row2456, row2457, row3623, row3624, row3625, row3626, row3627, row3628, row3629, row3630, row3631]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows18_0 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2098, row2099, row2100, row2101, row2102, row2103, row3479, row3480, row3481, row2110, row2111, row2112, row2113, row2114, row2115, row4244, row4245, row4246, row4247, row4248, row4249, row3485, row3486, row3487, row4250, row4251, row4252, row4253, row4254, row4255]

def rows18_1 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2128, row2129, row2130, row2131, row2132, row2133, row3491, row3492, row3493, row2140, row2141, row2142, row2143, row2144, row2145, row4256, row4257, row4258, row4259, row4260, row4261, row3497, row3498, row3499, row4262, row4263, row4264, row4265, row4266, row4267]

def rows18_2 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2158, row2159, row2160, row2161, row2162, row2163, row3503, row3504, row3505, row2170, row2171, row2172, row2173, row2174, row2175, row4268, row4269, row4270, row4271, row4272, row4273, row3509, row3510, row3511, row4274, row4275, row4276, row4277, row4278, row4279]

def rows18_3 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2188, row2189, row2190, row2191, row2192, row2193, row3515, row3516, row3517, row2200, row2201, row2202, row2203, row2204, row2205, row4280, row4281, row4282, row4283, row4284, row4285, row3521, row3522, row3523, row4286, row4287, row4288, row4289, row4290, row4291]

def rows18_4 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2218, row2219, row2220, row2221, row2222, row2223, row3527, row3528, row3529, row2230, row2231, row2232, row2233, row2234, row2235, row4292, row4293, row4294, row4295, row4296, row4297, row3533, row3534, row3535, row4298, row4299, row4300, row4301, row4302, row4303]

def rows18_5 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2248, row2249, row2250, row2251, row2252, row2253, row3539, row3540, row3541, row2260, row2261, row2262, row2263, row2264, row2265, row4304, row4305, row4306, row4307, row4308, row4309, row3545, row3546, row3547, row4310, row4311, row4312, row4313, row4314, row4315]

def rows18_6 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2278, row2279, row2280, row2281, row2282, row2283, row3551, row3552, row3553, row2290, row2291, row2292, row2293, row2294, row2295, row4316, row4317, row4318, row4319, row4320, row4321, row3557, row3558, row3559, row4322, row4323, row4324, row4325, row4326, row4327]

def rows18_7 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2308, row2309, row2310, row2311, row2312, row2313, row3563, row3564, row3565, row2320, row2321, row2322, row2323, row2324, row2325, row4328, row4329, row4330, row4331, row4332, row4333, row3569, row3570, row3571, row4334, row4335, row4336, row4337, row4338, row4339]

def rows18_8 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2338, row2339, row2340, row2341, row2342, row2343, row3575, row3576, row3577, row2350, row2351, row2352, row2353, row2354, row2355, row4340, row4341, row4342, row4343, row4344, row4345, row3581, row3582, row3583, row4346, row4347, row4348, row4349, row4350, row4351]

def rows18_9 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2368, row2369, row2370, row2371, row2372, row2373, row3587, row3588, row3589, row2380, row2381, row2382, row2383, row2384, row2385, row4352, row4353, row4354, row4355, row4356, row4357, row3593, row3594, row3595, row4358, row4359, row4360, row4361, row4362, row4363]

def rows18_10 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2398, row2399, row2400, row2401, row2402, row2403, row3599, row3600, row3601, row2410, row2411, row2412, row2413, row2414, row2415, row4364, row4365, row4366, row4367, row4368, row4369, row3605, row3606, row3607, row4370, row4371, row4372, row4373, row4374, row4375]

def rows18_11 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2428, row2429, row2430, row2431, row2432, row2433, row3611, row3612, row3613, row2440, row2441, row2442, row2443, row2444, row2445, row4376, row4377, row4378, row4379, row4380, row4381, row3617, row3618, row3619, row4382, row4383, row4384, row4385, row4386, row4387]

def rows18_12 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2458, row2459, row2460, row2461, row2462, row2463, row3623, row3624, row3625, row2470, row2471, row2472, row2473, row2474, row2475, row4388, row4389, row4390, row4391, row4392, row4393, row3629, row3630, row3631, row4394, row4395, row4396, row4397, row4398, row4399]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows20_0 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4836, row4837, row4838, row1476, row1477, row1478, row4839, row4840, row4841, row630, row631, row632, row1485, row1486, row1487, row639, row640, row641]

end MUB6.Certificate.GramEntries.Block1

end OAI
end


