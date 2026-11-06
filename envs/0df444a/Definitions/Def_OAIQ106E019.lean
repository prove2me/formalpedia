-- Prove2me | Definitions.Def_OAIQ106E019
-- name    : OAIQ106E019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:24:15.330207+00:00
-- url     : https://prove2.me/theorems/2d05f732-f645-461c-9e21-0f14c930b3ad
-- title:
--   Definitions bundle OAIQ106E019 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 117 declarations of OpenAI's Lean: 117 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block1.rows15_0`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_10`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_11`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_12`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_13`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_14`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_15`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_3`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_4`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_5`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_6`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_7`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_8`, `OAI.MUB6.Certificate.GramEntries.Block1.rows15_9`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_13`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_14`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_15`, `OAI.MUB6.Certificate.GramEntries.Block1.rows16_16`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_0`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_10`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_11`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_12`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_13`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_14`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_15`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_16`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_17`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_3`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_4`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_5`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_6`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_7`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_8`, `OAI.MUB6.Certificate.GramEntries.Block1.rows17_9`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_13`, `OAI.MUB6.Certificate.GramEntries.Block1.rows18_14` and 77 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block1Row1`, `MutuallyUnbiased_GramEntries_Block1Row15`, `MutuallyUnbiased_GramEntries_Block1Row16`, `MutuallyUnbiased_GramEntries_Block1Row17`, `MutuallyUnbiased_GramEntries_Block1Row18`, `MutuallyUnbiased_GramEntries_Block1Row19`, `MutuallyUnbiased_GramEntries_Block1Row2`, `MutuallyUnbiased_GramEntries_Block1Row20`, `MutuallyUnbiased_GramEntries_Block1Row3`, `MutuallyUnbiased_GramEntries_Block1Row4`, `MutuallyUnbiased_GramEntries_Block1Row5`, `MutuallyUnbiased_GramEntries_Block1Row6`, `MutuallyUnbiased_GramEntries_Block1Row7`.
--
--   **Imports.** It imports the bundles `OAIQ106E015` and `OAIQ106E018` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_9_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval19_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_19_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_20_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval20_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval2_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8_e` and `OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E015
import Definitions.Def_OAIQ106E018

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block1.form1.size → Integer.Sparse Key := ![row660, row661, row662, row663, row664, row665, row666, row667, row668, row669, row670, row671, row672, row673]

def rows1_1 : Fin GramFunctions.Block1.form1.size → Integer.Sparse Key := ![row674, row675, row676, row677, row678, row679, row680, row681, row682, row683, row684, row685, row686, row687]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows15_0 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row700, row701, row702, row703, row704, row705, row3032, row3033, row3034, row712, row713, row714, row715, row716, row717, row3035, row3036, row3037, row3038, row3039, row3040, row3041, row3042, row3043, row3044, row3045, row3046, row3047, row3048, row3049]

def rows15_1 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row730, row731, row732, row733, row734, row735, row3050, row3051, row3052, row742, row743, row744, row745, row746, row747, row3053, row3054, row3055, row3056, row3057, row3058, row3059, row3060, row3061, row3062, row3063, row3064, row3065, row3066, row3067]

def rows15_2 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row760, row761, row762, row763, row764, row765, row3068, row3069, row3070, row772, row773, row774, row775, row776, row777, row3071, row3072, row3073, row3074, row3075, row3076, row3077, row3078, row3079, row3080, row3081, row3082, row3083, row3084, row3085]

def rows15_3 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3086, row3087, row3088, row3089, row3090, row3091, row3092, row3093, row3094, row3095, row3096, row3097, row3098, row3099, row3100, row3101, row3102, row3103, row3104, row3105, row3106, row3107, row3108, row3109, row3110, row3111, row3112, row3113, row3114, row3115]

def rows15_4 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3116, row3117, row3118, row3119, row3120, row3121, row3122, row3123, row3124, row3125, row3126, row3127, row3128, row3129, row3130, row3131, row3132, row3133, row3134, row3135, row3136, row3137, row3138, row3139, row3140, row3141, row3142, row3143, row3144, row3145]

def rows15_5 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3146, row3147, row3148, row3149, row3150, row3151, row3152, row3153, row3154, row3155, row3156, row3157, row3158, row3159, row3160, row3161, row3162, row3163, row3164, row3165, row3166, row3167, row3168, row3169, row3170, row3171, row3172, row3173, row3174, row3175]

def rows15_6 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3176, row3177, row3178, row3179, row3180, row3181, row3182, row3183, row3184, row3185, row3186, row3187, row3188, row3189, row3190, row3191, row3192, row3193, row3194, row3195, row3196, row3197, row3198, row3199, row3200, row3201, row3202, row3203, row3204, row3205]

def rows15_7 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3206, row3207, row3208, row3209, row3210, row3211, row3212, row3213, row3214, row3215, row3216, row3217, row3218, row3219, row3220, row3221, row3222, row3223, row3224, row3225, row3226, row3227, row3228, row3229, row3230, row3231, row3232, row3233, row3234, row3235]

def rows15_8 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3236, row3237, row3238, row3239, row3240, row3241, row3242, row3243, row3244, row3245, row3246, row3247, row3248, row3249, row3250, row3251, row3252, row3253, row3254, row3255, row3256, row3257, row3258, row3259, row3260, row3261, row3262, row3263, row3264, row3265]

def rows15_9 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3266, row3267, row3268, row3269, row3270, row3271, row3272, row3273, row3274, row3275, row3276, row3277, row3278, row3279, row3280, row3281, row3282, row3283, row3284, row3285, row3286, row3287, row3288, row3289, row3290, row3291, row3292, row3293, row3294, row3295]

def rows15_10 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3296, row3297, row3298, row3299, row3300, row3301, row3302, row3303, row3304, row3305, row3306, row3307, row3308, row3309, row3310, row3311, row3312, row3313, row3314, row3315, row3316, row3317, row3318, row3319, row3320, row3321, row3322, row3323, row3324, row3325]

def rows15_11 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3326, row3327, row3328, row3329, row3330, row3331, row3332, row3333, row3334, row3335, row3336, row3337, row3338, row3339, row3340, row3341, row3342, row3343, row3344, row3345, row3346, row3347, row3348, row3349, row3350, row3351, row3352, row3353, row3354, row3355]

def rows15_12 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3356, row3357, row3358, row3359, row3360, row3361, row3362, row3363, row3364, row3365, row3366, row3367, row3368, row3369, row3370, row3371, row3372, row3373, row3374, row3375, row3376, row3377, row3378, row3379, row3380, row3381, row3382, row3383, row3384, row3385]

def rows15_13 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3386, row3387, row3388, row3389, row3390, row3391, row3392, row3393, row3394, row3395, row3396, row3397, row3398, row3399, row3400, row3401, row3402, row3403, row3404, row3405, row3406, row3407, row3408, row3409, row3410, row3411, row3412, row3413, row3414, row3415]

def rows15_14 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3416, row3417, row3418, row3419, row3420, row3421, row3422, row3423, row3424, row3425, row3426, row3427, row3428, row3429, row3430, row3431, row3432, row3433, row3434, row3435, row3436, row3437, row3438, row3439, row3440, row3441, row3442, row3443, row3444, row3445]

def rows15_15 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3446, row3447, row3448, row3449, row3450, row3451, row3452, row3453, row3454, row3455, row3456, row3457, row3458, row3459, row3460, row3461, row3462, row3463, row3464, row3465, row3466, row3467, row3468, row3469, row3470, row3471, row3472, row3473, row3474, row3475]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

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

def rows16_13 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row3632, row3633, row3634, row3635, row3636, row3637, row3638, row3639, row3640, row3641, row3642, row3643, row3644, row3645, row3646, row3647, row3648, row3649]

def rows16_14 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row3650, row3651, row3652, row3653, row3654, row3655, row3656, row3657, row3658, row3659, row3660, row3661, row3662, row3663, row3664, row3665, row3666, row3667]

def rows16_15 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row3668, row3669, row3670, row3671, row3672, row3673, row3674, row3675, row3676, row3677, row3678, row3679, row3680, row3681, row3682, row3683, row3684, row3685]

def rows16_16 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row3686, row3687, row3688, row3689, row3690, row3691, row3692, row3693, row3694, row3695, row3696, row3697, row3698, row3699, row3700, row3701, row3702, row3703]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows17_0 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3704, row3705, row3706, row3707, row3708, row3709, row3710, row3711, row3712, row3713, row3714, row3715, row3716, row3717, row3718, row3719, row3720, row3721, row3722, row3723, row3724, row3725, row3726, row3727, row3728, row3729, row3730, row3731, row3732, row3733]

def rows17_1 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3734, row3735, row3736, row3737, row3738, row3739, row3740, row3741, row3742, row3743, row3744, row3745, row3746, row3747, row3748, row3749, row3750, row3751, row3752, row3753, row3754, row3755, row3756, row3757, row3758, row3759, row3760, row3761, row3762, row3763]

def rows17_2 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3764, row3765, row3766, row3767, row3768, row3769, row3770, row3771, row3772, row3773, row3774, row3775, row3776, row3777, row3778, row3779, row3780, row3781, row3782, row3783, row3784, row3785, row3786, row3787, row3788, row3789, row3790, row3791, row3792, row3793]

def rows17_3 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3794, row3795, row3796, row3797, row3798, row3799, row3800, row3801, row3802, row3803, row3804, row3805, row3806, row3807, row3808, row3809, row3810, row3811, row3812, row3813, row3814, row3815, row3816, row3817, row3818, row3819, row3820, row3821, row3822, row3823]

def rows17_4 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3824, row3825, row3826, row3827, row3828, row3829, row3830, row3831, row3832, row3833, row3834, row3835, row3836, row3837, row3838, row3839, row3840, row3841, row3842, row3843, row3844, row3845, row3846, row3847, row3848, row3849, row3850, row3851, row3852, row3853]

def rows17_5 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3854, row3855, row3856, row3857, row3858, row3859, row3860, row3861, row3862, row3863, row3864, row3865, row3866, row3867, row3868, row3869, row3870, row3871, row3872, row3873, row3874, row3875, row3876, row3877, row3878, row3879, row3880, row3881, row3882, row3883]

def rows17_6 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3884, row3885, row3886, row3887, row3888, row3889, row3890, row3891, row3892, row3893, row3894, row3895, row3896, row3897, row3898, row3899, row3900, row3901, row3902, row3903, row3904, row3905, row3906, row3907, row3908, row3909, row3910, row3911, row3912, row3913]

def rows17_7 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3914, row3915, row3916, row3917, row3918, row3919, row3920, row3921, row3922, row3923, row3924, row3925, row3926, row3927, row3928, row3929, row3930, row3931, row3932, row3933, row3934, row3935, row3936, row3937, row3938, row3939, row3940, row3941, row3942, row3943]

def rows17_8 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3944, row3945, row3946, row3947, row3948, row3949, row3950, row3951, row3952, row3953, row3954, row3955, row3956, row3957, row3958, row3959, row3960, row3961, row3962, row3963, row3964, row3965, row3966, row3967, row3968, row3969, row3970, row3971, row3972, row3973]

def rows17_9 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3974, row3975, row3976, row3977, row3978, row3979, row3980, row3981, row3982, row3983, row3984, row3985, row3986, row3987, row3988, row3989, row3990, row3991, row3992, row3993, row3994, row3995, row3996, row3997, row3998, row3999, row4000, row4001, row4002, row4003]

def rows17_10 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4004, row4005, row4006, row4007, row4008, row4009, row4010, row4011, row4012, row4013, row4014, row4015, row4016, row4017, row4018, row4019, row4020, row4021, row4022, row4023, row4024, row4025, row4026, row4027, row4028, row4029, row4030, row4031, row4032, row4033]

def rows17_11 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4034, row4035, row4036, row4037, row4038, row4039, row4040, row4041, row4042, row4043, row4044, row4045, row4046, row4047, row4048, row4049, row4050, row4051, row4052, row4053, row4054, row4055, row4056, row4057, row4058, row4059, row4060, row4061, row4062, row4063]

def rows17_12 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4064, row4065, row4066, row4067, row4068, row4069, row4070, row4071, row4072, row4073, row4074, row4075, row4076, row4077, row4078, row4079, row4080, row4081, row4082, row4083, row4084, row4085, row4086, row4087, row4088, row4089, row4090, row4091, row4092, row4093]

def rows17_13 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4094, row4095, row4096, row4097, row4098, row4099, row4100, row4101, row4102, row4103, row4104, row4105, row4106, row4107, row4108, row4109, row4110, row4111, row4112, row4113, row4114, row4115, row4116, row4117, row4118, row4119, row4120, row4121, row4122, row4123]

def rows17_14 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4124, row4125, row4126, row4127, row4128, row4129, row4130, row4131, row4132, row4133, row4134, row4135, row4136, row4137, row4138, row4139, row4140, row4141, row4142, row4143, row4144, row4145, row4146, row4147, row4148, row4149, row4150, row4151, row4152, row4153]

def rows17_15 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4154, row4155, row4156, row4157, row4158, row4159, row4160, row4161, row4162, row4163, row4164, row4165, row4166, row4167, row4168, row4169, row4170, row4171, row4172, row4173, row4174, row4175, row4176, row4177, row4178, row4179, row4180, row4181, row4182, row4183]

def rows17_16 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4184, row4185, row4186, row4187, row4188, row4189, row4190, row4191, row4192, row4193, row4194, row4195, row4196, row4197, row4198, row4199, row4200, row4201, row4202, row4203, row4204, row4205, row4206, row4207, row4208, row4209, row4210, row4211, row4212, row4213]

def rows17_17 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4214, row4215, row4216, row4217, row4218, row4219, row4220, row4221, row4222, row4223, row4224, row4225, row4226, row4227, row4228, row4229, row4230, row4231, row4232, row4233, row4234, row4235, row4236, row4237, row4238, row4239, row4240, row4241, row4242, row4243]

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

def rows18_13 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4400, row4401, row4402, row4403, row4404, row4405, row3641, row3642, row3643, row4406, row4407, row4408, row4409, row4410, row4411, row4412, row4413, row4414, row4415, row4416, row4417, row3647, row3648, row3649, row4418, row4419, row4420, row4421, row4422, row4423]

def rows18_14 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4424, row4425, row4426, row4427, row4428, row4429, row3659, row3660, row3661, row4430, row4431, row4432, row4433, row4434, row4435, row4436, row4437, row4438, row4439, row4440, row4441, row3665, row3666, row3667, row4442, row4443, row4444, row4445, row4446, row4447]

def rows18_15 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4448, row4449, row4450, row4451, row4452, row4453, row3677, row3678, row3679, row4454, row4455, row4456, row4457, row4458, row4459, row4460, row4461, row4462, row4463, row4464, row4465, row3683, row3684, row3685, row4466, row4467, row4468, row4469, row4470, row4471]

def rows18_16 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4472, row4473, row4474, row4475, row4476, row4477, row3695, row3696, row3697, row4478, row4479, row4480, row4481, row4482, row4483, row4484, row4485, row4486, row4487, row4488, row4489, row3701, row3702, row3703, row4490, row4491, row4492, row4493, row4494, row4495]

def rows18_17 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4496, row4497, row4498, row4499, row4500, row4501, row4502, row4503, row4504, row4505, row4506, row4507, row4508, row4509, row4510, row4511, row4512, row4513, row4514, row4515, row4516, row4517, row4518, row4519, row4520, row4521, row4522, row4523, row4524, row4525]

def rows18_18 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4526, row4527, row4528, row4529, row4530, row4531, row4532, row4533, row4534, row4535, row4536, row4537, row4538, row4539, row4540, row4541, row4542, row4543, row4544, row4545, row4546, row4547, row4548, row4549, row4550, row4551, row4552, row4553, row4554, row4555]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows19_0 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4556, row4557, row4558, row4559, row4560, row4561, row4562, row4563, row4564, row4565, row4566, row4567, row4568, row4569]

def rows19_1 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4570, row4571, row4572, row4573, row4574, row4575, row4576, row4577, row4578, row4579, row4580, row4581, row4582, row4583]

def rows19_2 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4584, row4585, row4586, row4587, row4588, row4589, row4590, row4591, row4592, row4593, row4594, row4595, row4596, row4597]

def rows19_3 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4598, row4599, row4600, row4601, row4602, row4603, row4604, row4605, row4606, row4607, row4608, row4609, row4610, row4611]

def rows19_4 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4612, row4613, row4614, row4615, row4616, row4617, row4618, row4619, row4620, row4621, row4622, row4623, row4624, row4625]

def rows19_5 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4626, row4627, row4628, row4629, row4630, row4631, row4632, row4633, row4634, row4635, row4636, row4637, row4638, row4639]

def rows19_6 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4640, row4641, row4642, row4643, row4644, row4645, row4646, row4647, row4648, row4649, row4650, row4651, row4652, row4653]

def rows19_7 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4654, row4655, row4656, row4657, row4658, row4659, row4660, row4661, row4662, row4663, row4664, row4665, row4666, row4667]

def rows19_8 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4668, row4669, row4670, row4671, row4672, row4673, row4674, row4675, row4676, row4677, row4678, row4679, row4680, row4681]

def rows19_9 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4682, row4683, row4684, row4685, row4686, row4687, row4688, row4689, row4690, row4691, row4692, row4693, row4694, row4695]

def rows19_10 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4696, row4697, row4698, row4699, row4700, row4701, row4702, row4703, row4704, row4705, row4706, row4707, row4708, row4709]

def rows19_11 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4710, row4711, row4712, row4713, row4714, row4715, row4716, row4717, row4718, row4719, row4720, row4721, row4722, row4723]

def rows19_12 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4724, row4725, row4726, row4727, row4728, row4729, row4730, row4731, row4732, row4733, row4734, row4735, row4736, row4737]

def rows19_13 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4738, row4739, row4740, row4741, row4742, row4743, row4744, row4745, row4746, row4747, row4748, row4749, row4750, row4751]

def rows19_14 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4752, row4753, row4754, row4755, row4756, row4757, row4758, row4759, row4760, row4761, row4762, row4763, row4764, row4765]

def rows19_15 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4766, row4767, row4768, row4769, row4770, row4771, row4772, row4773, row4774, row4775, row4776, row4777, row4778, row4779]

def rows19_16 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4780, row4781, row4782, row4783, row4784, row4785, row4786, row4787, row4788, row4789, row4790, row4791, row4792, row4793]

def rows19_17 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4794, row4795, row4796, row4797, row4798, row4799, row4800, row4801, row4802, row4803, row4804, row4805, row4806, row4807]

def rows19_18 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4808, row4809, row4810, row4811, row4812, row4813, row4814, row4815, row4816, row4817, row4818, row4819, row4820, row4821]

def rows19_19 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4822, row4823, row4824, row4825, row4826, row4827, row4828, row4829, row4830, row4831, row4832, row4833, row4834, row4835]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block1.form2.size → Integer.Sparse Key := ![row688, row689, row690, row691, row692, row693, row694, row695, row696, row697, row698, row699, row700, row701, row702, row703, row704, row705, row706, row707, row708, row709, row710, row711, row712, row713, row714, row715, row716, row717]

def rows2_1 : Fin GramFunctions.Block1.form2.size → Integer.Sparse Key := ![row718, row719, row720, row721, row722, row723, row724, row725, row726, row727, row728, row729, row730, row731, row732, row733, row734, row735, row736, row737, row738, row739, row740, row741, row742, row743, row744, row745, row746, row747]

def rows2_2 : Fin GramFunctions.Block1.form2.size → Integer.Sparse Key := ![row748, row749, row750, row751, row752, row753, row754, row755, row756, row757, row758, row759, row760, row761, row762, row763, row764, row765, row766, row767, row768, row769, row770, row771, row772, row773, row774, row775, row776, row777]

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

def rows20_1 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4842, row4843, row4844, row1494, row1495, row1496, row4845, row4846, row4847, row4848, row4849, row4850, row1503, row1504, row1505, row4851, row4852, row4853]

def rows20_2 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4854, row4855, row4856, row1524, row1525, row1526, row4857, row4858, row4859, row4860, row4861, row4862, row1533, row1534, row1535, row4863, row4864, row4865]

def rows20_3 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4866, row4867, row4868, row1554, row1555, row1556, row4869, row4870, row4871, row4872, row4873, row4874, row1563, row1564, row1565, row4875, row4876, row4877]

def rows20_4 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4878, row4879, row4880, row1584, row1585, row1586, row4881, row4882, row4883, row4884, row4885, row4886, row1593, row1594, row1595, row4887, row4888, row4889]

def rows20_5 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4890, row4891, row4892, row1614, row1615, row1616, row4893, row4894, row4895, row4896, row4897, row4898, row1623, row1624, row1625, row4899, row4900, row4901]

def rows20_6 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4902, row4903, row4904, row1644, row1645, row1646, row4905, row4906, row4907, row4908, row4909, row4910, row1653, row1654, row1655, row4911, row4912, row4913]

def rows20_7 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4914, row4915, row4916, row1674, row1675, row1676, row4917, row4918, row4919, row4920, row4921, row4922, row1683, row1684, row1685, row4923, row4924, row4925]

def rows20_8 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4926, row4927, row4928, row1704, row1705, row1706, row4929, row4930, row4931, row4932, row4933, row4934, row1713, row1714, row1715, row4935, row4936, row4937]

def rows20_9 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4938, row4939, row4940, row1734, row1735, row1736, row4941, row4942, row4943, row4944, row4945, row4946, row1743, row1744, row1745, row4947, row4948, row4949]

def rows20_10 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4950, row4951, row4952, row4953, row4954, row4955, row4956, row4957, row4958, row4959, row4960, row4961, row4962, row4963, row4964, row4965, row4966, row4967]

def rows20_11 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4968, row4969, row4970, row4971, row4972, row4973, row4974, row4975, row4976, row4977, row4978, row4979, row4980, row4981, row4982, row4983, row4984, row4985]

def rows20_12 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4986, row4987, row4988, row4989, row4990, row4991, row4992, row4993, row4994, row4995, row4996, row4997, row4998, row4999, row5000, row5001, row5002, row5003]

def rows20_13 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5004, row5005, row5006, row5007, row5008, row5009, row5010, row5011, row5012, row5013, row5014, row5015, row5016, row5017, row5018, row5019, row5020, row5021]

def rows20_14 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5022, row5023, row5024, row5025, row5026, row5027, row5028, row5029, row5030, row5031, row5032, row5033, row5034, row5035, row5036, row5037, row5038, row5039]

def rows20_15 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5040, row5041, row5042, row5043, row5044, row5045, row5046, row5047, row5048, row5049, row5050, row5051, row5052, row5053, row5054, row5055, row5056, row5057]

def rows20_16 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5058, row5059, row5060, row5061, row5062, row5063, row5064, row5065, row5066, row5067, row5068, row5069, row5070, row5071, row5072, row5073, row5074, row5075]

def rows20_17 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5076, row5077, row5078, row5079, row5080, row5081, row5082, row5083, row5084, row5085, row5086, row5087, row5088, row5089, row5090, row5091, row5092, row5093]

def rows20_18 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5094, row5095, row5096, row5097, row5098, row5099, row5100, row5101, row5102, row5103, row5104, row5105, row5106, row5107, row5108, row5109, row5110, row5111]

def rows20_19 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5112, row5113, row5114, row5115, row5116, row5117, row5118, row5119, row5120, row5121, row5122, row5123, row5124, row5125, row5126, row5127, row5128, row5129]

def rows20_20 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5130, row5131, row5132, row5133, row5134, row5135, row5136, row5137, row5138, row5139, row5140, row5141, row5142, row5143, row5144, row5145, row5146, row5147]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block1.form3.size → Integer.Sparse Key := ![row778, row779, row780, row781, row782, row783, row784, row785, row786, row787, row788, row789, row790, row791]

def rows3_1 : Fin GramFunctions.Block1.form3.size → Integer.Sparse Key := ![row792, row793, row794, row795, row796, row797, row798, row799, row800, row801, row802, row803, row804, row805]

def rows3_2 : Fin GramFunctions.Block1.form3.size → Integer.Sparse Key := ![row806, row807, row808, row809, row810, row811, row812, row813, row814, row815, row816, row817, row818, row819]

def rows3_3 : Fin GramFunctions.Block1.form3.size → Integer.Sparse Key := ![row820, row821, row822, row823, row824, row825, row826, row827, row828, row829, row830, row831, row832, row833]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row834, row835, row836, row837, row838, row839, row840, row841, row842, row843, row844, row845, row846, row847]

def rows4_1 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row848, row849, row850, row851, row852, row853, row854, row855, row856, row857, row858, row859, row860, row861]

def rows4_2 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row862, row863, row864, row865, row866, row867, row868, row869, row870, row871, row872, row873, row874, row875]

def rows4_3 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row876, row877, row878, row879, row880, row881, row882, row883, row884, row885, row886, row887, row888, row889]

def rows4_4 : Fin GramFunctions.Block1.form4.size → Integer.Sparse Key := ![row890, row891, row892, row893, row894, row895, row896, row897, row898, row899, row900, row901, row902, row903]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows5_0 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row904, row905, row906, row907, row908, row909, row910, row911, row912, row913, row914, row915, row916, row917, row918, row919, row920, row921, row922, row923, row924, row925, row926, row927, row928, row929, row930, row931, row932, row933]

def rows5_1 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row934, row935, row936, row937, row938, row939, row940, row941, row942, row943, row944, row945, row946, row947, row948, row949, row950, row951, row952, row953, row954, row955, row956, row957, row958, row959, row960, row961, row962, row963]

def rows5_2 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row964, row965, row966, row967, row968, row969, row970, row971, row972, row973, row974, row975, row976, row977, row978, row979, row980, row981, row982, row983, row984, row985, row986, row987, row988, row989, row990, row991, row992, row993]

def rows5_3 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row994, row995, row996, row997, row998, row999, row1000, row1001, row1002, row1003, row1004, row1005, row1006, row1007, row1008, row1009, row1010, row1011, row1012, row1013, row1014, row1015, row1016, row1017, row1018, row1019, row1020, row1021, row1022, row1023]

def rows5_4 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row1024, row1025, row1026, row1027, row1028, row1029, row1030, row1031, row1032, row1033, row1034, row1035, row1036, row1037, row1038, row1039, row1040, row1041, row1042, row1043, row1044, row1045, row1046, row1047, row1048, row1049, row1050, row1051, row1052, row1053]

def rows5_5 : Fin GramFunctions.Block1.form5.size → Integer.Sparse Key := ![row1054, row1055, row1056, row1057, row1058, row1059, row1060, row1061, row1062, row1063, row1064, row1065, row1066, row1067, row1068, row1069, row1070, row1071, row1072, row1073, row1074, row1075, row1076, row1077, row1078, row1079, row1080, row1081, row1082, row1083]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows6_0 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1084, row1085, row1086, row1087, row1088, row1089, row1090, row1091, row1092, row1093, row1094, row1095, row1096, row1097]

def rows6_1 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1098, row1099, row1100, row1101, row1102, row1103, row1104, row1105, row1106, row1107, row1108, row1109, row1110, row1111]

def rows6_2 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1112, row1113, row1114, row1115, row1116, row1117, row1118, row1119, row1120, row1121, row1122, row1123, row1124, row1125]

def rows6_3 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1126, row1127, row1128, row1129, row1130, row1131, row1132, row1133, row1134, row1135, row1136, row1137, row1138, row1139]

def rows6_4 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1140, row1141, row1142, row1143, row1144, row1145, row1146, row1147, row1148, row1149, row1150, row1151, row1152, row1153]

def rows6_5 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1154, row1155, row1156, row1157, row1158, row1159, row1160, row1161, row1162, row1163, row1164, row1165, row1166, row1167]

def rows6_6 : Fin GramFunctions.Block1.form6.size → Integer.Sparse Key := ![row1168, row1169, row1170, row1171, row1172, row1173, row1174, row1175, row1176, row1177, row1178, row1179, row1180, row1181]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_0 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1182, row1183, row1184, row1185, row1186, row1187, row1188, row1189, row1190, row1191, row1192, row1193, row904, row905, row906, row907, row908, row909, row1194, row1195, row1196, row1197, row1198, row1199, row913, row914, row915, row916, row917, row918]

def rows7_1 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1200, row1201, row1202, row1203, row1204, row1205, row1206, row1207, row1208, row1209, row1210, row1211, row934, row935, row936, row937, row938, row939, row1212, row1213, row1214, row1215, row1216, row1217, row943, row944, row945, row946, row947, row948]

def rows7_2 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1218, row1219, row1220, row1221, row1222, row1223, row1224, row1225, row1226, row1227, row1228, row1229, row964, row965, row966, row967, row968, row969, row1230, row1231, row1232, row1233, row1234, row1235, row973, row974, row975, row976, row977, row978]

def rows7_3 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1236, row1237, row1238, row1239, row1240, row1241, row1242, row1243, row1244, row1245, row1246, row1247, row994, row995, row996, row997, row998, row999, row1248, row1249, row1250, row1251, row1252, row1253, row1003, row1004, row1005, row1006, row1007, row1008]

def rows7_4 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1254, row1255, row1256, row1257, row1258, row1259, row1260, row1261, row1262, row1263, row1264, row1265, row1024, row1025, row1026, row1027, row1028, row1029, row1266, row1267, row1268, row1269, row1270, row1271, row1033, row1034, row1035, row1036, row1037, row1038]

def rows7_5 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1272, row1273, row1274, row1275, row1276, row1277, row1278, row1279, row1280, row1281, row1282, row1283, row1054, row1055, row1056, row1057, row1058, row1059, row1284, row1285, row1286, row1287, row1288, row1289, row1063, row1064, row1065, row1066, row1067, row1068]

end MUB6.Certificate.GramEntries.Block1

end OAI
end


