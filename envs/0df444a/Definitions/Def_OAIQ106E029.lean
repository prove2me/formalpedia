-- Prove2me | Definitions.Def_OAIQ106E029
-- name    : OAIQ106E029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:51:37.08019+00:00
-- url     : https://prove2.me/theorems/fb7fdcf1-f7b4-40a3-b2df-27edb096854b
-- title:
--   Definitions bundle OAIQ106E029 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3889 declarations of OpenAI's Lean: 3889 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.row10000`, `OAI.MUB6.Certificate.GramRows.row10001`, `OAI.MUB6.Certificate.GramRows.row10002`, `OAI.MUB6.Certificate.GramRows.row10003`, `OAI.MUB6.Certificate.GramRows.row10004`, `OAI.MUB6.Certificate.GramRows.row10005`, `OAI.MUB6.Certificate.GramRows.row10006`, `OAI.MUB6.Certificate.GramRows.row10007`, `OAI.MUB6.Certificate.GramRows.row10008`, `OAI.MUB6.Certificate.GramRows.row10009`, `OAI.MUB6.Certificate.GramRows.row10010`, `OAI.MUB6.Certificate.GramRows.row10011`, `OAI.MUB6.Certificate.GramRows.row10012`, `OAI.MUB6.Certificate.GramRows.row10013`, `OAI.MUB6.Certificate.GramRows.row10014`, `OAI.MUB6.Certificate.GramRows.row10015`, `OAI.MUB6.Certificate.GramRows.row10016`, `OAI.MUB6.Certificate.GramRows.row10017`, `OAI.MUB6.Certificate.GramRows.row10018`, `OAI.MUB6.Certificate.GramRows.row10019`, `OAI.MUB6.Certificate.GramRows.row10020`, `OAI.MUB6.Certificate.GramRows.row10021`, `OAI.MUB6.Certificate.GramRows.row10022`, `OAI.MUB6.Certificate.GramRows.row10023`, `OAI.MUB6.Certificate.GramRows.row10024`, `OAI.MUB6.Certificate.GramRows.row10025`, `OAI.MUB6.Certificate.GramRows.row10026`, `OAI.MUB6.Certificate.GramRows.row10027`, `OAI.MUB6.Certificate.GramRows.row10028`, `OAI.MUB6.Certificate.GramRows.row10029`, `OAI.MUB6.Certificate.GramRows.row10030`, `OAI.MUB6.Certificate.GramRows.row10031`, `OAI.MUB6.Certificate.GramRows.row10032`, `OAI.MUB6.Certificate.GramRows.row10033`, `OAI.MUB6.Certificate.GramRows.row10034`, `OAI.MUB6.Certificate.GramRows.row10035`, `OAI.MUB6.Certificate.GramRows.row10036`, `OAI.MUB6.Certificate.GramRows.row10037`, `OAI.MUB6.Certificate.GramRows.row10038`, `OAI.MUB6.Certificate.GramRows.row10039` and 3849 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block100`, `MutuallyUnbiased_GramRows_Block101`, `MutuallyUnbiased_GramRows_Block102`, `MutuallyUnbiased_GramRows_Block103`, `MutuallyUnbiased_GramRows_Block104`, `MutuallyUnbiased_GramRows_Block105`, `MutuallyUnbiased_GramRows_Block106`, `MutuallyUnbiased_GramRows_Block107`, `MutuallyUnbiased_GramRows_Block108`, `MutuallyUnbiased_GramRows_Block109`, `MutuallyUnbiased_GramRows_Block110`, `MutuallyUnbiased_GramRows_Block111`, `MutuallyUnbiased_GramRows_Block112`, `MutuallyUnbiased_GramRows_Block113`, `MutuallyUnbiased_GramRows_Block114`, `MutuallyUnbiased_GramRows_Block115`, `MutuallyUnbiased_GramRows_Block116`, `MutuallyUnbiased_GramRows_Block117`, `MutuallyUnbiased_GramRows_Block118`, `MutuallyUnbiased_GramRows_Block119`, `MutuallyUnbiased_GramRows_Block120`, `MutuallyUnbiased_GramRows_Block121`, `MutuallyUnbiased_GramRows_Block122`, `MutuallyUnbiased_GramRows_Block123`, `MutuallyUnbiased_GramRows_Block124`, `MutuallyUnbiased_GramRows_Block125`, `MutuallyUnbiased_GramRows_Block126`, `MutuallyUnbiased_GramRows_Block127`, `MutuallyUnbiased_GramRows_Block81`, `MutuallyUnbiased_GramRows_Block82`, `MutuallyUnbiased_GramRows_Block83`, `MutuallyUnbiased_GramRows_Block84`, `MutuallyUnbiased_GramRows_Block85`, `MutuallyUnbiased_GramRows_Block86`, `MutuallyUnbiased_GramRows_Block87`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E030`, `OAIQ106E031` and `OAIQ106E033`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E000
import Definitions.Def_OAIQ106E002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9739 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

def row9740 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

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

def row9934 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9935 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9936 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9937 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9938 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9939 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9940 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9941 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9942 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9943 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9944 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1175, -4), (key1185, 4), (key1186, -2), (key1222, 4)]

def row9945 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9946 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9947 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9948 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9949 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9950 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9951 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9952 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9953 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9954 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9955 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9956 : Integer.Sparse Key := [(key982, -2), (key988, 2), (key1096, -4), (key1171, -4), (key1175, 2), (key1186, 4), (key1222, -2), (key1224, 4)]

def row9958 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9959 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9960 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9961 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9962 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9963 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9964 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9965 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9966 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9967 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9968 : Integer.Sparse Key := [(key8, 6), (key91, -18), (key152, 12)]

def row9969 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9970 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9971 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9972 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9973 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9974 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9975 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9976 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9977 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9978 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9979 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9980 : Integer.Sparse Key := [(key8, 6), (key91, 12), (key152, -18)]

def row9981 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, 2), (key88, -12), (key92, 4), (key94, -6), (key153, 4), (key156, -6), (key161, 4), (key194, 2), (key203, 4)]

def row9982 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -12), (key92, 4), (key94, -6), (key153, 4), (key156, -6), (key161, 4), (key194, 2), (key203, 4)]

def row9983 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -12), (key92, 4), (key94, -6), (key153, 4), (key156, -6), (key161, 4), (key194, 2), (key203, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9984 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, 2), (key88, -8), (key94, -6), (key153, 4), (key156, -4), (key161, 4), (key203, 4)]

def row9985 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, 2), (key88, -8), (key94, -6), (key153, 2), (key156, -4), (key161, 4), (key165, 2), (key187, 4)]

def row9986 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key14, 2), (key88, -8), (key94, -6), (key153, 2), (key156, -4), (key161, 4), (key165, 2), (key187, 4)]

def row9987 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

def row9988 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

def row9989 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

def row9990 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

def row9991 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

def row9992 : Integer.Sparse Key := [(key5, 2), (key9, 2), (key11, 2), (key88, -10), (key92, 2), (key94, -6), (key153, 2), (key156, -4), (key165, 2), (key167, 4), (key187, 4)]

def row9993 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row9994 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row9995 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row9996 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row9997 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row9998 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row9999 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row10000 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row10001 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row10002 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row10003 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row10004 : Integer.Sparse Key := [(key5, 2), (key11, 4), (key88, 4), (key94, 4), (key156, 4), (key165, -6), (key167, -8), (key187, -4)]

def row10005 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10006 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10007 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10008 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10009 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10010 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10011 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10012 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10013 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10014 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10015 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10016 : Integer.Sparse Key := [(key1002, -4), (key1016, 4), (key1037, 2), (key1072, 4), (key1115, -6), (key1124, 4), (key1151, -8), (key1167, 4)]

def row10017 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10018 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10019 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10020 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10021 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10022 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10023 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10024 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10025 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10026 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10027 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10028 : Integer.Sparse Key := [(key1002, 4), (key1016, -4), (key1037, 4), (key1072, 2), (key1115, 4), (key1124, -8), (key1151, 4), (key1167, -6)]

def row10029 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10030 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10031 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10032 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10033 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10034 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10035 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10036 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10037 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10038 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10039 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10040 : Integer.Sparse Key := [(key981, 4), (key987, 2), (key1095, -8), (key1101, -6), (key1166, 4), (key1173, 4), (key1229, -4), (key1246, 4)]

def row10041 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10042 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10043 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10044 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10045 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10046 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10047 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10048 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10049 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10050 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10051 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10052 : Integer.Sparse Key := [(key981, 2), (key987, 4), (key1095, 4), (key1101, 4), (key1166, -6), (key1173, -8), (key1229, 4), (key1246, -4)]

def row10053 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10054 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10055 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10056 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10057 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10058 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10059 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10060 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10061 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10062 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10063 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10064 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1017, 2), (key1022, 2), (key1038, 2), (key1073, 2), (key1080, 2), (key1116, -4), (key1125, 2), (key1152, -2), (key1159, -4), (key1174, 2), (key1233, -2), (key1236, 2), (key1243, -2), (key1247, 2)]

def row10065 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10066 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10067 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10068 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10069 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10070 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10071 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10072 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10073 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10074 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10075 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10076 : Integer.Sparse Key := [(key1003, 2), (key1009, 2), (key1017, -2), (key1022, -2), (key1038, 2), (key1044, 2), (key1080, 2), (key1116, 2), (key1125, -4), (key1130, -2), (key1159, 2), (key1174, -4), (key1233, 2), (key1236, -2), (key1243, 2), (key1247, -2)]

def row10077 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10078 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10079 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10080 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10081 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10082 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10083 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10084 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10085 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10086 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10087 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10088 : Integer.Sparse Key := [(key980, 6), (key1094, -18), (key1165, 12)]

def row10089 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10090 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10091 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10092 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10093 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10094 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10095 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10096 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10097 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10098 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10099 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10100 : Integer.Sparse Key := [(key980, 6), (key1094, 12), (key1165, -18)]

def row10101 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10102 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10103 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10104 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10105 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10106 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10107 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10108 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10109 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10110 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10111 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10112 : Integer.Sparse Key := [(key1003, 4), (key1009, 2), (key1038, -4), (key1044, -2), (key1125, -4), (key1130, -4), (key1152, 4), (key1159, 4), (key1236, -4), (key1243, 4)]

def row10113 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10114 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10115 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10116 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10117 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10118 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10119 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10120 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10121 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10122 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10123 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10124 : Integer.Sparse Key := [(key1017, 2), (key1022, 4), (key1073, -2), (key1080, -4), (key1125, 4), (key1130, 4), (key1152, -4), (key1159, -4), (key1236, 4), (key1243, -4)]

def row10125 : Integer.Sparse Key := [(key25, 2), (key37, 2), (key40, 2), (key50, 2), (key76, 2), (key81, 2), (key117, 2), (key139, 2), (key162, 2), (key197, 2), (key201, 2), (key204, 2), (key210, -4), (key213, -2), (key430, -4), (key461, -2), (key590, -4), (key592, -4), (key609, -4)]

def row10126 : Integer.Sparse Key := [(key25, 2), (key37, 2), (key40, 2), (key50, 2), (key76, 2), (key81, 2), (key117, 2), (key139, 2), (key162, 2), (key197, 2), (key201, 2), (key204, 2), (key210, -4), (key213, -2), (key430, -4), (key461, -2), (key590, -4), (key592, -4), (key609, -4)]

def row10127 : Integer.Sparse Key := [(key25, 2), (key37, 2), (key40, 2), (key50, 2), (key76, 2), (key81, 2), (key117, 2), (key139, 2), (key162, 2), (key197, 2), (key201, 2), (key204, 2), (key210, -4), (key213, -2), (key430, -4), (key461, -2), (key590, -4), (key592, -4), (key609, -4)]

def row10128 : Integer.Sparse Key := [(key37, 2), (key40, 2), (key76, 2), (key81, 2), (key162, 2), (key204, 2), (key210, -2), (key213, -2), (key379, 2), (key430, -4), (key461, -2), (key464, 2), (key483, 2), (key590, -2), (key592, -4), (key609, -2)]

def row10129 : Integer.Sparse Key := [(key37, 1), (key40, 2), (key76, 1), (key81, 2), (key162, 2), (key210, -2), (key213, -2), (key215, 1), (key379, 2), (key430, -4), (key461, -2), (key464, 2), (key483, 2), (key565, 1), (key590, -2), (key592, -4), (key609, -2), (key615, 2)]

def row10130 : Integer.Sparse Key := [(key37, 1), (key40, 2), (key76, 1), (key81, 2), (key162, 2), (key210, -2), (key213, -2), (key215, 1), (key379, 2), (key430, -4), (key461, -2), (key464, 2), (key483, 2), (key565, 1), (key590, -2), (key592, -4), (key609, -2), (key615, 2)]

def row10131 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

def row10132 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

def row10133 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

def row10134 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

def row10135 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

def row10136 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1), (key210, -3), (key213, -2), (key215, 1), (key217, 2), (key379, 1), (key430, -4), (key461, -2), (key464, 1), (key483, 2), (key565, 1), (key567, 2), (key590, -3), (key592, -4), (key609, -2), (key612, 2), (key615, 2)]

def row10137 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10138 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10139 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10140 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10141 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10142 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10143 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10144 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10145 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10146 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10147 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10148 : Integer.Sparse Key := [(key210, 2), (key213, 2), (key215, -2), (key217, -2), (key379, 2), (key382, 2), (key430, 2), (key461, 2), (key464, -4), (key466, -2), (key483, -2), (key567, 2), (key592, 2), (key609, 2), (key612, -4), (key615, -2)]

def row10149 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10150 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10151 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10152 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10153 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10154 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10155 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10156 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10157 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10158 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10159 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10160 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, 2), (key1022, -2), (key1038, 2), (key1044, -2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -4), (key1152, 2), (key1159, -4), (key1174, -2), (key1236, 2), (key1243, 2), (key1247, 2)]

def row10161 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10162 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10163 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10164 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10165 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10166 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10167 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10168 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10169 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10170 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10171 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10172 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, -4), (key1130, 2), (key1152, -4), (key1159, 2), (key1233, 2), (key1236, 2), (key1243, 2)]

def row10173 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10174 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10175 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10176 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10177 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10178 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10179 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10180 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10181 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10182 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10183 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10184 : Integer.Sparse Key := [(key24, -4), (key36, 4), (key49, 2), (key75, 4), (key106, -6), (key116, 4), (key138, -8), (key154, 4)]

def row10185 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10186 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10187 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10188 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10189 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10190 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10191 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10192 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10193 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10194 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10195 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10196 : Integer.Sparse Key := [(key24, 4), (key36, -4), (key49, 4), (key75, 2), (key106, 4), (key116, -8), (key138, 4), (key154, -6)]

def row10197 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10198 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10199 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10200 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10201 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10202 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10203 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10204 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10205 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10206 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10207 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10208 : Integer.Sparse Key := [(key985, -6), (key1095, 12), (key1170, -12), (key1184, 6)]

def row10209 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10210 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10211 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10212 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10213 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10214 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10215 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10216 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10217 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10218 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10219 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10220 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1170, 12), (key1221, 6)]

def row10221 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10222 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10223 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10224 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10225 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10226 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10227 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10228 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10229 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10230 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10231 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10232 : Integer.Sparse Key := [(key987, -6), (key1095, 12), (key1173, -12), (key1229, 6)]

def row10233 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10234 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10235 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10236 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10237 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10238 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10239 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10240 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10241 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10242 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10243 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10244 : Integer.Sparse Key := [(key981, -6), (key1095, -12), (key1173, 12), (key1246, 6)]

def row10245 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10246 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10247 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10248 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10249 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10250 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10251 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10252 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10253 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10254 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10255 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10256 : Integer.Sparse Key := [(key714, 4), (key718, 2), (key891, -8), (key895, -6), (key916, -4), (key947, 4), (key948, 4), (key955, 4)]

def row10257 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10258 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10259 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10260 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10261 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10262 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10263 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10264 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10265 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10266 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10267 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10268 : Integer.Sparse Key := [(key714, 2), (key718, 4), (key891, 4), (key895, 4), (key916, 4), (key947, -6), (key948, -8), (key955, -4)]

def row10269 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10270 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10271 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10272 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10273 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10274 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10275 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10276 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10277 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10278 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10279 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10280 : Integer.Sparse Key := [(key14, -6), (key88, 12), (key94, 6), (key97, -6), (key156, 6), (key161, -12)]

def row10281 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10282 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10283 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10284 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10285 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10286 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10287 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10288 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10289 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10290 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10291 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10292 : Integer.Sparse Key := [(key9, -6), (key92, -12), (key153, -6), (key165, 6), (key167, 12), (key187, 6)]

def row10293 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10294 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10295 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10296 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10297 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10298 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10299 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10300 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10301 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10302 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10303 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10304 : Integer.Sparse Key := [(key981, 4), (key985, 2), (key1095, -8), (key1099, -6), (key1166, 4), (key1170, 4), (key1184, -4), (key1221, 4)]

def row10305 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10306 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10307 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10308 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10309 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10310 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10311 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10312 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10313 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10314 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10315 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10316 : Integer.Sparse Key := [(key981, 2), (key985, 4), (key1095, 4), (key1099, 4), (key1166, -6), (key1170, -8), (key1184, 4), (key1221, -4)]

def row10317 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10318 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10319 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10320 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10321 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10322 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10323 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10324 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10325 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10326 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10327 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10328 : Integer.Sparse Key := [(key1002, 6), (key1037, -6), (key1124, -12), (key1151, 12)]

def row10329 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10330 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10331 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10332 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10333 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10334 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10335 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10336 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10337 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10338 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10339 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10340 : Integer.Sparse Key := [(key1016, 6), (key1072, -6), (key1124, 12), (key1151, -12)]

def row10341 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10342 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10343 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10344 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10345 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10346 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10347 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10348 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10349 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10350 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10351 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10352 : Integer.Sparse Key := [(key1008, -4), (key1021, 4), (key1039, 2), (key1078, 4), (key1117, -2), (key1157, -4), (key1195, -4), (key1201, 4), (key1216, -4), (key1225, 4)]

def row10353 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10354 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10355 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10356 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10357 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10358 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10359 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10360 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10361 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10362 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10363 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10364 : Integer.Sparse Key := [(key1008, 4), (key1021, -4), (key1043, 4), (key1081, 2), (key1129, -4), (key1176, -2), (key1195, 4), (key1201, -4), (key1216, 4), (key1225, -4)]

def row10365 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

def row10366 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

def row10367 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10368 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 4), (key163, -4), (key170, -2), (key189, 4)]

def row10369 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 4), (key163, -4), (key170, -2), (key189, 4)]

def row10370 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 4), (key163, -4), (key170, -2), (key189, 4)]

def row10371 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

def row10372 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

def row10373 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 2), (key163, -4), (key169, 2), (key170, -2), (key189, 4)]

def row10374 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 2), (key163, -4), (key169, 2), (key170, -2), (key189, 4)]

def row10375 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

def row10376 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

def row10377 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

def row10378 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

def row10379 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

def row10380 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -2), (key163, 4), (key169, -2), (key170, 2), (key189, -2), (key192, 4)]

def row10381 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -2), (key163, 4), (key169, -2), (key170, 2), (key189, -2), (key192, 4)]

def row10382 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -4), (key163, 4), (key170, 2), (key189, -2), (key192, 4)]

def row10383 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -4), (key163, 4), (key170, 2), (key189, -2), (key192, 4)]

def row10384 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -2), (key163, 4), (key169, -2), (key170, 2), (key189, -2), (key192, 4)]

def row10385 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -2), (key163, 4), (key169, -2), (key170, 2), (key189, -2), (key192, 4)]

def row10386 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

def row10387 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

def row10388 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

def row10389 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

def row10390 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

def row10391 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

def row10392 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

def row10393 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

def row10394 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

def row10395 : Integer.Sparse Key := [(key2420, -6), (key2438, 6), (key2495, -6), (key2504, 6)]

def row10396 : Integer.Sparse Key := [(key2420, -6), (key2438, 6), (key2495, -6), (key2504, 6)]

def row10397 : Integer.Sparse Key := [(key2420, -6), (key2438, 6), (key2495, -6), (key2504, 6)]

def row10398 : Integer.Sparse Key := [(key2420, -6), (key2438, 6), (key2495, -6), (key2504, 6)]

def row10399 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

def row10400 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

def row10401 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

def row10402 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

def row10403 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

def row10404 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

def row10405 : Integer.Sparse Key := [(key1045, 18), (key1131, -18)]

def row10406 : Integer.Sparse Key := [(key1045, 18), (key1131, -18)]

def row10407 : Integer.Sparse Key := [(key1045, 18), (key1131, -18)]

def row10408 : Integer.Sparse Key := [(key1045, 18), (key1131, -18)]

def row10409 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

def row10410 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

def row10411 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

def row10412 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

def row10413 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

def row10414 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

def row10415 : Integer.Sparse Key := [(key1050, 6), (key1058, 12), (key1136, -6), (key1138, -12)]

def row10416 : Integer.Sparse Key := [(key1050, 6), (key1058, 12), (key1136, -6), (key1138, -12)]

def row10417 : Integer.Sparse Key := [(key1050, 6), (key1058, 12), (key1136, -6), (key1138, -12)]

def row10418 : Integer.Sparse Key := [(key1050, 6), (key1058, 12), (key1136, -6), (key1138, -12)]

def row10419 : Integer.Sparse Key := [(key2677, -6), (key3045, -2), (key3059, 8), (key3094, -4), (key3122, 4)]

def row10420 : Integer.Sparse Key := [(key2677, -6), (key3045, -2), (key3059, 8), (key3094, -4), (key3122, 4)]

def row10421 : Integer.Sparse Key := [(key2677, -6), (key3045, -2), (key3059, 8), (key3094, -4), (key3122, 4)]

def row10422 : Integer.Sparse Key := [(key2677, -6), (key2811, -6), (key3045, -2), (key3059, 8), (key3094, 2), (key3122, 4)]

def row10423 : Integer.Sparse Key := [(key2677, -6), (key2811, -6), (key3045, -2), (key3059, 8), (key3094, 2), (key3122, 4)]

def row10424 : Integer.Sparse Key := [(key2677, -6), (key2811, -12), (key3045, -2), (key3059, 8), (key3094, 8), (key3122, 4)]

def row10425 : Integer.Sparse Key := [(key2677, 6), (key2708, -16), (key2861, -6), (key3045, 6), (key3059, 4), (key3094, 6)]

def row10426 : Integer.Sparse Key := [(key2677, 6), (key2708, -16), (key2861, -6), (key3045, 6), (key3059, 4), (key3094, 6)]

def row10427 : Integer.Sparse Key := [(key2677, 6), (key2708, -16), (key2811, 2), (key2861, -6), (key3045, 6), (key3059, 4), (key3094, 4)]

def row10428 : Integer.Sparse Key := [(key2677, 6), (key2708, -12), (key2811, 6), (key2861, -6), (key3045, 6)]

def row10429 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

def row10430 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

def row10431 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

def row10432 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

def row10433 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

def row10434 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

def row10435 : Integer.Sparse Key := [(key2416, 6), (key2423, 12), (key2489, -6), (key2491, -12)]

def row10436 : Integer.Sparse Key := [(key2416, 6), (key2423, 12), (key2489, -6), (key2491, -12)]

def row10437 : Integer.Sparse Key := [(key2416, 6), (key2423, 12), (key2489, -6), (key2491, -12)]

def row10438 : Integer.Sparse Key := [(key2416, 6), (key2423, 12), (key2489, -6), (key2491, -12)]

def row10439 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

def row10440 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

def row10441 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

def row10442 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

def row10443 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

def row10444 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

def row10445 : Integer.Sparse Key := [(key2681, 6), (key2688, 6), (key2712, -6), (key2714, -6), (key2817, 6), (key2863, -6)]

def row10446 : Integer.Sparse Key := [(key2681, 6), (key2688, 6), (key2712, -6), (key2714, -6), (key2817, 6), (key2863, -6)]

def row10447 : Integer.Sparse Key := [(key2681, 6), (key2688, 6), (key2712, -6), (key2714, -6), (key2817, 6), (key2863, -6)]

def row10448 : Integer.Sparse Key := [(key2681, 6), (key2688, 6), (key2712, -6), (key2714, -6), (key2817, 6), (key2863, -6)]

def row10449 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

def row10450 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

def row10451 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

def row10452 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

def row10453 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

def row10454 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

def row10455 : Integer.Sparse Key := [(key2412, 6), (key2485, -24), (key3031, 12), (key3118, 6)]

def row10456 : Integer.Sparse Key := [(key2412, 6), (key2485, -24), (key3031, 12), (key3118, 6)]

def row10457 : Integer.Sparse Key := [(key2412, 6), (key2485, -24), (key3031, 12), (key3118, 6)]

def row10458 : Integer.Sparse Key := [(key2412, 6), (key2485, -18), (key3031, 12)]

def row10459 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

def row10460 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

def row10461 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

def row10462 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

def row10463 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

def row10464 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

def row10465 : Integer.Sparse Key := [(key2712, 6), (key2714, 12), (key2815, -6), (key2817, -12)]

def row10466 : Integer.Sparse Key := [(key2712, 6), (key2714, 12), (key2815, -6), (key2817, -12)]

def row10467 : Integer.Sparse Key := [(key2712, 6), (key2714, 12), (key2815, -6), (key2817, -12)]

def row10468 : Integer.Sparse Key := [(key2712, 6), (key2714, 12), (key2815, -6), (key2817, -12)]

def row10469 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

def row10470 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

def row10471 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

def row10472 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

def row10473 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

def row10474 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

def row10475 : Integer.Sparse Key := [(key1407, 6), (key1411, 6), (key1435, -6), (key1436, -6), (key1585, 6), (key1628, -6)]

def row10476 : Integer.Sparse Key := [(key1407, 6), (key1411, 6), (key1435, -6), (key1436, -6), (key1585, 6), (key1628, -6)]

def row10477 : Integer.Sparse Key := [(key1407, 6), (key1411, 6), (key1435, -6), (key1436, -6), (key1585, 6), (key1628, -6)]

def row10478 : Integer.Sparse Key := [(key1407, 6), (key1411, 6), (key1435, -6), (key1436, -6), (key1585, 6), (key1628, -6)]

def row10479 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

def row10480 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

def row10481 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

def row10482 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

def row10483 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

def row10484 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

def row10485 : Integer.Sparse Key := [(key2681, -6), (key2688, 6), (key2712, -6), (key2714, 6), (key2815, -6), (key2817, 6)]

def row10486 : Integer.Sparse Key := [(key2681, -6), (key2688, 6), (key2712, -6), (key2714, 6), (key2815, -6), (key2817, 6)]

def row10487 : Integer.Sparse Key := [(key2681, -6), (key2688, 6), (key2712, -6), (key2714, 6), (key2815, -6), (key2817, 6)]

def row10488 : Integer.Sparse Key := [(key2681, -6), (key2688, 6), (key2712, -6), (key2714, 6), (key2815, -6), (key2817, 6)]

def row10489 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

def row10490 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

def row10491 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

def row10492 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

def row10493 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

def row10494 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

def row10495 : Integer.Sparse Key := [(key1402, 12), (key1430, -12), (key1579, 6), (key1627, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10496 : Integer.Sparse Key := [(key1402, 12), (key1430, -12), (key1579, 6), (key1627, -6)]

def row10497 : Integer.Sparse Key := [(key1402, 12), (key1430, -12), (key1579, 6), (key1627, -6)]

def row10498 : Integer.Sparse Key := [(key1402, 12), (key1430, -12), (key1579, 6), (key1627, -6)]

def row10499 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

def row10500 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

def row10501 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

def row10502 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

def row10503 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

def row10504 : Integer.Sparse Key := [(key2413, 12), (key2490, -12)]

def row10505 : Integer.Sparse Key := [(key2413, -18), (key2490, 18)]

def row10506 : Integer.Sparse Key := [(key2413, -18), (key2490, 18)]

def row10507 : Integer.Sparse Key := [(key2413, -18), (key2490, 18)]

def row10508 : Integer.Sparse Key := [(key2413, -18), (key2490, 18)]

def row10509 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

def row10510 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

def row10511 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

def row10512 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

def row10513 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

def row10514 : Integer.Sparse Key := [(key2416, 12), (key2491, -12)]

def row10515 : Integer.Sparse Key := [(key2416, -18), (key2491, 18)]

def row10516 : Integer.Sparse Key := [(key2416, -18), (key2491, 18)]

def row10517 : Integer.Sparse Key := [(key2416, -18), (key2491, 18)]

def row10518 : Integer.Sparse Key := [(key2416, -18), (key2491, 18)]

def row10519 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

def row10520 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

def row10521 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

def row10522 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

def row10523 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

def row10524 : Integer.Sparse Key := [(key2204, -4), (key2205, -8), (key2319, 4), (key2320, 8)]

def row10525 : Integer.Sparse Key := [(key2204, 6), (key2205, 12), (key2319, -6), (key2320, -12)]

def row10526 : Integer.Sparse Key := [(key2204, 6), (key2205, 12), (key2319, -6), (key2320, -12)]

def row10527 : Integer.Sparse Key := [(key2204, 6), (key2205, 12), (key2319, -6), (key2320, -12)]

def row10528 : Integer.Sparse Key := [(key2204, 6), (key2205, 12), (key2319, -6), (key2320, -12)]

def row10529 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

def row10530 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

def row10531 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

def row10532 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

def row10533 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

def row10534 : Integer.Sparse Key := [(key1050, 12), (key1138, -12)]

def row10535 : Integer.Sparse Key := [(key1050, -18), (key1138, 18)]

def row10536 : Integer.Sparse Key := [(key1050, -18), (key1138, 18)]

def row10537 : Integer.Sparse Key := [(key1050, -18), (key1138, 18)]

def row10538 : Integer.Sparse Key := [(key1050, -18), (key1138, 18)]

def row10539 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

def row10540 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

def row10541 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

def row10542 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

def row10543 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

def row10544 : Integer.Sparse Key := [(key2413, -4), (key2422, -8), (key2486, 4), (key2490, 8)]

def row10545 : Integer.Sparse Key := [(key2413, 6), (key2422, 12), (key2486, -6), (key2490, -12)]

def row10546 : Integer.Sparse Key := [(key2413, 6), (key2422, 12), (key2486, -6), (key2490, -12)]

def row10547 : Integer.Sparse Key := [(key2413, 6), (key2422, 12), (key2486, -6), (key2490, -12)]

def row10548 : Integer.Sparse Key := [(key2413, 6), (key2422, 12), (key2486, -6), (key2490, -12)]

def row10549 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key3045, 6), (key3094, 12)]

def row10550 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key3045, 6), (key3094, 12)]

def row10551 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key3045, 6), (key3094, 12)]

def row10552 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key2811, 6), (key3045, 6), (key3094, 6)]

def row10553 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key2811, 6), (key3045, 6), (key3094, 6)]

def row10554 : Integer.Sparse Key := [(key2677, -6), (key2708, -12), (key2811, 12), (key3045, 6)]

def row10555 : Integer.Sparse Key := [(key2708, 18), (key2811, -18)]

def row10556 : Integer.Sparse Key := [(key2708, 18), (key2811, -18)]

def row10557 : Integer.Sparse Key := [(key2708, 18), (key2811, -18)]

def row10558 : Integer.Sparse Key := [(key2708, 18), (key2811, -18)]

def row10559 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

def row10560 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

def row10561 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

def row10562 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

def row10563 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

def row10564 : Integer.Sparse Key := [(key2692, -8), (key2718, 8), (key2830, -4), (key2871, 4)]

def row10565 : Integer.Sparse Key := [(key2692, 12), (key2718, -12), (key2830, 6), (key2871, -6)]

def row10566 : Integer.Sparse Key := [(key2692, 12), (key2718, -12), (key2830, 6), (key2871, -6)]

def row10567 : Integer.Sparse Key := [(key2692, 12), (key2718, -12), (key2830, 6), (key2871, -6)]

def row10568 : Integer.Sparse Key := [(key2692, 12), (key2718, -12), (key2830, 6), (key2871, -6)]

def row10569 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

def row10570 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

def row10571 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

def row10572 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

def row10573 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

def row10574 : Integer.Sparse Key := [(key1055, 4), (key1074, -4), (key1143, 4), (key1153, -4)]

def row10575 : Integer.Sparse Key := [(key1055, -6), (key1074, 6), (key1143, -6), (key1153, 6)]

def row10576 : Integer.Sparse Key := [(key1055, -6), (key1074, 6), (key1143, -6), (key1153, 6)]

def row10577 : Integer.Sparse Key := [(key1055, -6), (key1074, 6), (key1143, -6), (key1153, 6)]

def row10578 : Integer.Sparse Key := [(key1055, -6), (key1074, 6), (key1143, -6), (key1153, 6)]

def row10579 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

def row10580 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

def row10581 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

def row10582 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

def row10583 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

def row10584 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3099, 8)]

def row10585 : Integer.Sparse Key := [(key3079, 6), (key3084, 6), (key3099, -12)]

def row10586 : Integer.Sparse Key := [(key3079, 6), (key3084, 6), (key3099, -12)]

def row10587 : Integer.Sparse Key := [(key3079, 6), (key3084, 6), (key3099, -12)]

def row10588 : Integer.Sparse Key := [(key3079, 6), (key3084, 6), (key3099, -12)]

def row10589 : Integer.Sparse Key := [(key1851, 6), (key1855, -6)]

def row10590 : Integer.Sparse Key := [(key1851, 6), (key1855, -6)]

def row10591 : Integer.Sparse Key := [(key1851, 6), (key1855, -6)]

def row10592 : Integer.Sparse Key := [(key1851, 6), (key1855, -6)]

def row10593 : Integer.Sparse Key := [(key1851, -24), (key1855, 24)]

def row10594 : Integer.Sparse Key := [(key685, -6), (key692, 6)]

def row10595 : Integer.Sparse Key := [(key685, -6), (key692, 6)]

def row10596 : Integer.Sparse Key := [(key685, -6), (key692, 6)]

def row10597 : Integer.Sparse Key := [(key685, -6), (key692, 6)]

def row10598 : Integer.Sparse Key := [(key685, 24), (key692, -24)]

def row10599 : Integer.Sparse Key := [(key619, -6), (key645, 6)]

def row10600 : Integer.Sparse Key := [(key619, -6), (key645, 6)]

def row10601 : Integer.Sparse Key := [(key619, -6), (key645, 6)]

def row10602 : Integer.Sparse Key := [(key619, -6), (key645, 6)]

def row10603 : Integer.Sparse Key := [(key619, 24), (key645, -24)]

def row10604 : Integer.Sparse Key := [(key1958, -6), (key1960, 6)]

def row10605 : Integer.Sparse Key := [(key1958, -6), (key1960, 6)]

def row10606 : Integer.Sparse Key := [(key1958, -6), (key1960, 6)]

def row10607 : Integer.Sparse Key := [(key1958, -6), (key1960, 6)]

def row10608 : Integer.Sparse Key := [(key1958, 24), (key1960, -24)]

def row10609 : Integer.Sparse Key := [(key1852, -6), (key1884, 6)]

def row10610 : Integer.Sparse Key := [(key1852, -6), (key1884, 6)]

def row10611 : Integer.Sparse Key := [(key1852, -6), (key1884, 6)]

def row10612 : Integer.Sparse Key := [(key1852, -6), (key1884, 6)]

def row10613 : Integer.Sparse Key := [(key1852, 24), (key1884, -24)]

def row10614 : Integer.Sparse Key := [(key1861, -6), (key1867, 6)]

def row10615 : Integer.Sparse Key := [(key1861, -6), (key1867, 6)]

def row10616 : Integer.Sparse Key := [(key1861, -6), (key1867, 6)]

def row10617 : Integer.Sparse Key := [(key1861, -6), (key1867, 6)]

def row10618 : Integer.Sparse Key := [(key1861, 24), (key1867, -24)]

def row10619 : Integer.Sparse Key := [(key1957, -6), (key1969, 6)]

def row10620 : Integer.Sparse Key := [(key1957, -6), (key1969, 6)]

def row10621 : Integer.Sparse Key := [(key1957, -6), (key1969, 6)]

def row10622 : Integer.Sparse Key := [(key1957, -6), (key1969, 6)]

def row10623 : Integer.Sparse Key := [(key1957, 24), (key1969, -24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10624 : Integer.Sparse Key := [(key1867, -6), (key1877, 6)]

def row10625 : Integer.Sparse Key := [(key1867, -6), (key1877, 6)]

def row10626 : Integer.Sparse Key := [(key1867, -6), (key1877, 6)]

def row10627 : Integer.Sparse Key := [(key1867, -6), (key1877, 6)]

def row10628 : Integer.Sparse Key := [(key1867, 24), (key1877, -24)]

def row10629 : Integer.Sparse Key := [(key627, -6), (key629, 6)]

def row10630 : Integer.Sparse Key := [(key627, -6), (key629, 6)]

def row10631 : Integer.Sparse Key := [(key627, -6), (key629, 6)]

def row10632 : Integer.Sparse Key := [(key627, -6), (key629, 6)]

def row10633 : Integer.Sparse Key := [(key627, 24), (key629, -24)]

def row10634 : Integer.Sparse Key := [(key1859, 6), (key1861, -6)]

def row10635 : Integer.Sparse Key := [(key1859, 6), (key1861, -6)]

def row10636 : Integer.Sparse Key := [(key1859, 6), (key1861, -6)]

def row10637 : Integer.Sparse Key := [(key1859, 6), (key1861, -6)]

def row10638 : Integer.Sparse Key := [(key1859, -24), (key1861, 24)]

def row10639 : Integer.Sparse Key := [(key686, -6), (key687, 6)]

def row10640 : Integer.Sparse Key := [(key686, -6), (key687, 6)]

def row10641 : Integer.Sparse Key := [(key686, -6), (key687, 6)]

def row10642 : Integer.Sparse Key := [(key686, -6), (key687, 6)]

def row10643 : Integer.Sparse Key := [(key686, 24), (key687, -24)]

def row10644 : Integer.Sparse Key := [(key1932, 6), (key1953, -6)]

def row10645 : Integer.Sparse Key := [(key1932, 6), (key1953, -6)]

def row10646 : Integer.Sparse Key := [(key1932, 6), (key1953, -6)]

def row10647 : Integer.Sparse Key := [(key1932, 6), (key1953, -6)]

def row10648 : Integer.Sparse Key := [(key1932, -24), (key1953, 24)]

def row10649 : Integer.Sparse Key := [(key1850, 6), (key1884, -6)]

def row10650 : Integer.Sparse Key := [(key1850, 6), (key1884, -6)]

def row10651 : Integer.Sparse Key := [(key1850, 6), (key1884, -6)]

def row10652 : Integer.Sparse Key := [(key1850, 6), (key1884, -6)]

def row10653 : Integer.Sparse Key := [(key1850, -24), (key1884, 24)]

def row10654 : Integer.Sparse Key := [(key362, -6), (key366, 6)]

def row10655 : Integer.Sparse Key := [(key362, -6), (key366, 6)]

def row10656 : Integer.Sparse Key := [(key362, -6), (key366, 6)]

def row10657 : Integer.Sparse Key := [(key362, -6), (key366, 6)]

def row10658 : Integer.Sparse Key := [(key362, 24), (key366, -24)]

def row10659 : Integer.Sparse Key := [(key617, 6), (key645, -6)]

def row10660 : Integer.Sparse Key := [(key617, 6), (key645, -6)]

def row10661 : Integer.Sparse Key := [(key617, 6), (key645, -6)]

def row10662 : Integer.Sparse Key := [(key617, 6), (key645, -6)]

def row10663 : Integer.Sparse Key := [(key617, -24), (key645, 24)]

def row10664 : Integer.Sparse Key := [(key1933, -6), (key1953, 6)]

def row10665 : Integer.Sparse Key := [(key1933, -6), (key1953, 6)]

def row10666 : Integer.Sparse Key := [(key1933, -6), (key1953, 6)]

def row10667 : Integer.Sparse Key := [(key1933, -6), (key1953, 6)]

def row10668 : Integer.Sparse Key := [(key1933, 24), (key1953, -24)]

def row10669 : Integer.Sparse Key := [(key1960, -6), (key1966, 6)]

def row10670 : Integer.Sparse Key := [(key1960, -6), (key1966, 6)]

def row10671 : Integer.Sparse Key := [(key1960, -6), (key1966, 6)]

def row10672 : Integer.Sparse Key := [(key1960, -6), (key1966, 6)]

def row10673 : Integer.Sparse Key := [(key1960, 24), (key1966, -24)]

def row10674 : Integer.Sparse Key := [(key1864, -6), (key1869, 6)]

def row10675 : Integer.Sparse Key := [(key1864, -6), (key1869, 6)]

def row10676 : Integer.Sparse Key := [(key1864, -6), (key1869, 6)]

def row10677 : Integer.Sparse Key := [(key1864, -6), (key1869, 6)]

def row10678 : Integer.Sparse Key := [(key1864, 24), (key1869, -24)]

def row10679 : Integer.Sparse Key := [(key618, 6), (key622, -6)]

def row10680 : Integer.Sparse Key := [(key618, 6), (key622, -6)]

def row10681 : Integer.Sparse Key := [(key618, 6), (key622, -6)]

def row10682 : Integer.Sparse Key := [(key618, 6), (key622, -6)]

def row10683 : Integer.Sparse Key := [(key618, -24), (key622, 24)]

def row10684 : Integer.Sparse Key := [(key1962, -6), (key1964, 6)]

def row10685 : Integer.Sparse Key := [(key1962, -6), (key1964, 6)]

def row10686 : Integer.Sparse Key := [(key1962, -6), (key1964, 6)]

def row10687 : Integer.Sparse Key := [(key1962, -6), (key1964, 6)]

def row10688 : Integer.Sparse Key := [(key1962, 24), (key1964, -24)]

def row10689 : Integer.Sparse Key := [(key288, 6), (key289, -6)]

def row10690 : Integer.Sparse Key := [(key288, 6), (key289, -6)]

def row10691 : Integer.Sparse Key := [(key288, 6), (key289, -6)]

def row10692 : Integer.Sparse Key := [(key288, 6), (key289, -6)]

def row10693 : Integer.Sparse Key := [(key288, -24), (key289, 24)]

def row10694 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10695 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10696 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10697 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10698 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10699 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10700 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10701 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10702 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10703 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10704 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10705 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10706 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10707 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10708 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10709 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10710 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10711 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10712 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10713 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10714 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10715 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10716 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10717 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2409, -2), (key2437, 2), (key2472, -2), (key2480, 2), (key2482, -2), (key2503, 2), (key2506, -2), (key2522, 2), (key2538, -2), (key2563, 2)]

def row10718 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10719 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10720 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10721 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10722 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10723 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10724 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10725 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10726 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10727 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10728 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10729 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -4), (key2480, -4), (key2482, 4), (key2503, -4), (key2506, 4), (key2522, 4)]

def row10730 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10731 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10732 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10733 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10734 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10735 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10736 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10737 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10738 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10739 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10740 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10741 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10742 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10743 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10744 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10745 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10746 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10747 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10748 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10749 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10750 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10751 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10752 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10753 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, -18), (key1187, 6)]

def row10754 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10755 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10756 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10757 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10758 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10759 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10760 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10761 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10762 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10763 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10764 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10765 : Integer.Sparse Key := [(key990, 6), (key1025, 6), (key1103, 12), (key1187, -24)]

def row10766 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10767 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10768 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10769 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10770 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10771 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10772 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10773 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10774 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10775 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10776 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10777 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10778 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10779 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10780 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10781 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10782 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10783 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10784 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10785 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10786 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10787 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10788 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10789 : Integer.Sparse Key := [(key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1069, 2), (key1107, -4), (key1112, -6), (key1121, -4), (key1148, -4), (key1191, 2), (key1197, 2), (key1210, 2)]

def row10790 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10791 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10792 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10793 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10794 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10795 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10796 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10797 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10798 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10799 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10800 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10801 : Integer.Sparse Key := [(key999, 4), (key1013, 2), (key1034, 4), (key1069, 2), (key1112, 4), (key1121, 4), (key1148, 4), (key1191, -12), (key1197, -6), (key1210, -6)]

def row10802 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10803 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10804 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10805 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10806 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10807 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10808 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10809 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10810 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10811 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10812 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10813 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10814 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10815 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10816 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10817 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10818 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10819 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10820 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10821 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10822 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10823 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10824 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10825 : Integer.Sparse Key := [(key2607, 2), (key2623, -4), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, -4), (key2788, 2), (key2800, 2), (key2823, 2), (key2850, -6), (key2854, 2), (key2864, -4)]

def row10826 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10827 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10828 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10829 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10830 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10831 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10832 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10833 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10834 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10835 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10836 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10837 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, 2), (key2697, 4), (key2777, 4), (key2788, -6), (key2800, 4), (key2850, 4), (key2854, -12)]

def row10838 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10839 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10840 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10841 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10842 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10843 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10844 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10845 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10846 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10847 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10848 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10849 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10850 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10851 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10852 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10853 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10854 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10855 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10856 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10857 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10858 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10859 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10860 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10861 : Integer.Sparse Key := [(key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2434, 2), (key2465, -4), (key2469, -6), (key2477, -4), (key2500, -4), (key2536, 2), (key2541, 2), (key2552, 2)]

def row10862 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10863 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10864 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10865 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10866 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10867 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10868 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10869 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10870 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10871 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10872 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10873 : Integer.Sparse Key := [(key2375, 4), (key2387, 2), (key2403, 4), (key2434, 2), (key2469, 4), (key2477, 4), (key2500, 4), (key2536, -12), (key2541, -6), (key2552, -6)]

def row10874 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10875 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10876 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10877 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10878 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10879 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row10880 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10881 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10882 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10883 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10884 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10885 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10886 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10887 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10888 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10889 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10890 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10891 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10892 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10893 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10894 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10895 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10896 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10897 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, 1), (key2791, 1), (key2802, 1), (key2826, 1), (key2852, -2), (key2857, -2), (key2867, -2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row10898 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10899 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10900 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10901 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10902 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10903 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10904 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10905 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10906 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10907 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10908 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10909 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2783, 2), (key2791, 2), (key2806, 2), (key2826, 2), (key2857, 2), (key2867, 2), (key2894, -4), (key2896, -4), (key2903, -4)]

def row10910 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10911 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10912 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10913 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10914 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10915 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10916 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10917 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10918 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10919 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10920 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10921 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10922 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10923 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10924 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10925 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10926 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10927 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10928 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10929 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10930 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10931 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10932 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10933 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, -18), (key2872, 6)]

def row10934 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10935 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10936 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10937 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10938 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10939 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10940 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10941 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10942 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10943 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10944 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10945 : Integer.Sparse Key := [(key2582, 6), (key2761, 6), (key2838, 12), (key2872, -24)]

def row10946 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10947 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10948 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10949 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10950 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10951 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10952 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10953 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10954 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10955 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10956 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10957 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10958 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10959 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10960 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10961 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10962 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10963 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10964 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10965 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10966 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10967 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10968 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10969 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2723, 2), (key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2973, 2), (key2975, 2), (key2982, 2)]

def row10970 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10971 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10972 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10973 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10974 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10975 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10976 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10977 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10978 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10979 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10980 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10981 : Integer.Sparse Key := [(key2647, 4), (key2652, 2), (key2736, 4), (key2746, 2), (key2894, 4), (key2896, 4), (key2903, 4), (key2937, -4), (key2942, -2), (key2949, -4), (key2959, -2), (key2973, -4), (key2975, -4), (key2982, -4)]

def row10982 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10983 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10984 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10985 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10986 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10987 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10988 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10989 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10990 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10991 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10992 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10993 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10994 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10995 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10996 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10997 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10998 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row10999 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row11000 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row11001 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row11002 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row11003 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row11004 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row11005 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, 1), (key1555, 1), (key1569, 1), (key1592, 1), (key1618, -2), (key1623, -2), (key1632, -2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row11006 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11007 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11008 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11009 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11010 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11011 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11012 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11013 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11014 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11015 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11016 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11017 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

def row11018 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11019 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11020 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11021 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11022 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11023 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11024 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11025 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11026 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11027 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11028 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11029 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11030 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11031 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11032 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11033 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11034 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11035 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11036 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11037 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11038 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11039 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11040 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11041 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row11042 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11043 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11044 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11045 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11046 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11047 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11048 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11049 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11050 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11051 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11052 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11053 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

def row11054 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11055 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11056 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11057 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11058 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11059 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11060 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11061 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11062 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11063 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11064 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11065 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11066 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11067 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11068 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11069 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11070 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11071 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11072 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11073 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11074 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11075 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11076 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11077 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

def row11078 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11079 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11080 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11081 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11082 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11083 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11084 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11085 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11086 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11087 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11088 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11089 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

def row11090 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11091 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11092 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11093 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11094 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11095 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11096 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11097 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11098 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11099 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11100 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11101 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11102 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11103 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11104 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11105 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11106 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11107 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11108 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11109 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11110 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11111 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11112 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11113 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def row11114 : Integer.Sparse Key := [(key2370, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -12)]

def row11115 : Integer.Sparse Key := [(key2370, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -12)]

def row11116 : Integer.Sparse Key := [(key2370, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -12)]

def row11117 : Integer.Sparse Key := [(key2398, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -12)]

def row11118 : Integer.Sparse Key := [(key2398, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -12)]

def row11119 : Integer.Sparse Key := [(key2398, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -12)]

def row11120 : Integer.Sparse Key := [(key2370, -6), (key2464, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -6)]

def row11121 : Integer.Sparse Key := [(key2370, -6), (key2464, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -6)]

def row11122 : Integer.Sparse Key := [(key2398, -6), (key2464, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -6)]

def row11123 : Integer.Sparse Key := [(key2398, -6), (key2464, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -6)]

def row11124 : Integer.Sparse Key := [(key2370, -6), (key2464, -12), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6)]

def row11125 : Integer.Sparse Key := [(key2398, -6), (key2464, -12), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6)]

def row11126 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11127 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11128 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11129 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11130 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11131 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11132 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11133 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11134 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11135 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11136 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11137 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11138 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11139 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11140 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11141 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11142 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11143 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11144 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11145 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11146 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11147 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11148 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11149 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

def row11150 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11151 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11152 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11153 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11154 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11155 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11156 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11157 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11158 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11159 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11160 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11161 : Integer.Sparse Key := [(key2371, -6), (key2399, -6), (key2465, -12), (key2536, 12), (key2541, 6), (key2552, 6)]

def row11162 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11163 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11164 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11165 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11166 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11167 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11168 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11169 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11170 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11171 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11172 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11173 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11174 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11175 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11176 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11177 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11178 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11179 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11180 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11181 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11182 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11183 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11184 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11185 : Integer.Sparse Key := [(key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2200, 2), (key2302, -4), (key2303, -6), (key2305, -4), (key2310, -4), (key2341, 2), (key2343, 2), (key2347, 2)]

def row11186 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11187 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11188 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11189 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11190 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11191 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11192 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11193 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11194 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11195 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11196 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11197 : Integer.Sparse Key := [(key2092, 4), (key2095, 2), (key2194, 4), (key2200, 2), (key2303, 4), (key2305, 4), (key2310, 4), (key2341, -12), (key2343, -6), (key2347, -6)]

def row11198 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11199 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11200 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11201 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11202 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11203 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11204 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11205 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11206 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11207 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11208 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11209 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11210 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11211 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11212 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11213 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11214 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11215 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11216 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11217 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11218 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11219 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11220 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11221 : Integer.Sparse Key := [(key999, -6), (key1034, -6), (key1107, 6), (key1121, 6), (key1148, 6), (key1191, -6)]

def row11222 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11223 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11224 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11225 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11226 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11227 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11228 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11229 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11230 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11231 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11232 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11233 : Integer.Sparse Key := [(key994, -6), (key1029, -6), (key1107, -12), (key1191, 12), (key1197, 6), (key1210, 6)]

def row11234 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

def row11235 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

def row11236 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

def row11237 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

def row11238 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

def row11239 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

def row11240 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

def row11241 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

def row11242 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

def row11243 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

def row11244 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

def row11245 : Integer.Sparse Key := [(key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2583, 2), (key2586, 2), (key2597, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2965, 2), (key2987, 2)]

def row11246 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2586, 2), (key2762, 2), (key2765, 2), (key2874, 2), (key2908, 2), (key2928, 2), (key2987, 2)]

def row11247 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2586, 2), (key2762, 2), (key2765, 2), (key2874, 2), (key2908, 2), (key2928, 2), (key2987, 2)]

def row11248 : Integer.Sparse Key := [(key2398, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2583, 2), (key2586, 2), (key2597, 2), (key2765, 2), (key2874, 2), (key2908, 2), (key2987, 2)]

def row11249 : Integer.Sparse Key := [(key2398, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2583, 2), (key2586, 2), (key2597, 2), (key2765, 2), (key2874, 2), (key2908, 2), (key2987, 2)]

def row11250 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2540, 2), (key2551, 2), (key2586, 2), (key2762, 2), (key2765, 2), (key2874, 2)]

def row11251 : Integer.Sparse Key := [(key2386, 2), (key2398, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2540, 2), (key2551, 2), (key2583, 2), (key2586, 2), (key2765, 2), (key2874, 2)]

def row11252 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2762, 2), (key2839, 2)]

def row11253 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2762, 2), (key2839, 2)]

def row11254 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, 2), (key2839, 2)]

def row11255 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, 2), (key2401, 2), (key2433, 2), (key2464, -6), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, 2), (key2839, 2)]

def row11256 : Integer.Sparse Key := [(key2370, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2762, 2)]

def row11257 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, 2), (key2401, 2), (key2433, 2), (key2464, -4), (key2467, -6), (key2476, -4), (key2499, -4), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, 2)]

def row11258 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11259 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11260 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11261 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11262 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11263 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11264 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11265 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11266 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11267 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11268 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11269 : Integer.Sparse Key := [(key2373, 4), (key2386, 2), (key2401, 4), (key2433, 2), (key2467, 4), (key2476, 4), (key2499, 4), (key2534, -12), (key2540, -6), (key2551, -6)]

def row11270 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11271 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11272 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11273 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11274 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11275 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11276 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11277 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11278 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11279 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11280 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11281 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11282 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11283 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11284 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11285 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11286 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11287 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11288 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11289 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11290 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11291 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11292 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11293 : Integer.Sparse Key := [(key2623, 6), (key2697, -6), (key2777, 6), (key2800, -6), (key2854, -6), (key2864, 6)]

def row11294 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11295 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11296 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11297 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11298 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11299 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11300 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11301 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11302 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11303 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11304 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11305 : Integer.Sparse Key := [(key2634, 6), (key2720, -6), (key2788, 6), (key2823, -6), (key2854, 12), (key2864, -12)]

def row11306 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11307 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11308 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11309 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11310 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11311 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11312 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11313 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11314 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11315 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11316 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11317 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11318 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11319 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11320 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11321 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11322 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11323 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11324 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11325 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11326 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11327 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11328 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11329 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2642, -2), (key2654, 2), (key2671, 2), (key2706, -2), (key2729, -2), (key2748, 2), (key2794, 2), (key2829, 2), (key2860, -2), (key2870, -2), (key2883, -2), (key2913, 2), (key2944, 2), (key2961, 2), (key2977, -2), (key2984, -2)]

def row11330 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11331 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11332 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11333 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11334 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11335 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11336 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11337 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11338 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11339 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11340 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11341 : Integer.Sparse Key := [(key2619, 2), (key2642, 4), (key2649, -2), (key2654, -4), (key2674, 2), (key2729, 4), (key2738, -2), (key2748, -4), (key2796, 4), (key2832, 4), (key2883, 4), (key2898, -4), (key2905, -4), (key2913, -4)]

def row11342 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11343 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11344 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11345 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11346 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11347 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11348 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11349 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11350 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11351 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11352 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11353 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11354 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11355 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11356 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11357 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11358 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11359 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11360 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11361 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11362 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11363 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11364 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11365 : Integer.Sparse Key := [(key1007, -2), (key1017, 2), (key1042, -2), (key1073, 2), (key1116, -2), (key1125, 2), (key1128, -2), (key1152, 2), (key1156, -2), (key1172, 2), (key1194, -2), (key1223, 2)]

def row11366 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11367 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11368 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11369 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11370 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11371 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11372 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11373 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11374 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11375 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11376 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11377 : Integer.Sparse Key := [(key1003, -4), (key1007, 2), (key1017, -2), (key1020, 4), (key1038, -4), (key1042, 2), (key1073, -2), (key1077, 4), (key1116, -4), (key1125, -4), (key1128, 4), (key1152, -4), (key1156, 4), (key1172, 4)]

def row11378 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11379 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11380 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11381 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11382 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11383 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11384 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11385 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11386 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11387 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11388 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11389 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11390 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11391 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11392 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11393 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11394 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11395 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11396 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11397 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11398 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11399 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11400 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11401 : Integer.Sparse Key := [(key2678, 2), (key2687, 6), (key2709, -4), (key2713, 2), (key2812, -4), (key2816, 2), (key2862, -4)]

def row11402 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11403 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11404 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11405 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11406 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11407 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11408 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11409 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11410 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11411 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11412 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11413 : Integer.Sparse Key := [(key2678, 12), (key2687, -4), (key2709, 6), (key2713, -8), (key2812, 6), (key2816, -8), (key2862, -4)]

def row11414 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11415 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11416 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11417 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11418 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11419 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11420 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11421 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11422 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11423 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11424 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11425 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11426 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11427 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11428 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11429 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11430 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11431 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11432 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11433 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11434 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11435 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11436 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11437 : Integer.Sparse Key := [(key1936, 6), (key1937, -18), (key1940, 6), (key1949, 6)]

def row11438 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11439 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11440 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11441 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11442 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11443 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11444 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11445 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11446 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11447 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11448 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11449 : Integer.Sparse Key := [(key1936, -24), (key1937, 12), (key1940, 6), (key1949, 6)]

def row11450 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11451 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11452 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11453 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11454 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11455 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11456 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11457 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11458 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11459 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11460 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11461 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2734, 2), (key2745, 2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11462 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 1), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11463 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 1), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11464 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 2), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11465 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 2), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11466 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 1), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11467 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2745, 1), (key2778, 1), (key2781, -2), (key2801, 1), (key2804, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11468 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11469 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11470 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11471 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11472 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11473 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, -2), (key2790, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def row11474 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11475 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11476 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11477 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -8), (key2701, 2), (key2722, 2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11478 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -8), (key2701, 2), (key2722, 2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11479 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -8), (key2701, 2), (key2722, 2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11480 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11481 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11482 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -6), (key2701, 2), (key2722, 2), (key2778, -2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11483 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -6), (key2701, 2), (key2722, 2), (key2778, -2), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11484 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11485 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, -4), (key2627, 2), (key2636, 2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2722, 2), (key2778, -4), (key2781, 2), (key2790, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, -4), (key2856, 2), (key2866, 2)]

def row11486 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11487 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11488 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11489 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11490 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11491 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11492 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11493 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11494 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11495 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11496 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11497 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2472, 4), (key2480, -4), (key2482, -4), (key2503, 4), (key2506, 4), (key2522, -4), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row11498 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11499 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11500 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11501 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11502 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11503 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11504 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11505 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11506 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11507 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11508 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11509 : Integer.Sparse Key := [(key990, 6), (key1025, -24), (key1103, 12), (key1187, 6)]

def row11510 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11511 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11512 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11513 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11514 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11515 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11516 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11517 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11518 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11519 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11520 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11521 : Integer.Sparse Key := [(key994, 2), (key999, 4), (key1029, -6), (key1034, -12), (key1069, -6), (key1107, 4), (key1112, 4), (key1148, 4), (key1191, 4), (key1210, 2)]

def row11522 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11523 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11524 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11525 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11526 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11527 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11528 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11529 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11530 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11531 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11532 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11533 : Integer.Sparse Key := [(key2607, -6), (key2623, 4), (key2634, 2), (key2697, 4), (key2720, 2), (key2800, -12), (key2823, -6), (key2850, 4), (key2854, 4), (key2864, 4)]

def row11534 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11535 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11536 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11537 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11538 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11539 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11540 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11541 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11542 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11543 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11544 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11545 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2399, -6), (key2403, -12), (key2434, -6), (key2465, 4), (key2469, 4), (key2500, 4), (key2536, 4), (key2552, 2)]

def row11546 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11547 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11548 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11549 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11550 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11551 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11552 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11553 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11554 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11555 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11556 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11557 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2779, 2), (key2783, 2), (key2802, -4), (key2806, -4), (key2826, -4), (key2852, 2), (key2867, 2), (key2894, 2), (key2903, 2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row11558 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11559 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11560 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11561 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11562 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11563 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11564 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11565 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11566 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11567 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11568 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11569 : Integer.Sparse Key := [(key2582, 6), (key2761, -24), (key2838, 12), (key2872, 6)]

def row11570 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11571 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11572 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11573 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11574 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11575 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11576 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11577 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11578 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11579 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11580 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11581 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2664, -2), (key2668, -4), (key2699, -4), (key2703, -4), (key2723, -4), (key2736, -4), (key2746, -2), (key2802, 4), (key2806, 4), (key2826, 4), (key2949, 4), (key2959, 2)]

def row11582 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11583 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11584 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11585 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11586 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11587 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11588 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11589 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11590 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11591 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11592 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11593 : Integer.Sparse Key := [(key1292, -2), (key1297, -4), (key1312, 2), (key1317, 2), (key1338, 2), (key1542, 2), (key1547, 2), (key1569, -4), (key1574, -4), (key1592, -4), (key1618, 2), (key1632, 2), (key1656, 2), (key1666, 2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row11594 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11595 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11596 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11597 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11598 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11599 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11600 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11601 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11602 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11603 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11604 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11605 : Integer.Sparse Key := [(key2625, 2), (key2629, 2), (key2637, -4), (key2647, 2), (key2652, -2), (key2779, 2), (key2783, 2), (key2791, -4), (key2852, 2), (key2857, -4), (key2867, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, 2), (key2942, -2), (key2973, 2), (key2975, -4), (key2982, 2)]

def row11606 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11607 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11608 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11609 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11610 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11611 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11612 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11613 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11614 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11615 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11616 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11617 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1538, 4), (key1565, -12), (key1614, 4), (key1652, 4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row11618 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11619 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11620 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11621 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11622 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11623 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11624 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11625 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11626 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11627 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11628 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11629 : Integer.Sparse Key := [(key2398, 6), (key2401, 12), (key2433, 6), (key2597, -6), (key2886, -12), (key2908, -6)]

def row11630 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11631 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11632 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11633 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11634 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11635 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11636 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11637 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11638 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11639 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11640 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11641 : Integer.Sparse Key := [(key2387, -6), (key2399, 6), (key2403, 12), (key2434, 6), (key2477, -12), (key2541, -6)]

def row11642 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11643 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11644 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11645 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11646 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11647 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11648 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11649 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11650 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11651 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11652 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11653 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2193, -6), (key2194, -12), (key2200, -6), (key2302, 4), (key2303, 4), (key2310, 4), (key2341, 4), (key2347, 2)]

def row11654 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11655 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11656 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11657 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11658 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11659 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11660 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11661 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11662 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11663 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11664 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11665 : Integer.Sparse Key := [(key1013, -6), (key1029, 6), (key1034, 12), (key1069, 6), (key1121, -12), (key1197, -6)]

def row11666 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11667 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11668 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11669 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11670 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11671 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11672 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11673 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11674 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11675 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11676 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11677 : Integer.Sparse Key := [(key2398, -6), (key2401, -12), (key2433, -6), (key2583, 2), (key2586, 4), (key2839, 4), (key2842, 4), (key2874, 4), (key2965, 4), (key2987, 2)]

def row11678 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11679 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11680 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11681 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11682 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11683 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11684 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11685 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11686 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11687 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11688 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11689 : Integer.Sparse Key := [(key2607, 6), (key2662, -6), (key2777, -12), (key2788, -6), (key2800, 12), (key2823, 6)]

def row11690 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11691 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11692 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11693 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11694 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11695 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11696 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11697 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11698 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11699 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11700 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11701 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 4), (key2649, 2), (key2786, 4), (key2809, -4), (key2829, -4), (key2832, -4), (key2870, 4), (key2905, 4), (key2939, 2), (key2951, -2), (key2961, -4), (key2984, 4)]

def row11702 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11703 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11704 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11705 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11706 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11707 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11708 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11709 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11710 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11711 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11712 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11713 : Integer.Sparse Key := [(key1003, 4), (key1007, 2), (key1017, -2), (key1020, -4), (key1116, 4), (key1125, -4), (key1128, -4), (key1152, 4), (key1156, 4), (key1172, -4), (key1194, 2), (key1200, -4), (key1213, 4), (key1223, -2)]

def row11714 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11715 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11716 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11717 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11718 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11719 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11720 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11721 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11722 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11723 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11724 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11725 : Integer.Sparse Key := [(key2678, -8), (key2687, -4), (key2709, 6), (key2713, 12), (key2812, -4), (key2816, -8), (key2862, 6)]

def row11726 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11727 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11728 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11729 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11730 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11731 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11732 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11733 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11734 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11735 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11736 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11737 : Integer.Sparse Key := [(key1936, 6), (key1937, 12), (key1940, -24), (key1949, 6)]

def row11738 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11739 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11740 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11741 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11742 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11743 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11744 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11745 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11746 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11747 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11748 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11749 : Integer.Sparse Key := [(key2624, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2734, -4), (key2745, -2), (key2851, 2), (key2856, 2), (key2866, 2), (key2892, -4), (key2895, -4), (key2902, -4), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11750 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11751 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11752 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11753 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -6), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11754 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -6), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11755 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -8), (key2851, 2), (key2856, 2), (key2866, 2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11756 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -8), (key2851, 2), (key2856, 2), (key2866, 2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11757 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -6), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11758 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -6), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -2), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11759 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11760 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11761 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2801, -4), (key2804, -4), (key2825, -4), (key2851, 2), (key2856, 2), (key2866, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row11762 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11763 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11764 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11765 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11766 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11767 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11768 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11769 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11770 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11771 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11772 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11773 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2734, 2), (key2745, 2), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11774 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 1), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11775 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 1), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11776 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 2), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11777 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 2), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11778 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 1), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11779 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2745, 1), (key2778, 1), (key2790, 2), (key2801, 1), (key2825, 2), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2941, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11780 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11781 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11782 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11783 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11784 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11785 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, -1), (key2627, -2), (key2636, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, -1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2851, -2), (key2856, -2), (key2866, -2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row11786 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

def row11787 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

def row11788 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

def row11789 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

def row11790 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

def row11791 : Integer.Sparse Key := [(key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4), (key2532, -8), (key2533, -4), (key2562, -4), (key2564, -8)]

def row11792 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

def row11793 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

def row11794 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

def row11795 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

def row11796 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

def row11797 : Integer.Sparse Key := [(key974, -24), (key1088, 12), (key1178, 12)]

def row11798 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11799 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11800 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11801 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11802 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11803 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11804 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11805 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11806 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11807 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11808 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11809 : Integer.Sparse Key := [(key974, 6), (key1088, -18), (key1178, 12)]

def row11810 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

def row11811 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

def row11812 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

def row11813 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

def row11814 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

def row11815 : Integer.Sparse Key := [(key976, -12), (key984, -12), (key1090, 8), (key1098, 4), (key1180, 4), (key1183, 8)]

def row11816 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11817 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11818 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11819 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11820 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11821 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11822 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11823 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11824 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11825 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11826 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11827 : Integer.Sparse Key := [(key976, 4), (key984, 2), (key1090, -8), (key1098, -6), (key1169, -4), (key1180, 4), (key1183, 4), (key1220, 4)]

def row11828 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

def row11829 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

def row11830 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

def row11831 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

def row11832 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

def row11833 : Integer.Sparse Key := [(key2405, -12), (key2436, -12), (key2471, 4), (key2479, 8), (key2502, 8), (key2518, 4)]

def row11834 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11835 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11836 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11837 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11838 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11839 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11840 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11841 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11842 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11843 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11844 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11845 : Integer.Sparse Key := [(key2377, -4), (key2389, 4), (key2405, 2), (key2436, 4), (key2471, -6), (key2479, 4), (key2502, -8), (key2518, 4)]

def row11846 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2366, -12), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

def row11847 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -6), (key2366, -6), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

def row11848 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -6), (key2366, -6), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

def row11849 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -12), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

def row11850 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -12), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

def row11851 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2363, -12), (key2456, 8), (key2461, 4), (key2517, 4), (key2523, 8)]

def row11852 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, 2), (key2452, -12), (key2456, 4), (key2458, -6), (key2517, 4), (key2519, -6), (key2523, 4), (key2567, 2), (key2579, 4)]

def row11853 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -12), (key2456, 4), (key2458, -6), (key2517, 4), (key2519, -6), (key2523, 4), (key2567, 2), (key2579, 4)]

def row11854 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -12), (key2456, 4), (key2458, -6), (key2517, 4), (key2519, -6), (key2523, 4), (key2567, 2), (key2579, 4)]

def row11855 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, 2), (key2452, -8), (key2458, -6), (key2517, 4), (key2519, -4), (key2523, 4), (key2579, 4)]

def row11856 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, 2), (key2452, -8), (key2458, -6), (key2517, 2), (key2519, -4), (key2523, 4), (key2528, 2), (key2560, 4)]

def row11857 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2366, 2), (key2452, -8), (key2458, -6), (key2517, 2), (key2519, -4), (key2523, 4), (key2528, 2), (key2560, 4)]

def row11858 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

def row11859 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

def row11860 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

def row11861 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

def row11862 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

def row11863 : Integer.Sparse Key := [(key2357, 2), (key2361, 2), (key2363, 2), (key2452, -10), (key2456, 2), (key2458, -6), (key2517, 2), (key2519, -4), (key2528, 2), (key2530, 4), (key2560, 4)]

def row11864 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

def row11865 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

def row11866 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

def row11867 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

def row11868 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

def row11869 : Integer.Sparse Key := [(key2406, -8), (key2411, -4), (key2437, -4), (key2443, -8), (key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4)]

def row11870 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -4), (key2593, -2), (key2843, -4), (key2880, -2), (key2966, -4), (key2968, -4), (key2989, -4)]

def row11871 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -4), (key2593, -2), (key2843, -4), (key2880, -2), (key2966, -4), (key2968, -4), (key2989, -4)]

def row11872 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -4), (key2593, -2), (key2843, -4), (key2880, -2), (key2966, -4), (key2968, -4), (key2989, -4)]

def row11873 : Integer.Sparse Key := [(key2390, 2), (key2394, 2), (key2437, 2), (key2443, 2), (key2524, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2766, 2), (key2843, -4), (key2880, -2), (key2887, 2), (key2910, 2), (key2966, -2), (key2968, -4), (key2989, -2)]

def row11874 : Integer.Sparse Key := [(key2390, 1), (key2394, 2), (key2437, 1), (key2443, 2), (key2524, 2), (key2587, -2), (key2593, -2), (key2598, 1), (key2766, 2), (key2843, -4), (key2880, -2), (key2887, 2), (key2910, 2), (key2929, 1), (key2966, -2), (key2968, -4), (key2989, -2), (key3002, 2)]

def row11875 : Integer.Sparse Key := [(key2390, 1), (key2394, 2), (key2437, 1), (key2443, 2), (key2524, 2), (key2587, -2), (key2593, -2), (key2598, 1), (key2766, 2), (key2843, -4), (key2880, -2), (key2887, 2), (key2910, 2), (key2929, 1), (key2966, -2), (key2968, -4), (key2989, -2), (key3002, 2)]

def row11876 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

def row11877 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

def row11878 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

def row11879 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

def row11880 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

def row11881 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2587, -3), (key2593, -2), (key2598, 1), (key2600, 2), (key2766, 1), (key2843, -4), (key2880, -2), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, -3), (key2968, -4), (key2989, -2), (key2995, 2), (key3002, 2)]

def row11882 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

def row11883 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

def row11884 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

def row11885 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

def row11886 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

def row11887 : Integer.Sparse Key := [(key2360, -24), (key2455, 12), (key2516, 12)]

def row11888 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11889 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11890 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11891 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11892 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11893 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11894 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11895 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11896 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11897 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11898 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11899 : Integer.Sparse Key := [(key2360, 6), (key2455, -18), (key2516, 12)]

def row11900 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

def row11901 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

def row11902 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

def row11903 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row11904 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

def row11905 : Integer.Sparse Key := [(key2378, -8), (key2383, -4), (key2390, -4), (key2394, -8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8)]

def row11906 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11907 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11908 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11909 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11910 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11911 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11912 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11913 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11914 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11915 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11916 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11917 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2766, -4), (key2772, -2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row11918 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

def row11919 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

def row11920 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

def row11921 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

def row11922 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

def row11923 : Integer.Sparse Key := [(key1531, -8), (key1536, -4), (key1609, 4), (key1648, 4), (key1651, 4), (key1765, -4), (key1768, -8), (key1806, 4), (key1809, 4), (key1837, 4)]

def row11924 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11925 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11926 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11927 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11928 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11929 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11930 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11931 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11932 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11933 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11934 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11935 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1265, 2), (key1268, 2), (key1531, 2), (key1609, -4), (key1642, -2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, -2), (key1809, -4), (key1832, -2), (key1837, 2), (key1848, 2)]

def row11936 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

def row11937 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

def row11938 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

def row11939 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

def row11940 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

def row11941 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 4), (key2569, -4), (key2571, -8), (key2576, -8), (key2580, -4)]

def row11942 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, 2), (key2394, -2), (key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -4), (key2503, 2), (key2509, -4), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2)]

def row11943 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, 2), (key2394, -2), (key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -4), (key2503, 2), (key2509, -4), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2)]

def row11944 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, 2), (key2394, -2), (key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -4), (key2503, 2), (key2509, -4), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2)]

def row11945 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2394, -2), (key2411, -2), (key2437, 2), (key2443, -2), (key2484, -4), (key2509, -4), (key2524, -2), (key2580, 2), (key2587, 2), (key2766, 2), (key2887, 2), (key2910, 2), (key2966, 2), (key2989, 2)]

def row11946 : Integer.Sparse Key := [(key2383, -2), (key2390, 1), (key2394, -2), (key2411, -2), (key2437, 1), (key2443, -2), (key2484, -4), (key2509, -4), (key2524, -2), (key2587, 2), (key2598, 1), (key2766, 2), (key2887, 2), (key2910, 2), (key2929, 1), (key2966, 2), (key2989, 2), (key3002, 2)]

def row11947 : Integer.Sparse Key := [(key2383, -2), (key2390, 1), (key2394, -2), (key2411, -2), (key2437, 1), (key2443, -2), (key2484, -4), (key2509, -4), (key2524, -2), (key2587, 2), (key2598, 1), (key2766, 2), (key2887, 2), (key2910, 2), (key2929, 1), (key2966, 2), (key2989, 2), (key3002, 2)]

def row11948 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

def row11949 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

def row11950 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

def row11951 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

def row11952 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

def row11953 : Integer.Sparse Key := [(key2378, 1), (key2383, -2), (key2390, 1), (key2394, -4), (key2406, 1), (key2411, -2), (key2437, 1), (key2443, -4), (key2480, 1), (key2484, -4), (key2503, 1), (key2509, -4), (key2524, -4), (key2587, 1), (key2598, 1), (key2600, 2), (key2766, 1), (key2887, 1), (key2910, 2), (key2929, 1), (key2931, 2), (key2966, 1), (key2989, 2), (key2995, 2), (key3002, 2)]

def row11954 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

def row11955 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

def row11956 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

def row11957 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

def row11958 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

def row11959 : Integer.Sparse Key := [(key1529, -12), (key1607, 4), (key1646, 8), (key1763, -12), (key1804, 8), (key1835, 4)]

def row11960 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11961 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11962 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11963 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11964 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11965 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11966 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11967 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11968 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11969 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11970 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11971 : Integer.Sparse Key := [(key1254, -4), (key1263, 4), (key1529, 2), (key1607, -6), (key1646, 4), (key1763, 4), (key1804, -8), (key1835, 4)]

def row11972 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

def row11973 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

def row11974 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

def row11975 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

def row11976 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

def row11977 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2531, -12), (key2561, -12)]

def row11978 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11979 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11980 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11981 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11982 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11983 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11984 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11985 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11986 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11987 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11988 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11989 : Integer.Sparse Key := [(key2364, -6), (key2456, 12), (key2520, -12), (key2531, 6)]

def row11990 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2567, -12), (key2579, -12)]

def row11991 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2567, -12), (key2579, -12)]

def row11992 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2567, -12), (key2579, -12)]

def row11993 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2567, -12), (key2579, -12)]

def row11994 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2567, -12), (key2579, -12)]

def row11995 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2567, -12), (key2579, -12)]

def row11996 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row11997 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row11998 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row11999 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12000 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12001 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12002 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12003 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12004 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12005 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12006 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12007 : Integer.Sparse Key := [(key2366, -6), (key2452, 12), (key2458, 6), (key2461, -6), (key2519, 6), (key2523, -12)]

def row12008 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

def row12009 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

def row12010 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

def row12011 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

def row12012 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

def row12013 : Integer.Sparse Key := [(key1999, -12), (key2003, -12), (key2268, 8), (key2272, 4), (key2323, 4), (key2324, 8)]

def row12014 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12015 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12016 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12017 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12018 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12019 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12020 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12021 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12022 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12023 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12024 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12025 : Integer.Sparse Key := [(key1999, 4), (key2003, 2), (key2268, -8), (key2272, -6), (key2294, -4), (key2323, 4), (key2324, 4), (key2336, 4)]

def row12026 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

def row12027 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

def row12028 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

def row12029 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

def row12030 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

def row12031 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1169, -12), (key1220, -12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12032 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12033 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12034 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12035 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12036 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12037 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12038 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12039 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12040 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12041 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12042 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12043 : Integer.Sparse Key := [(key984, -6), (key1090, 12), (key1169, 6), (key1183, -12)]

def row12044 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

def row12045 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

def row12046 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

def row12047 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

def row12048 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

def row12049 : Integer.Sparse Key := [(key2361, -12), (key2364, -12), (key2456, 8), (key2459, 4), (key2517, 4), (key2520, 8)]

def row12050 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12051 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12052 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12053 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12054 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12055 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12056 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12057 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12058 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12059 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12060 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12061 : Integer.Sparse Key := [(key2361, 4), (key2364, 2), (key2456, -8), (key2459, -6), (key2517, 4), (key2520, 4), (key2531, -4), (key2561, 4)]

def row12062 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

def row12063 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

def row12064 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

def row12065 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

def row12066 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

def row12067 : Integer.Sparse Key := [(key2377, -12), (key2389, -12), (key2405, 12), (key2436, 12)]

def row12068 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12069 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12070 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12071 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12072 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12073 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12074 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12075 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12076 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12077 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12078 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12079 : Integer.Sparse Key := [(key2377, 6), (key2405, -6), (key2479, -12), (key2502, 12)]

def row12080 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

def row12081 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

def row12082 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

def row12083 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

def row12084 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

def row12085 : Integer.Sparse Key := [(key2407, -4), (key2410, -8), (key2441, -8), (key2445, -4), (key2473, 4), (key2483, 8), (key2507, 8), (key2526, 4)]

def row12086 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2407, 2), (key2441, 4), (key2544, 4), (key2555, 4), (key2565, 4), (key2592, -2), (key2595, -4), (key2848, -2), (key2882, -4), (key2970, -4), (key2991, -4), (key2993, -4)]

def row12087 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2407, 2), (key2441, 4), (key2544, 4), (key2555, 4), (key2565, 4), (key2592, -2), (key2595, -4), (key2848, -2), (key2882, -4), (key2970, -4), (key2991, -4), (key2993, -4)]

def row12088 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2407, 2), (key2441, 4), (key2544, 4), (key2555, 4), (key2565, 4), (key2592, -2), (key2595, -4), (key2848, -2), (key2882, -4), (key2970, -4), (key2991, -4), (key2993, -4)]

def row12089 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2595, -4), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2970, -4), (key2993, -4)]

def row12090 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2595, -4), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2970, -4), (key2993, -4)]

def row12091 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2595, -4), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2970, -4), (key2993, -4)]

def row12092 : Integer.Sparse Key := [(key2379, 2), (key2393, 2), (key2407, 2), (key2441, 2), (key2544, 2), (key2555, 2), (key2592, -2), (key2595, -4), (key2602, 2), (key2848, -2), (key2882, -4), (key2912, 2), (key2933, 2), (key2970, -4), (key2991, -2), (key2993, -4), (key3003, 4)]

def row12093 : Integer.Sparse Key := [(key2379, 2), (key2393, 2), (key2407, 2), (key2441, 2), (key2544, 2), (key2555, 2), (key2592, -2), (key2595, -4), (key2602, 2), (key2848, -2), (key2882, -4), (key2912, 2), (key2933, 2), (key2970, -4), (key2991, -2), (key2993, -4), (key3003, 4)]

def row12094 : Integer.Sparse Key := [(key2393, 2), (key2441, 2), (key2595, -4), (key2602, 2), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2933, 2), (key2970, -4), (key2993, -4), (key3003, 4)]

def row12095 : Integer.Sparse Key := [(key2393, 2), (key2441, 2), (key2595, -4), (key2602, 2), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2933, 2), (key2970, -4), (key2993, -4), (key3003, 4)]

def row12096 : Integer.Sparse Key := [(key2379, 2), (key2407, 2), (key2592, -2), (key2595, -4), (key2602, 4), (key2848, -2), (key2882, -4), (key2912, 4), (key2933, 4), (key2970, -4), (key2993, -4), (key3003, 4)]

def row12097 : Integer.Sparse Key := [(key2595, -4), (key2602, 4), (key2771, 2), (key2848, -2), (key2882, -4), (key2912, 4), (key2933, 4), (key2970, -4), (key2993, -4), (key3003, 4)]

def row12098 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

def row12099 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

def row12100 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

def row12101 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

def row12102 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

def row12103 : Integer.Sparse Key := [(key1096, 4), (key1100, 8), (key1171, -8), (key1175, -4), (key1185, 8), (key1186, 4), (key1222, -4), (key1224, -8)]

def row12104 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12105 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12106 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12107 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12108 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12109 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12110 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12111 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12112 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12113 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12114 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12115 : Integer.Sparse Key := [(key982, 2), (key988, -2), (key1096, 2), (key1100, -4), (key1171, 4), (key1175, -2), (key1186, -4), (key1222, 4)]

def row12116 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

def row12117 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

def row12118 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

def row12119 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

def row12120 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

def row12121 : Integer.Sparse Key := [(key2420, -4), (key2427, -16), (key2438, -4), (key2495, 12), (key2504, 12)]

def row12122 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12123 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12124 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12125 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12126 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12127 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12128 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12129 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12130 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12131 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12132 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12133 : Integer.Sparse Key := [(key2420, -4), (key2427, 4), (key2438, 6), (key2495, -8), (key2504, 2)]

def row12134 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

def row12135 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

def row12136 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

def row12137 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

def row12138 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

def row12139 : Integer.Sparse Key := [(key1851, 12), (key1855, 12), (key1886, -24)]

def row12140 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12141 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12142 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12143 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12144 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12145 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12146 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12147 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12148 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12149 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12150 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12151 : Integer.Sparse Key := [(key1851, 12), (key1855, -18), (key1886, 6)]

def row12152 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

def row12153 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

def row12154 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

def row12155 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

def row12156 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

def row12157 : Integer.Sparse Key := [(key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4), (key2538, -4), (key2543, -8), (key2554, -8), (key2563, -4)]

def row12158 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12159 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12160 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12161 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12162 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12163 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12164 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12165 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12166 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12167 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12168 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12169 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, 2), (key2392, -2), (key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -4), (key2503, 2), (key2506, -4), (key2522, -2), (key2543, 2), (key2554, 2), (key2563, 2)]

def row12170 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

def row12171 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

def row12172 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

def row12173 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

def row12174 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

def row12175 : Integer.Sparse Key := [(key2406, -8), (key2409, -4), (key2437, -4), (key2440, -8), (key2472, 4), (key2480, 4), (key2482, 4), (key2503, 4), (key2506, 4), (key2522, 4)]

def row12176 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12177 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12178 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12179 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12180 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12181 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12182 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12183 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12184 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12185 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12186 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12187 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2472, -4), (key2480, 2), (key2503, -2), (key2506, -4), (key2522, 2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row12188 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

def row12189 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

def row12190 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

def row12191 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

def row12192 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

def row12193 : Integer.Sparse Key := [(key2362, -4), (key2365, -16), (key2367, -4), (key2457, 4), (key2460, 8), (key2521, 8), (key2525, 4)]

def row12194 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

def row12195 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

def row12196 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

def row12197 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2525, -4), (key2562, 4), (key2564, 4)]

def row12198 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2525, -4), (key2562, 4), (key2564, 4)]

def row12199 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2525, -4), (key2562, 4), (key2564, 4)]

def row12200 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

def row12201 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

def row12202 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -2), (key2525, -4), (key2532, 2), (key2562, 4), (key2564, 4)]

def row12203 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -2), (key2525, -4), (key2532, 2), (key2562, 4), (key2564, 4)]

def row12204 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

def row12205 : Integer.Sparse Key := [(key2362, 2), (key2365, 4), (key2457, -2), (key2460, -8), (key2521, -4), (key2525, -4), (key2532, 4), (key2562, 4), (key2564, 4)]

def row12206 : Integer.Sparse Key := [(key1700, 24), (key1851, -24)]

def row12207 : Integer.Sparse Key := [(key1700, -6), (key1851, 6)]

def row12208 : Integer.Sparse Key := [(key1700, -6), (key1851, 6)]

def row12209 : Integer.Sparse Key := [(key1700, -6), (key1851, 6)]

def row12210 : Integer.Sparse Key := [(key1700, -6), (key1851, 6)]

def row12211 : Integer.Sparse Key := [(key219, -24), (key491, 24)]

def row12212 : Integer.Sparse Key := [(key219, 6), (key491, -6)]

def row12213 : Integer.Sparse Key := [(key219, 6), (key491, -6)]

def row12214 : Integer.Sparse Key := [(key219, 6), (key491, -6)]

def row12215 : Integer.Sparse Key := [(key219, 6), (key491, -6)]

def row12216 : Integer.Sparse Key := [(key30, -24), (key110, 24)]

def row12217 : Integer.Sparse Key := [(key30, 6), (key110, -6)]

def row12218 : Integer.Sparse Key := [(key30, 6), (key110, -6)]

def row12219 : Integer.Sparse Key := [(key30, 6), (key110, -6)]

def row12220 : Integer.Sparse Key := [(key30, 6), (key110, -6)]

def row12221 : Integer.Sparse Key := [(key1483, -24), (key1709, 24)]

def row12222 : Integer.Sparse Key := [(key1483, 6), (key1709, -6)]

def row12223 : Integer.Sparse Key := [(key1483, 6), (key1709, -6)]

def row12224 : Integer.Sparse Key := [(key1483, 6), (key1709, -6)]

def row12225 : Integer.Sparse Key := [(key1483, 6), (key1709, -6)]

def row12226 : Integer.Sparse Key := [(key1274, -24), (key1697, 24)]

def row12227 : Integer.Sparse Key := [(key1274, 6), (key1697, -6)]

def row12228 : Integer.Sparse Key := [(key1274, 6), (key1697, -6)]

def row12229 : Integer.Sparse Key := [(key1274, 6), (key1697, -6)]

def row12230 : Integer.Sparse Key := [(key1274, 6), (key1697, -6)]

def row12231 : Integer.Sparse Key := [(key1485, -24), (key1711, 24)]

def row12232 : Integer.Sparse Key := [(key1485, 6), (key1711, -6)]

def row12233 : Integer.Sparse Key := [(key1485, 6), (key1711, -6)]

def row12234 : Integer.Sparse Key := [(key1485, 6), (key1711, -6)]

def row12235 : Integer.Sparse Key := [(key1485, 6), (key1711, -6)]

def row12236 : Integer.Sparse Key := [(key1272, -24), (key1695, 24)]

def row12237 : Integer.Sparse Key := [(key1272, 6), (key1695, -6)]

def row12238 : Integer.Sparse Key := [(key1272, 6), (key1695, -6)]

def row12239 : Integer.Sparse Key := [(key1272, 6), (key1695, -6)]

def row12240 : Integer.Sparse Key := [(key1272, 6), (key1695, -6)]

def row12241 : Integer.Sparse Key := [(key1359, -24), (key1485, 24)]

def row12242 : Integer.Sparse Key := [(key1359, 6), (key1485, -6)]

def row12243 : Integer.Sparse Key := [(key1359, 6), (key1485, -6)]

def row12244 : Integer.Sparse Key := [(key1359, 6), (key1485, -6)]

def row12245 : Integer.Sparse Key := [(key1359, 6), (key1485, -6)]

def row12246 : Integer.Sparse Key := [(key395, -24), (key440, 24)]

def row12247 : Integer.Sparse Key := [(key395, 6), (key440, -6)]

def row12248 : Integer.Sparse Key := [(key395, 6), (key440, -6)]

def row12249 : Integer.Sparse Key := [(key395, 6), (key440, -6)]

def row12250 : Integer.Sparse Key := [(key395, 6), (key440, -6)]

def row12251 : Integer.Sparse Key := [(key1711, 24), (key1936, -24)]

def row12252 : Integer.Sparse Key := [(key1711, -6), (key1936, 6)]

def row12253 : Integer.Sparse Key := [(key1711, -6), (key1936, 6)]

def row12254 : Integer.Sparse Key := [(key1711, -6), (key1936, 6)]

def row12255 : Integer.Sparse Key := [(key1711, -6), (key1936, 6)]

def row12256 : Integer.Sparse Key := [(key348, -24), (key505, 24)]

def row12257 : Integer.Sparse Key := [(key348, 6), (key505, -6)]

def row12258 : Integer.Sparse Key := [(key348, 6), (key505, -6)]

def row12259 : Integer.Sparse Key := [(key348, 6), (key505, -6)]

def row12260 : Integer.Sparse Key := [(key348, 6), (key505, -6)]

def row12261 : Integer.Sparse Key := [(key1273, 24), (key1850, -24)]

def row12262 : Integer.Sparse Key := [(key1273, -6), (key1850, 6)]

def row12263 : Integer.Sparse Key := [(key1273, -6), (key1850, 6)]

def row12264 : Integer.Sparse Key := [(key1273, -6), (key1850, 6)]

def row12265 : Integer.Sparse Key := [(key1273, -6), (key1850, 6)]

def row12266 : Integer.Sparse Key := [(key1274, 24), (key1932, -24)]

def row12267 : Integer.Sparse Key := [(key1274, -6), (key1932, 6)]

def row12268 : Integer.Sparse Key := [(key1274, -6), (key1932, 6)]

def row12269 : Integer.Sparse Key := [(key1274, -6), (key1932, 6)]

def row12270 : Integer.Sparse Key := [(key1274, -6), (key1932, 6)]

def row12271 : Integer.Sparse Key := [(key750, -24), (key927, 24)]

def row12272 : Integer.Sparse Key := [(key750, 6), (key927, -6)]

def row12273 : Integer.Sparse Key := [(key750, 6), (key927, -6)]

def row12274 : Integer.Sparse Key := [(key750, 6), (key927, -6)]

def row12275 : Integer.Sparse Key := [(key750, 6), (key927, -6)]

def row12276 : Integer.Sparse Key := [(key30, 24), (key146, -24)]

def row12277 : Integer.Sparse Key := [(key30, -6), (key146, 6)]

def row12278 : Integer.Sparse Key := [(key30, -6), (key146, 6)]

def row12279 : Integer.Sparse Key := [(key30, -6), (key146, 6)]

def row12280 : Integer.Sparse Key := [(key30, -6), (key146, 6)]

def row12281 : Integer.Sparse Key := [(key1273, -24), (key1696, 24)]

def row12282 : Integer.Sparse Key := [(key1273, 6), (key1696, -6)]

def row12283 : Integer.Sparse Key := [(key1273, 6), (key1696, -6)]

def row12284 : Integer.Sparse Key := [(key1273, 6), (key1696, -6)]

def row12285 : Integer.Sparse Key := [(key1273, 6), (key1696, -6)]

def row12286 : Integer.Sparse Key := [(key1357, -24), (key1483, 24)]

def row12287 : Integer.Sparse Key := [(key1357, 6), (key1483, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12288 : Integer.Sparse Key := [(key1357, 6), (key1483, -6)]

def row12289 : Integer.Sparse Key := [(key1357, 6), (key1483, -6)]

def row12290 : Integer.Sparse Key := [(key1357, 6), (key1483, -6)]

def row12291 : Integer.Sparse Key := [(key1489, -24), (key1715, 24)]

def row12292 : Integer.Sparse Key := [(key1489, 6), (key1715, -6)]

def row12293 : Integer.Sparse Key := [(key1489, 6), (key1715, -6)]

def row12294 : Integer.Sparse Key := [(key1489, 6), (key1715, -6)]

def row12295 : Integer.Sparse Key := [(key1489, 6), (key1715, -6)]

def row12296 : Integer.Sparse Key := [(key118, 24), (key155, -24)]

def row12297 : Integer.Sparse Key := [(key118, -6), (key155, 6)]

def row12298 : Integer.Sparse Key := [(key118, -6), (key155, 6)]

def row12299 : Integer.Sparse Key := [(key118, -6), (key155, 6)]

def row12300 : Integer.Sparse Key := [(key118, -6), (key155, 6)]

def row12301 : Integer.Sparse Key := [(key1498, -24), (key1730, 24)]

def row12302 : Integer.Sparse Key := [(key1498, 6), (key1730, -6)]

def row12303 : Integer.Sparse Key := [(key1498, 6), (key1730, -6)]

def row12304 : Integer.Sparse Key := [(key1498, 6), (key1730, -6)]

def row12305 : Integer.Sparse Key := [(key1498, 6), (key1730, -6)]

def row12306 : Integer.Sparse Key := [(key670, 24), (key680, -24)]

def row12307 : Integer.Sparse Key := [(key670, -6), (key680, 6)]

def row12308 : Integer.Sparse Key := [(key670, -6), (key680, 6)]

def row12309 : Integer.Sparse Key := [(key670, -6), (key680, 6)]

def row12310 : Integer.Sparse Key := [(key670, -6), (key680, 6)]

def row12311 : Integer.Sparse Key := [(key1710, 24), (key1859, -24)]

def row12312 : Integer.Sparse Key := [(key1710, -6), (key1859, 6)]

def row12313 : Integer.Sparse Key := [(key1710, -6), (key1859, 6)]

def row12314 : Integer.Sparse Key := [(key1710, -6), (key1859, 6)]

def row12315 : Integer.Sparse Key := [(key1710, -6), (key1859, 6)]

def row12316 : Integer.Sparse Key := [(key1484, -24), (key1710, 24)]

def row12317 : Integer.Sparse Key := [(key1484, 6), (key1710, -6)]

def row12318 : Integer.Sparse Key := [(key1484, 6), (key1710, -6)]

def row12319 : Integer.Sparse Key := [(key1484, 6), (key1710, -6)]

def row12320 : Integer.Sparse Key := [(key1484, 6), (key1710, -6)]

def row12321 : Integer.Sparse Key := [(key1277, -24), (key1700, 24)]

def row12322 : Integer.Sparse Key := [(key1277, 6), (key1700, -6)]

def row12323 : Integer.Sparse Key := [(key1277, 6), (key1700, -6)]

def row12324 : Integer.Sparse Key := [(key1277, 6), (key1700, -6)]

def row12325 : Integer.Sparse Key := [(key1277, 6), (key1700, -6)]

def row12326 : Integer.Sparse Key := [(key288, -24), (key513, 24)]

def row12327 : Integer.Sparse Key := [(key288, 6), (key513, -6)]

def row12328 : Integer.Sparse Key := [(key288, 6), (key513, -6)]

def row12329 : Integer.Sparse Key := [(key288, 6), (key513, -6)]

def row12330 : Integer.Sparse Key := [(key288, 6), (key513, -6)]

def row12331 : Integer.Sparse Key := [(key2421, -6), (key2428, 12), (key2429, -12), (key2442, 6), (key2550, -6), (key2556, 6)]

def row12332 : Integer.Sparse Key := [(key2421, -6), (key2428, 12), (key2429, -12), (key2442, 6), (key2550, -6), (key2556, 6)]

def row12333 : Integer.Sparse Key := [(key2421, -6), (key2428, 12), (key2429, -12), (key2442, 6), (key2550, -6), (key2556, 6)]

def row12334 : Integer.Sparse Key := [(key2421, -6), (key2428, 12), (key2429, -12), (key2442, 6), (key2550, -6), (key2556, 6)]

def row12335 : Integer.Sparse Key := [(key2421, -6), (key2428, -12), (key2429, 12), (key2442, 6), (key2496, -6), (key2508, 6)]

def row12336 : Integer.Sparse Key := [(key2421, -6), (key2428, -12), (key2429, 12), (key2442, 6), (key2496, -6), (key2508, 6)]

def row12337 : Integer.Sparse Key := [(key2421, -6), (key2428, -12), (key2429, 12), (key2442, 6), (key2496, -6), (key2508, 6)]

def row12338 : Integer.Sparse Key := [(key2421, -6), (key2428, -12), (key2429, 12), (key2442, 6), (key2496, -6), (key2508, 6)]

def row12339 : Integer.Sparse Key := [(key1046, 18), (key1132, -24), (key1203, 6)]

def row12340 : Integer.Sparse Key := [(key1046, 18), (key1132, -24), (key1203, 6)]

def row12341 : Integer.Sparse Key := [(key1046, 18), (key1132, -24), (key1203, 6)]

def row12342 : Integer.Sparse Key := [(key1046, 18), (key1132, -24), (key1203, 6)]

def row12343 : Integer.Sparse Key := [(key1046, 18), (key1132, 6), (key1203, -24)]

def row12344 : Integer.Sparse Key := [(key1046, 18), (key1132, 6), (key1203, -24)]

def row12345 : Integer.Sparse Key := [(key1046, 18), (key1132, 6), (key1203, -24)]

def row12346 : Integer.Sparse Key := [(key1046, 18), (key1132, 6), (key1203, -24)]

def row12347 : Integer.Sparse Key := [(key1049, 6), (key1060, 12), (key1135, -6), (key1140, -18), (key1207, 6)]

def row12348 : Integer.Sparse Key := [(key1049, 6), (key1060, 12), (key1135, -6), (key1140, -18), (key1207, 6)]

def row12349 : Integer.Sparse Key := [(key1049, 6), (key1060, 12), (key1135, -6), (key1140, -18), (key1207, 6)]

def row12350 : Integer.Sparse Key := [(key1049, 6), (key1060, 12), (key1135, -6), (key1140, -18), (key1207, 6)]

def row12351 : Integer.Sparse Key := [(key1052, 6), (key1060, 12), (key1140, 6), (key1205, -6), (key1207, -18)]

def row12352 : Integer.Sparse Key := [(key1052, 6), (key1060, 12), (key1140, 6), (key1205, -6), (key1207, -18)]

def row12353 : Integer.Sparse Key := [(key1052, 6), (key1060, 12), (key1140, 6), (key1205, -6), (key1207, -18)]

def row12354 : Integer.Sparse Key := [(key1052, 6), (key1060, 12), (key1140, 6), (key1205, -6), (key1207, -18)]

def row12355 : Integer.Sparse Key := [(key3046, 12), (key3060, -18), (key3064, 6), (key3101, 6), (key3125, -6)]

def row12356 : Integer.Sparse Key := [(key3046, 12), (key3060, -18), (key3064, 6), (key3101, 6), (key3125, -6)]

def row12357 : Integer.Sparse Key := [(key3046, 12), (key3060, -18), (key3064, 6), (key3101, 6), (key3125, -6)]

def row12358 : Integer.Sparse Key := [(key3046, 12), (key3060, -18), (key3064, 6), (key3101, 6), (key3125, -6)]

def row12359 : Integer.Sparse Key := [(key3046, 12), (key3060, 6), (key3064, -18), (key3095, 6), (key3123, -6)]

def row12360 : Integer.Sparse Key := [(key3046, 12), (key3060, 6), (key3064, -18), (key3095, 6), (key3123, -6)]

def row12361 : Integer.Sparse Key := [(key3046, 12), (key3060, 6), (key3064, -18), (key3095, 6), (key3123, -6)]

def row12362 : Integer.Sparse Key := [(key3046, 12), (key3060, 6), (key3064, -18), (key3095, 6), (key3123, -6)]

def row12363 : Integer.Sparse Key := [(key2415, 6), (key2425, 12), (key2488, -6), (key2493, -18), (key2549, 6)]

def row12364 : Integer.Sparse Key := [(key2415, 6), (key2425, 12), (key2488, -6), (key2493, -18), (key2549, 6)]

def row12365 : Integer.Sparse Key := [(key2415, 6), (key2425, 12), (key2488, -6), (key2493, -18), (key2549, 6)]

def row12366 : Integer.Sparse Key := [(key2415, 6), (key2425, 12), (key2488, -6), (key2493, -18), (key2549, 6)]

def row12367 : Integer.Sparse Key := [(key2418, 6), (key2425, 12), (key2493, 6), (key2547, -6), (key2549, -18)]

def row12368 : Integer.Sparse Key := [(key2418, 6), (key2425, 12), (key2493, 6), (key2547, -6), (key2549, -18)]

def row12369 : Integer.Sparse Key := [(key2418, 6), (key2425, 12), (key2493, 6), (key2547, -6), (key2549, -18)]

def row12370 : Integer.Sparse Key := [(key2418, 6), (key2425, 12), (key2493, 6), (key2547, -6), (key2549, -18)]

def row12371 : Integer.Sparse Key := [(key2680, 6), (key2690, 6), (key2711, -6), (key2716, -12), (key2743, 6), (key2956, 6), (key2980, -6)]

def row12372 : Integer.Sparse Key := [(key2680, 6), (key2690, 6), (key2711, -6), (key2716, -12), (key2743, 6), (key2956, 6), (key2980, -6)]

def row12373 : Integer.Sparse Key := [(key2680, 6), (key2690, 6), (key2711, -6), (key2716, -12), (key2743, 6), (key2956, 6), (key2980, -6)]

def row12374 : Integer.Sparse Key := [(key2680, 6), (key2690, 6), (key2711, -6), (key2716, -12), (key2743, 6), (key2956, 6), (key2980, -6)]

def row12375 : Integer.Sparse Key := [(key2683, 6), (key2690, 6), (key2716, 6), (key2741, -6), (key2743, -12), (key2819, 6), (key2901, -6)]

def row12376 : Integer.Sparse Key := [(key2683, 6), (key2690, 6), (key2716, 6), (key2741, -6), (key2743, -12), (key2819, 6), (key2901, -6)]

def row12377 : Integer.Sparse Key := [(key2683, 6), (key2690, 6), (key2716, 6), (key2741, -6), (key2743, -12), (key2819, 6), (key2901, -6)]

def row12378 : Integer.Sparse Key := [(key2683, 6), (key2690, 6), (key2716, 6), (key2741, -6), (key2743, -12), (key2819, 6), (key2901, -6)]

def row12379 : Integer.Sparse Key := [(key3032, 18), (key3119, -24), (key3127, 6)]

def row12380 : Integer.Sparse Key := [(key3032, 18), (key3119, -24), (key3127, 6)]

def row12381 : Integer.Sparse Key := [(key3032, 18), (key3119, -24), (key3127, 6)]

def row12382 : Integer.Sparse Key := [(key3032, 18), (key3119, -24), (key3127, 6)]

def row12383 : Integer.Sparse Key := [(key3032, 18), (key3119, 6), (key3127, -24)]

def row12384 : Integer.Sparse Key := [(key3032, 18), (key3119, 6), (key3127, -24)]

def row12385 : Integer.Sparse Key := [(key3032, 18), (key3119, 6), (key3127, -24)]

def row12386 : Integer.Sparse Key := [(key3032, 18), (key3119, 6), (key3127, -24)]

def row12387 : Integer.Sparse Key := [(key2711, 6), (key2716, 12), (key2814, -6), (key2819, -12), (key2901, -6), (key2980, 6)]

def row12388 : Integer.Sparse Key := [(key2711, 6), (key2716, 12), (key2814, -6), (key2819, -12), (key2901, -6), (key2980, 6)]

def row12389 : Integer.Sparse Key := [(key2711, 6), (key2716, 12), (key2814, -6), (key2819, -12), (key2901, -6), (key2980, 6)]

def row12390 : Integer.Sparse Key := [(key2711, 6), (key2716, 12), (key2814, -6), (key2819, -12), (key2901, -6), (key2980, 6)]

def row12391 : Integer.Sparse Key := [(key2741, 6), (key2743, 12), (key2901, 6), (key2954, -6), (key2956, -12), (key2980, -6)]

def row12392 : Integer.Sparse Key := [(key2741, 6), (key2743, 12), (key2901, 6), (key2954, -6), (key2956, -12), (key2980, -6)]

def row12393 : Integer.Sparse Key := [(key2741, 6), (key2743, 12), (key2901, 6), (key2954, -6), (key2956, -12), (key2980, -6)]

def row12394 : Integer.Sparse Key := [(key2741, 6), (key2743, 12), (key2901, 6), (key2954, -6), (key2956, -12), (key2980, -6)]

def row12395 : Integer.Sparse Key := [(key1406, 6), (key1412, 6), (key1434, -6), (key1437, -12), (key1463, 6), (key1795, 6), (key1822, -6)]

def row12396 : Integer.Sparse Key := [(key1406, 6), (key1412, 6), (key1434, -6), (key1437, -12), (key1463, 6), (key1795, 6), (key1822, -6)]

def row12397 : Integer.Sparse Key := [(key1406, 6), (key1412, 6), (key1434, -6), (key1437, -12), (key1463, 6), (key1795, 6), (key1822, -6)]

def row12398 : Integer.Sparse Key := [(key1406, 6), (key1412, 6), (key1434, -6), (key1437, -12), (key1463, 6), (key1795, 6), (key1822, -6)]

def row12399 : Integer.Sparse Key := [(key1408, 6), (key1412, 6), (key1437, 6), (key1462, -6), (key1463, -12), (key1586, 6), (key1664, -6)]

def row12400 : Integer.Sparse Key := [(key1408, 6), (key1412, 6), (key1437, 6), (key1462, -6), (key1463, -12), (key1586, 6), (key1664, -6)]

def row12401 : Integer.Sparse Key := [(key1408, 6), (key1412, 6), (key1437, 6), (key1462, -6), (key1463, -12), (key1586, 6), (key1664, -6)]

def row12402 : Integer.Sparse Key := [(key1408, 6), (key1412, 6), (key1437, 6), (key1462, -6), (key1463, -12), (key1586, 6), (key1664, -6)]

def row12403 : Integer.Sparse Key := [(key2680, 6), (key2683, -12), (key2690, 6), (key2741, -6), (key2743, 6), (key2954, -6), (key2956, 6)]

def row12404 : Integer.Sparse Key := [(key2680, 6), (key2683, -12), (key2690, 6), (key2741, -6), (key2743, 6), (key2954, -6), (key2956, 6)]

def row12405 : Integer.Sparse Key := [(key2680, 6), (key2683, -12), (key2690, 6), (key2741, -6), (key2743, 6), (key2954, -6), (key2956, 6)]

def row12406 : Integer.Sparse Key := [(key2680, 6), (key2683, -12), (key2690, 6), (key2741, -6), (key2743, 6), (key2954, -6), (key2956, 6)]

def row12407 : Integer.Sparse Key := [(key2680, -12), (key2683, 6), (key2690, 6), (key2711, -6), (key2716, 6), (key2814, -6), (key2819, 6)]

def row12408 : Integer.Sparse Key := [(key2680, -12), (key2683, 6), (key2690, 6), (key2711, -6), (key2716, 6), (key2814, -6), (key2819, 6)]

def row12409 : Integer.Sparse Key := [(key2680, -12), (key2683, 6), (key2690, 6), (key2711, -6), (key2716, 6), (key2814, -6), (key2819, 6)]

def row12410 : Integer.Sparse Key := [(key2680, -12), (key2683, 6), (key2690, 6), (key2711, -6), (key2716, 6), (key2814, -6), (key2819, 6)]

def row12411 : Integer.Sparse Key := [(key1403, 12), (key1431, -18), (key1461, 6), (key1794, 6), (key1821, -6)]

def row12412 : Integer.Sparse Key := [(key1403, 12), (key1431, -18), (key1461, 6), (key1794, 6), (key1821, -6)]

def row12413 : Integer.Sparse Key := [(key1403, 12), (key1431, -18), (key1461, 6), (key1794, 6), (key1821, -6)]

def row12414 : Integer.Sparse Key := [(key1403, 12), (key1431, -18), (key1461, 6), (key1794, 6), (key1821, -6)]

def row12415 : Integer.Sparse Key := [(key1403, 12), (key1431, 6), (key1461, -18), (key1580, 6), (key1663, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12416 : Integer.Sparse Key := [(key1403, 12), (key1431, 6), (key1461, -18), (key1580, 6), (key1663, -6)]

def row12417 : Integer.Sparse Key := [(key1403, 12), (key1431, 6), (key1461, -18), (key1580, 6), (key1663, -6)]

def row12418 : Integer.Sparse Key := [(key1403, 12), (key1431, 6), (key1461, -18), (key1580, 6), (key1663, -6)]

def row12419 : Integer.Sparse Key := [(key2487, 6), (key2492, 18), (key3035, -18), (key3128, -6)]

def row12420 : Integer.Sparse Key := [(key2487, 6), (key2492, 18), (key3035, -18), (key3128, -6)]

def row12421 : Integer.Sparse Key := [(key2487, 6), (key2492, 18), (key3035, -18), (key3128, -6)]

def row12422 : Integer.Sparse Key := [(key2487, 6), (key2492, 18), (key3035, -18), (key3128, -6)]

def row12423 : Integer.Sparse Key := [(key2414, -6), (key2546, 6), (key2548, 18), (key3033, -12), (key3120, -6)]

def row12424 : Integer.Sparse Key := [(key2414, -6), (key2546, 6), (key2548, 18), (key3033, -12), (key3120, -6)]

def row12425 : Integer.Sparse Key := [(key2414, -6), (key2546, 6), (key2548, 18), (key3033, -12), (key3120, -6)]

def row12426 : Integer.Sparse Key := [(key2414, -6), (key2487, -6), (key2546, 6), (key2548, 18), (key3033, -12)]

def row12427 : Integer.Sparse Key := [(key2418, -18), (key2488, 6), (key2493, 18), (key2547, -6)]

def row12428 : Integer.Sparse Key := [(key2418, -18), (key2488, 6), (key2493, 18), (key2547, -6)]

def row12429 : Integer.Sparse Key := [(key2418, -18), (key2488, 6), (key2493, 18), (key2547, -6)]

def row12430 : Integer.Sparse Key := [(key2418, -18), (key2488, 6), (key2493, 18), (key2547, -6)]

def row12431 : Integer.Sparse Key := [(key2415, -18), (key2488, -6), (key2547, 6), (key2549, 18)]

def row12432 : Integer.Sparse Key := [(key2415, -18), (key2488, -6), (key2547, 6), (key2549, 18)]

def row12433 : Integer.Sparse Key := [(key2415, -18), (key2488, -6), (key2547, 6), (key2549, 18)]

def row12434 : Integer.Sparse Key := [(key2415, -18), (key2488, -6), (key2547, 6), (key2549, 18)]

def row12435 : Integer.Sparse Key := [(key2197, 6), (key2199, 12), (key2308, -6), (key2309, -18), (key2346, 6)]

def row12436 : Integer.Sparse Key := [(key2197, 6), (key2199, 12), (key2308, -6), (key2309, -18), (key2346, 6)]

def row12437 : Integer.Sparse Key := [(key2197, 6), (key2199, 12), (key2308, -6), (key2309, -18), (key2346, 6)]

def row12438 : Integer.Sparse Key := [(key2197, 6), (key2199, 12), (key2308, -6), (key2309, -18), (key2346, 6)]

def row12439 : Integer.Sparse Key := [(key2198, 6), (key2199, 12), (key2309, 6), (key2345, -6), (key2346, -18)]

def row12440 : Integer.Sparse Key := [(key2198, 6), (key2199, 12), (key2309, 6), (key2345, -6), (key2346, -18)]

def row12441 : Integer.Sparse Key := [(key2198, 6), (key2199, 12), (key2309, 6), (key2345, -6), (key2346, -18)]

def row12442 : Integer.Sparse Key := [(key2198, 6), (key2199, 12), (key2309, 6), (key2345, -6), (key2346, -18)]

def row12443 : Integer.Sparse Key := [(key1052, -18), (key1135, 6), (key1140, 18), (key1205, -6)]

def row12444 : Integer.Sparse Key := [(key1052, -18), (key1135, 6), (key1140, 18), (key1205, -6)]

def row12445 : Integer.Sparse Key := [(key1052, -18), (key1135, 6), (key1140, 18), (key1205, -6)]

def row12446 : Integer.Sparse Key := [(key1052, -18), (key1135, 6), (key1140, 18), (key1205, -6)]

def row12447 : Integer.Sparse Key := [(key1049, -18), (key1135, -6), (key1205, 6), (key1207, 18)]

def row12448 : Integer.Sparse Key := [(key1049, -18), (key1135, -6), (key1205, 6), (key1207, 18)]

def row12449 : Integer.Sparse Key := [(key1049, -18), (key1135, -6), (key1205, 6), (key1207, 18)]

def row12450 : Integer.Sparse Key := [(key1049, -18), (key1135, -6), (key1205, 6), (key1207, 18)]

def row12451 : Integer.Sparse Key := [(key2414, 2), (key2424, 4), (key2487, -6), (key2492, -18), (key3033, 4), (key3039, 8), (key3138, 6)]

def row12452 : Integer.Sparse Key := [(key2414, 2), (key2424, 4), (key2487, -6), (key2492, -18), (key3033, 4), (key3039, 8), (key3138, 6)]

def row12453 : Integer.Sparse Key := [(key2414, 2), (key2424, 4), (key2487, -6), (key2492, -18), (key3033, 4), (key3039, 8), (key3138, 6)]

def row12454 : Integer.Sparse Key := [(key2414, 2), (key2424, 12), (key2487, -6), (key2492, -18), (key2548, 6), (key3033, 4)]

def row12455 : Integer.Sparse Key := [(key2417, 6), (key2424, 12), (key2492, 6), (key2546, -6), (key2548, -18)]

def row12456 : Integer.Sparse Key := [(key2417, 6), (key2424, 12), (key2492, 6), (key2546, -6), (key2548, -18)]

def row12457 : Integer.Sparse Key := [(key2417, 6), (key2424, 12), (key2492, 6), (key2546, -6), (key2548, -18)]

def row12458 : Integer.Sparse Key := [(key2417, 6), (key2424, 12), (key2492, 6), (key2546, -6), (key2548, -18)]

def row12459 : Integer.Sparse Key := [(key3060, 18), (key3095, -18), (key3123, -6), (key3125, 6)]

def row12460 : Integer.Sparse Key := [(key3060, 18), (key3095, -18), (key3123, -6), (key3125, 6)]

def row12461 : Integer.Sparse Key := [(key3060, 18), (key3095, -18), (key3123, -6), (key3125, 6)]

def row12462 : Integer.Sparse Key := [(key3060, 18), (key3095, -18), (key3123, -6), (key3125, 6)]

def row12463 : Integer.Sparse Key := [(key3064, 18), (key3101, -18), (key3123, 6), (key3125, -6)]

def row12464 : Integer.Sparse Key := [(key3064, 18), (key3101, -18), (key3123, 6), (key3125, -6)]

def row12465 : Integer.Sparse Key := [(key3064, 18), (key3101, -18), (key3123, 6), (key3125, -6)]

def row12466 : Integer.Sparse Key := [(key3064, 18), (key3101, -18), (key3123, 6), (key3125, -6)]

def row12467 : Integer.Sparse Key := [(key2693, 12), (key2719, -12), (key2731, -6), (key2750, 6), (key2963, 6), (key2986, -6)]

def row12468 : Integer.Sparse Key := [(key2693, 12), (key2719, -12), (key2731, -6), (key2750, 6), (key2963, 6), (key2986, -6)]

def row12469 : Integer.Sparse Key := [(key2693, 12), (key2719, -12), (key2731, -6), (key2750, 6), (key2963, 6), (key2986, -6)]

def row12470 : Integer.Sparse Key := [(key2693, 12), (key2719, -12), (key2731, -6), (key2750, 6), (key2963, 6), (key2986, -6)]

def row12471 : Integer.Sparse Key := [(key2694, 12), (key2731, 6), (key2744, -12), (key2750, -6), (key2834, 6), (key2907, -6)]

def row12472 : Integer.Sparse Key := [(key2694, 12), (key2731, 6), (key2744, -12), (key2750, -6), (key2834, 6), (key2907, -6)]

def row12473 : Integer.Sparse Key := [(key2694, 12), (key2731, 6), (key2744, -12), (key2750, -6), (key2834, 6), (key2907, -6)]

def row12474 : Integer.Sparse Key := [(key2694, 12), (key2731, 6), (key2744, -12), (key2750, -6), (key2834, 6), (key2907, -6)]

def row12475 : Integer.Sparse Key := [(key1056, -6), (key1064, 12), (key1065, -12), (key1079, 6), (key1208, -6), (key1215, 6)]

def row12476 : Integer.Sparse Key := [(key1056, -6), (key1064, 12), (key1065, -12), (key1079, 6), (key1208, -6), (key1215, 6)]

def row12477 : Integer.Sparse Key := [(key1056, -6), (key1064, 12), (key1065, -12), (key1079, 6), (key1208, -6), (key1215, 6)]

def row12478 : Integer.Sparse Key := [(key1056, -6), (key1064, 12), (key1065, -12), (key1079, 6), (key1208, -6), (key1215, 6)]

def row12479 : Integer.Sparse Key := [(key1056, -6), (key1064, -12), (key1065, 12), (key1079, 6), (key1144, -6), (key1158, 6)]

def row12480 : Integer.Sparse Key := [(key1056, -6), (key1064, -12), (key1065, 12), (key1079, 6), (key1144, -6), (key1158, 6)]

def row12481 : Integer.Sparse Key := [(key1056, -6), (key1064, -12), (key1065, 12), (key1079, 6), (key1144, -6), (key1158, 6)]

def row12482 : Integer.Sparse Key := [(key1056, -6), (key1064, -12), (key1065, 12), (key1079, 6), (key1144, -6), (key1158, 6)]

def row12483 : Integer.Sparse Key := [(key3080, 6), (key3085, -12), (key3087, 18), (key3100, -12)]

def row12484 : Integer.Sparse Key := [(key3080, 6), (key3085, -12), (key3087, 18), (key3100, -12)]

def row12485 : Integer.Sparse Key := [(key3080, 6), (key3085, -12), (key3087, 18), (key3100, -12)]

def row12486 : Integer.Sparse Key := [(key3080, 6), (key3085, -12), (key3087, 18), (key3100, -12)]

def row12487 : Integer.Sparse Key := [(key3080, 6), (key3085, 18), (key3087, -12), (key3100, -12)]

def row12488 : Integer.Sparse Key := [(key3080, 6), (key3085, 18), (key3087, -12), (key3100, -12)]

def row12489 : Integer.Sparse Key := [(key3080, 6), (key3085, 18), (key3087, -12), (key3100, -12)]

def row12490 : Integer.Sparse Key := [(key3080, 6), (key3085, 18), (key3087, -12), (key3100, -12)]

def row12491 : Integer.Sparse Key := [(key1943, 6), (key1944, -24), (key1946, 18)]

def row12492 : Integer.Sparse Key := [(key1943, 6), (key1944, -24), (key1946, 18)]

def row12493 : Integer.Sparse Key := [(key1943, 6), (key1944, -24), (key1946, 18)]

def row12494 : Integer.Sparse Key := [(key1943, 6), (key1944, -24), (key1946, 18)]

def row12495 : Integer.Sparse Key := [(key1943, -24), (key1944, 6), (key1946, 18)]

def row12496 : Integer.Sparse Key := [(key1943, -24), (key1944, 6), (key1946, 18)]

def row12497 : Integer.Sparse Key := [(key1943, -24), (key1944, 6), (key1946, 18)]

def row12498 : Integer.Sparse Key := [(key1943, -24), (key1944, 6), (key1946, 18)]

def row12499 : Integer.Sparse Key := [(key2679, 3), (key2689, 3), (key2742, 2), (key3047, 3), (key3050, -12), (key3054, 3), (key3066, -6), (key3072, 4), (key3103, -6), (key3110, 6)]

def row12500 : Integer.Sparse Key := [(key2679, 3), (key2689, 3), (key2742, 2), (key3047, 3), (key3050, -12), (key3054, 3), (key3066, -6), (key3072, 4), (key3103, -6), (key3110, 6)]

def row12501 : Integer.Sparse Key := [(key2679, 3), (key2689, 4), (key2742, 2), (key2955, 2), (key3047, 3), (key3050, -12), (key3054, 2), (key3066, -6), (key3072, 4), (key3103, -6), (key3110, 4)]

def row12502 : Integer.Sparse Key := [(key2679, 3), (key2689, 6), (key2742, 6), (key2955, 6), (key3047, 3), (key3050, -12), (key3066, -6), (key3103, -6)]

def row12503 : Integer.Sparse Key := [(key2679, -6), (key2682, 6), (key2689, 6), (key2710, -2), (key2715, 6), (key2818, 6), (key3047, -6), (key3061, -4), (key3096, -6)]

def row12504 : Integer.Sparse Key := [(key2679, -6), (key2682, 6), (key2689, 6), (key2710, -2), (key2715, 6), (key2818, 6), (key3047, -6), (key3061, -4), (key3096, -6)]

def row12505 : Integer.Sparse Key := [(key2679, -6), (key2682, 6), (key2689, 6), (key2710, -2), (key2715, 6), (key2813, -2), (key2818, 6), (key3047, -6), (key3061, -4), (key3096, -4)]

def row12506 : Integer.Sparse Key := [(key2679, -6), (key2682, 6), (key2689, 6), (key2710, -6), (key2715, 6), (key2813, -6), (key2818, 6), (key3047, -6)]

def row12507 : Integer.Sparse Key := [(key2679, 3), (key2689, 3), (key2710, -6), (key2715, -12), (key2742, 2), (key2979, -6), (key3047, 3), (key3054, 3), (key3072, 4), (key3110, 6)]

def row12508 : Integer.Sparse Key := [(key2679, 3), (key2689, 3), (key2710, -6), (key2715, -12), (key2742, 2), (key2979, -6), (key3047, 3), (key3054, 3), (key3072, 4), (key3110, 6)]

def row12509 : Integer.Sparse Key := [(key2679, 3), (key2689, 4), (key2710, -6), (key2715, -12), (key2742, 2), (key2955, 2), (key2979, -6), (key3047, 3), (key3054, 2), (key3072, 4), (key3110, 4)]

def row12510 : Integer.Sparse Key := [(key2679, 3), (key2689, 6), (key2710, -6), (key2715, -12), (key2742, 6), (key2955, 6), (key2979, -6), (key3047, 3)]

def row12511 : Integer.Sparse Key := [(key2682, 6), (key2689, 6), (key2715, 6), (key2740, -6), (key2742, -12), (key2818, 6), (key2900, -6)]

def row12512 : Integer.Sparse Key := [(key2682, 6), (key2689, 6), (key2715, 6), (key2740, -6), (key2742, -12), (key2818, 6), (key2900, -6)]

def row12513 : Integer.Sparse Key := [(key2682, 6), (key2689, 6), (key2715, 6), (key2740, -6), (key2742, -12), (key2818, 6), (key2900, -6)]

def row12514 : Integer.Sparse Key := [(key2682, 6), (key2689, 6), (key2715, 6), (key2740, -6), (key2742, -12), (key2818, 6), (key2900, -6)]

def row12515 : Integer.Sparse Key := [(key2428, 12), (key2442, 6), (key2496, -12), (key2508, -12), (key2556, 6)]

def row12516 : Integer.Sparse Key := [(key2428, 12), (key2442, 6), (key2496, -12), (key2508, -12), (key2556, 6)]

def row12517 : Integer.Sparse Key := [(key2428, 12), (key2442, 6), (key2496, -12), (key2508, -12), (key2556, 6)]

def row12518 : Integer.Sparse Key := [(key2428, 12), (key2442, 6), (key2496, -12), (key2508, -12), (key2556, 6)]

def row12519 : Integer.Sparse Key := [(key2429, 12), (key2442, 6), (key2508, 6), (key2550, -12), (key2556, -12)]

def row12520 : Integer.Sparse Key := [(key2429, 12), (key2442, 6), (key2508, 6), (key2550, -12), (key2556, -12)]

def row12521 : Integer.Sparse Key := [(key2429, 12), (key2442, 6), (key2508, 6), (key2550, -12), (key2556, -12)]

def row12522 : Integer.Sparse Key := [(key2429, 12), (key2442, 6), (key2508, 6), (key2550, -12), (key2556, -12)]

def row12523 : Integer.Sparse Key := [(key1499, 18), (key1731, -24), (key1873, 6)]

def row12524 : Integer.Sparse Key := [(key1499, 18), (key1731, -24), (key1873, 6)]

def row12525 : Integer.Sparse Key := [(key1499, 18), (key1731, -24), (key1873, 6)]

def row12526 : Integer.Sparse Key := [(key1499, 18), (key1731, -24), (key1873, 6)]

def row12527 : Integer.Sparse Key := [(key1499, 18), (key1731, 6), (key1873, -24)]

def row12528 : Integer.Sparse Key := [(key1499, 18), (key1731, 6), (key1873, -24)]

def row12529 : Integer.Sparse Key := [(key1499, 18), (key1731, 6), (key1873, -24)]

def row12530 : Integer.Sparse Key := [(key1499, 18), (key1731, 6), (key1873, -24)]

def row12531 : Integer.Sparse Key := [(key3081, 6), (key3082, -6), (key3088, -18), (key3091, 18)]

def row12532 : Integer.Sparse Key := [(key3081, 6), (key3082, -6), (key3088, -18), (key3091, 18)]

def row12533 : Integer.Sparse Key := [(key3081, 6), (key3082, -6), (key3088, -18), (key3091, 18)]

def row12534 : Integer.Sparse Key := [(key3081, 6), (key3082, -6), (key3088, -18), (key3091, 18)]

def row12535 : Integer.Sparse Key := [(key3081, -6), (key3082, 6), (key3086, -18), (key3088, 18)]

def row12536 : Integer.Sparse Key := [(key3081, -6), (key3082, 6), (key3086, -18), (key3088, 18)]

def row12537 : Integer.Sparse Key := [(key3081, -6), (key3082, 6), (key3086, -18), (key3088, 18)]

def row12538 : Integer.Sparse Key := [(key3081, -6), (key3082, 6), (key3086, -18), (key3088, 18)]

def row12539 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12540 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12541 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12542 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12543 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12544 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12545 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12546 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12547 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12548 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12549 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12550 : Integer.Sparse Key := [(key1280, 2), (key1286, -2), (key1703, 2), (key1707, -4), (key1760, -4), (key1856, 4), (key1858, -2), (key1887, 4)]

def row12551 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12552 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12553 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12554 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12555 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12556 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12557 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12558 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12559 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12560 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12561 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12562 : Integer.Sparse Key := [(key1280, -2), (key1286, 2), (key1703, -4), (key1757, -4), (key1760, 2), (key1858, 4), (key1887, -2), (key1890, 4)]

def row12563 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12564 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12565 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12566 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12567 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12568 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12569 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12570 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12571 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12572 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12573 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12574 : Integer.Sparse Key := [(key229, 6), (key501, -18), (key557, 12)]

def row12575 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12576 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12577 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12578 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12579 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12580 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12581 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12582 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12583 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12584 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12585 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12586 : Integer.Sparse Key := [(key229, 6), (key501, 12), (key557, -18)]

def row12587 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12588 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12589 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12590 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12591 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12592 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12593 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12594 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12595 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12596 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12597 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12598 : Integer.Sparse Key := [(key226, 4), (key232, 2), (key498, -8), (key504, -6), (key552, 4), (key562, 4), (key666, -4), (key683, 4)]

def row12599 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12600 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12601 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12602 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12603 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12604 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12605 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12606 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12607 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12608 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12609 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12610 : Integer.Sparse Key := [(key226, 2), (key232, 4), (key498, 4), (key504, 4), (key552, -6), (key562, -8), (key666, 4), (key683, -4)]

def row12611 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12612 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12613 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12614 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12615 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12616 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12617 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12618 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12619 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12620 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12621 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12622 : Integer.Sparse Key := [(key1368, -4), (key1377, 4), (key1494, 2), (key1516, 4), (key1720, -6), (key1726, 4), (key1744, -8), (key1755, 4)]

def row12623 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12624 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12625 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12626 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12627 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12628 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12629 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12630 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12631 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12632 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12633 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12634 : Integer.Sparse Key := [(key1368, 4), (key1377, -4), (key1494, 4), (key1516, 2), (key1720, 4), (key1726, -8), (key1744, 4), (key1755, -6)]

def row12635 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12636 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12637 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12638 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12639 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12640 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12641 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12642 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12643 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12644 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12645 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12646 : Integer.Sparse Key := [(key1279, 4), (key1285, 2), (key1702, -8), (key1708, -6), (key1752, 4), (key1758, 4), (key1935, -4), (key1955, 4)]

def row12647 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12648 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12649 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12650 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12651 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12652 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12653 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12654 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12655 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12656 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12657 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12658 : Integer.Sparse Key := [(key1279, 2), (key1285, 4), (key1702, 4), (key1708, 4), (key1752, -6), (key1758, -8), (key1935, 4), (key1955, -4)]

def row12659 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12660 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12661 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12662 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12663 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12664 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12665 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12666 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12667 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12668 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12669 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12670 : Integer.Sparse Key := [(key1365, -2), (key1371, -2), (key1375, 2), (key1380, 2), (key1491, 2), (key1514, 2), (key1520, 2), (key1717, -4), (key1724, 2), (key1742, -2), (key1748, -4), (key1759, 2), (key1939, -2), (key1942, 2), (key1951, -2), (key1956, 2)]

def row12671 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12672 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12673 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12674 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12675 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12676 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12677 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12678 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12679 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12680 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12681 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12682 : Integer.Sparse Key := [(key1365, 2), (key1371, 2), (key1375, -2), (key1380, -2), (key1491, 2), (key1497, 2), (key1520, 2), (key1717, 2), (key1724, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1939, 2), (key1942, -2), (key1951, 2), (key1956, -2)]

def row12683 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12684 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12685 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12686 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12687 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12688 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12689 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12690 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12691 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12692 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12693 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12694 : Integer.Sparse Key := [(key1282, 6), (key1705, -18), (key1754, 12)]

def row12695 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12696 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12697 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12698 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12699 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12700 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12701 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12702 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12703 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12704 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12705 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12706 : Integer.Sparse Key := [(key1282, 6), (key1705, 12), (key1754, -18)]

def row12707 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12708 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12709 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12710 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12711 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12712 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12713 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12714 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12715 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12716 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12717 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12718 : Integer.Sparse Key := [(key1365, 4), (key1371, 2), (key1491, -4), (key1497, -2), (key1724, -4), (key1729, -4), (key1742, 4), (key1748, 4), (key1942, -4), (key1951, 4)]

def row12719 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12720 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12721 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12722 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12723 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12724 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12725 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12726 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12727 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12728 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12729 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12730 : Integer.Sparse Key := [(key1375, 2), (key1380, 4), (key1514, -2), (key1520, -4), (key1724, 4), (key1729, 4), (key1742, -4), (key1748, -4), (key1942, 4), (key1951, -4)]

def row12731 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12732 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12733 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12734 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12735 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12736 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12737 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12738 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12739 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12740 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12741 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12742 : Integer.Sparse Key := [(key284, -2), (key287, -2), (key293, 2), (key299, 2), (key353, 2), (key370, 2), (key373, 2), (key510, -4), (key521, 2), (key542, -2), (key546, -4), (key563, 2), (key669, -2), (key673, 2), (key679, -2), (key684, 2)]

def row12743 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12744 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12745 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12746 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12747 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12748 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12749 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12750 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12751 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12752 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12753 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12754 : Integer.Sparse Key := [(key284, 2), (key287, 2), (key293, -2), (key299, -2), (key353, 2), (key356, 2), (key373, 2), (key510, 2), (key521, -4), (key526, -2), (key546, 2), (key563, -4), (key669, 2), (key673, -2), (key679, 2), (key684, -2)]

def row12755 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12756 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12757 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12758 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12759 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12760 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12761 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12762 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12763 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12764 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12765 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12766 : Integer.Sparse Key := [(key1365, 2), (key1371, -2), (key1375, 2), (key1380, -2), (key1491, 2), (key1497, -2), (key1514, 2), (key1520, -2), (key1724, 2), (key1729, -4), (key1742, 2), (key1748, -4), (key1759, -2), (key1942, 2), (key1951, 2), (key1956, 2)]

def row12767 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12768 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12769 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12770 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12771 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12772 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12773 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12774 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12775 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12776 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12777 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12778 : Integer.Sparse Key := [(key1365, -2), (key1371, 2), (key1375, -2), (key1380, 2), (key1491, -2), (key1497, 2), (key1514, -2), (key1520, 2), (key1717, -2), (key1724, -4), (key1729, 2), (key1742, -4), (key1748, 2), (key1939, 2), (key1942, 2), (key1951, 2)]

def row12779 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12780 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12781 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12782 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12783 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12784 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12785 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12786 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12787 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12788 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12789 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12790 : Integer.Sparse Key := [(key286, -4), (key297, 4), (key355, 2), (key372, 4), (key512, -6), (key525, 4), (key545, -8), (key558, 4)]

def row12791 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12792 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12793 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12794 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12795 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12796 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12797 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12798 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12799 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12800 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12801 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12802 : Integer.Sparse Key := [(key286, 4), (key297, -4), (key355, 4), (key372, 2), (key512, 4), (key525, -8), (key545, 4), (key558, -6)]

def row12803 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12804 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12805 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12806 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12807 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12808 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12809 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12810 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12811 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12812 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12813 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12814 : Integer.Sparse Key := [(key1285, -6), (key1704, 12), (key1758, -12), (key1857, 6)]

def row12815 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12816 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12817 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12818 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12819 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12820 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12821 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12822 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12823 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12824 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12825 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12826 : Integer.Sparse Key := [(key1281, -6), (key1704, -12), (key1758, 12), (key1888, 6)]

def row12827 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12828 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12829 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12830 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12831 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12832 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12833 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12834 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12835 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12836 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12837 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12838 : Integer.Sparse Key := [(key1285, -6), (key1702, 12), (key1758, -12), (key1935, 6)]

def row12839 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12840 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12841 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12842 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12843 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12844 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12845 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12846 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12847 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12848 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12849 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12850 : Integer.Sparse Key := [(key1279, -6), (key1702, -12), (key1758, 12), (key1955, 6)]

def row12851 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12852 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12853 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12854 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12855 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12856 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12857 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12858 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12859 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12860 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12861 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12862 : Integer.Sparse Key := [(key732, 4), (key734, 2), (key866, -8), (key868, -6), (key882, -4), (key900, 4), (key901, 4), (key913, 4)]

def row12863 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12864 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12865 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12866 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12867 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12868 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12869 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12870 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12871 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12872 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12873 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12874 : Integer.Sparse Key := [(key732, 2), (key734, 4), (key866, 4), (key868, 4), (key882, 4), (key900, -6), (key901, -8), (key913, -4)]

def row12875 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12876 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12877 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12878 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12879 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12880 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12881 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12882 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12883 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12884 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12885 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12886 : Integer.Sparse Key := [(key232, -6), (key498, 12), (key562, -12), (key666, 6)]

def row12887 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12888 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12889 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12890 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12891 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12892 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12893 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12894 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12895 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12896 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12897 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12898 : Integer.Sparse Key := [(key226, -6), (key498, -12), (key562, 12), (key683, 6)]

def row12899 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12900 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12901 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12902 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12903 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12904 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12905 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12906 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12907 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12908 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12909 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12910 : Integer.Sparse Key := [(key1281, 4), (key1285, 2), (key1704, -8), (key1708, -6), (key1753, 4), (key1758, 4), (key1857, -4), (key1888, 4)]

def row12911 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12912 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12913 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12914 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12915 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12916 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12917 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12918 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12919 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12920 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12921 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12922 : Integer.Sparse Key := [(key1281, 2), (key1285, 4), (key1704, 4), (key1708, 4), (key1753, -6), (key1758, -8), (key1857, 4), (key1888, -4)]

def row12923 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12924 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12925 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12926 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12927 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row12928 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12929 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12930 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12931 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12932 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12933 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12934 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

def row12935 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12936 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12937 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12938 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12939 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12940 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12941 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12942 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12943 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12944 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12945 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12946 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

def row12947 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12948 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12949 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12950 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12951 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12952 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12953 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12954 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12955 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12956 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12957 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12958 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

def row12959 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12960 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12961 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12962 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12963 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12964 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12965 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12966 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12967 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12968 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12969 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12970 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

def row12971 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12972 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12973 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12974 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12975 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12976 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12977 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12978 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12979 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12980 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12981 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12982 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

def row12983 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12984 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12985 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12986 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12987 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12988 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12989 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12990 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12991 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12992 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12993 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12994 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

def row12995 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row12996 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row12997 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row12998 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row12999 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13000 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13001 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13002 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13003 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13004 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13005 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13006 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

def row13007 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13008 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13009 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13010 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13011 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13012 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13013 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13014 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13015 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13016 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13017 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13018 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

def row13019 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13020 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13021 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13022 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13023 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13024 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13025 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13026 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13027 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13028 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13029 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13030 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

def row13031 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13032 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13033 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13034 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13035 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13036 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13037 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13038 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13039 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13040 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13041 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13042 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

def row13043 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13044 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13045 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13046 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13047 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13048 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13049 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13050 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13051 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13052 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13053 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13054 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

def row13055 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13056 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13057 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13058 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13059 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13060 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13061 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13062 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13063 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13064 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13065 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13066 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

def row13067 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13068 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13069 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13070 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13071 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13072 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13073 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13074 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13075 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13076 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13077 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13078 : Integer.Sparse Key := [(key1367, -2), (key1371, -2), (key1376, 2), (key1380, 2), (key1493, 2), (key1515, 2), (key1520, 2), (key1719, -4), (key1725, 2), (key1743, -2), (key1748, -4), (key1759, 2), (key1866, -2), (key1871, 2), (key1881, -2), (key1889, 2)]

def row13079 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13080 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13081 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13082 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13083 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13084 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13085 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13086 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13087 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13088 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13089 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13090 : Integer.Sparse Key := [(key1367, 2), (key1371, 2), (key1376, -2), (key1380, -2), (key1493, 2), (key1497, 2), (key1520, 2), (key1719, 2), (key1725, -4), (key1729, -2), (key1748, 2), (key1759, -4), (key1866, 2), (key1871, -2), (key1881, 2), (key1889, -2)]

def row13091 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13092 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13093 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13094 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13095 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13096 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13097 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13098 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13099 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13100 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13101 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13102 : Integer.Sparse Key := [(key1280, 2), (key1284, 4), (key1703, -2), (key1707, -8), (key1757, 4), (key1856, -4), (key1858, -4), (key1887, 4), (key1890, 4)]

def row13103 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13104 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13105 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13106 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13107 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13108 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13109 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13110 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13111 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13112 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13113 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13114 : Integer.Sparse Key := [(key1284, 4), (key1286, 2), (key1707, 4), (key1757, -8), (key1760, -2), (key1856, 4), (key1858, 4), (key1887, -4), (key1890, -4)]

def row13115 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13116 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13117 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13118 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13119 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13120 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13121 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13122 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13123 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13124 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13125 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13126 : Integer.Sparse Key := [(key296, 6), (key524, -18), (key555, 12)]

def row13127 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13128 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13129 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13130 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13131 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13132 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13133 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13134 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13135 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13136 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13137 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13138 : Integer.Sparse Key := [(key296, 6), (key524, 12), (key555, -18)]

def row13139 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13140 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13141 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13142 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13143 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13144 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13145 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13146 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13147 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13148 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13149 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13150 : Integer.Sparse Key := [(key1508, 12), (key1510, -12), (key1749, -6), (key1882, 6)]

def row13151 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13152 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13153 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13154 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13155 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13156 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13157 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13158 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13159 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13160 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13161 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13162 : Integer.Sparse Key := [(key1508, -12), (key1510, 12), (key1737, -6), (key1876, 6)]

def row13163 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

def row13164 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

def row13165 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

def row13166 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 4), (key561, -4), (key632, -2), (key647, 4)]

def row13167 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 4), (key561, -4), (key632, -2), (key647, 4)]

def row13168 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 4), (key561, -4), (key632, -2), (key647, 4)]

def row13169 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

def row13170 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

def row13171 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 2), (key561, -4), (key631, 2), (key632, -2), (key647, 4)]

def row13172 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key553, 2), (key561, -4), (key631, 2), (key632, -2), (key647, 4)]

def row13173 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

def row13174 : Integer.Sparse Key := [(key291, 2), (key298, -2), (key518, 2), (key522, -4), (key561, -4), (key631, 4), (key632, -2), (key647, 4)]

def row13175 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

def row13176 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

def row13177 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

def row13178 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -2), (key561, 4), (key631, -2), (key632, 2), (key647, -2), (key650, 4)]

def row13179 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -2), (key561, 4), (key631, -2), (key632, 2), (key647, -2), (key650, 4)]

def row13180 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -4), (key561, 4), (key632, 2), (key647, -2), (key650, 4)]

def row13181 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -4), (key561, 4), (key632, 2), (key647, -2), (key650, 4)]

def row13182 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -2), (key561, 4), (key631, -2), (key632, 2), (key647, -2), (key650, 4)]

def row13183 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key553, -2), (key561, 4), (key631, -2), (key632, 2), (key647, -2), (key650, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13184 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

def row13185 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

def row13186 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7372 : Integer.Sparse Key := [(key1088, 24), (key1178, -24)]

def row7373 : Integer.Sparse Key := [(key1088, -6), (key1178, 6)]

def row7374 : Integer.Sparse Key := [(key1088, -6), (key1178, 6)]

def row7375 : Integer.Sparse Key := [(key1088, -6), (key1178, 6)]

def row7376 : Integer.Sparse Key := [(key1088, -6), (key1178, 6)]

def row7377 : Integer.Sparse Key := [(key0, -24), (key83, 24)]

def row7378 : Integer.Sparse Key := [(key0, 6), (key83, -6)]

def row7379 : Integer.Sparse Key := [(key0, 6), (key83, -6)]

def row7380 : Integer.Sparse Key := [(key0, 6), (key83, -6)]

def row7381 : Integer.Sparse Key := [(key0, 6), (key83, -6)]

def row7386 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7387 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7388 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7389 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7390 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7391 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7392 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7393 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7394 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7395 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7396 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7397 : Integer.Sparse Key := [(key976, 2), (key984, -2), (key1098, -4), (key1169, -2), (key1180, 4), (key1220, 2)]

def row7402 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7403 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7404 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7405 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7406 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7407 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7408 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7409 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7410 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7411 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7412 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7413 : Integer.Sparse Key := [(key3, 6), (key86, -12), (key147, 6)]

def row7418 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

def row7419 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

def row7420 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

def row7421 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key193, 2), (key202, 2)]

def row7422 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key193, 2), (key202, 2)]

def row7423 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, 2), (key202, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7424 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, 2), (key202, 2)]

def row7425 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key193, 2), (key202, 2)]

def row7426 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key193, 2), (key202, 2)]

def row7427 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

def row7428 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

def row7429 : Integer.Sparse Key := [(key1, 2), (key7, 4), (key84, -2), (key90, -8), (key151, -2), (key193, 4), (key202, 2)]

def row7434 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7435 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7436 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7437 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7438 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7439 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7440 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7441 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7442 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7443 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7444 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7445 : Integer.Sparse Key := [(key2377, -2), (key2389, 2), (key2405, -2), (key2436, 2), (key2471, -4), (key2518, 4)]

def row7450 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7451 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7452 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7453 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7454 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7455 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7456 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7457 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7458 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7459 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7460 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7461 : Integer.Sparse Key := [(key989, 6), (key1024, 6), (key1102, -12)]

def row7466 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7467 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7468 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7469 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7470 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7471 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7472 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7473 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7474 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7475 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7476 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7477 : Integer.Sparse Key := [(key995, 4), (key1011, 2), (key1030, 4), (key1067, 2), (key1108, -8), (key1119, -2), (key1146, -2)]

def row7482 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

def row7483 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

def row7484 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

def row7485 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, 2), (key2799, 4), (key2849, -8)]

def row7486 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, 2), (key2799, 4), (key2849, -8)]

def row7487 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, 2), (key2799, 4), (key2849, -8)]

def row7488 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

def row7489 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

def row7490 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2776, 2), (key2799, 4), (key2849, -8)]

def row7491 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2776, 2), (key2799, 4), (key2849, -8)]

def row7492 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

def row7493 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, 2), (key2696, -2), (key2776, 4), (key2799, 4), (key2849, -8)]

def row7498 : Integer.Sparse Key := [(key2357, 2), (key2363, -2), (key2458, -4), (key2519, -2), (key2528, 4), (key2560, 2)]

def row7499 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2458, -4), (key2519, -2), (key2528, 4), (key2560, 2)]

def row7500 : Integer.Sparse Key := [(key2357, -2), (key2361, 4), (key2363, -4), (key2366, 2), (key2458, -4), (key2519, -2), (key2528, 4), (key2560, 2)]

def row7501 : Integer.Sparse Key := [(key2357, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 2), (key2519, -2), (key2523, 2), (key2528, 2), (key2530, -2), (key2560, 2)]

def row7502 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 2), (key2519, -2), (key2523, 2), (key2528, 2), (key2530, -2), (key2560, 2)]

def row7503 : Integer.Sparse Key := [(key2357, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 4), (key2519, -2), (key2523, 2), (key2530, -2), (key2560, 2)]

def row7504 : Integer.Sparse Key := [(key2357, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 4), (key2519, -2), (key2523, 2), (key2530, -2), (key2560, 2)]

def row7505 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 4), (key2519, -2), (key2523, 2), (key2530, -2), (key2579, 2)]

def row7506 : Integer.Sparse Key := [(key2361, 2), (key2363, -2), (key2452, -2), (key2456, 2), (key2458, -4), (key2517, 4), (key2519, -2), (key2523, 2), (key2530, -2), (key2579, 2)]

def row7507 : Integer.Sparse Key := [(key2357, -2), (key2361, 4), (key2363, -4), (key2366, 2), (key2452, -4), (key2456, 4), (key2458, -4), (key2517, 4), (key2519, -4), (key2523, 4), (key2530, -4), (key2560, -2), (key2567, 2), (key2579, 4)]

def row7508 : Integer.Sparse Key := [(key2357, -2), (key2361, 4), (key2363, -4), (key2366, 2), (key2452, -4), (key2456, 4), (key2458, -4), (key2517, 4), (key2519, -4), (key2523, 4), (key2530, -4), (key2560, -2), (key2567, 2), (key2579, 4)]

def row7509 : Integer.Sparse Key := [(key2357, -2), (key2361, 4), (key2363, -4), (key2366, 2), (key2452, -4), (key2456, 4), (key2458, -4), (key2517, 4), (key2519, -4), (key2523, 4), (key2530, -4), (key2560, -2), (key2567, 2), (key2579, 4)]

def row7514 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7515 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7516 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7517 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7518 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7519 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7520 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7521 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7522 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7523 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7524 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7525 : Integer.Sparse Key := [(key970, 6), (key1084, -12), (key1226, 6)]

def row7530 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7531 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7532 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7533 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7534 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7535 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7536 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7537 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7538 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7539 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7540 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7541 : Integer.Sparse Key := [(key971, 2), (key979, 4), (key1085, -2), (key1093, -8), (key1164, -2), (key1228, 4), (key1245, 2)]

def row7546 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7547 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7548 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7549 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7550 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7551 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7552 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7553 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7554 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7555 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7556 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7557 : Integer.Sparse Key := [(key2372, -2), (key2385, 2), (key2400, 4), (key2432, 2), (key2466, -8), (key2475, 4), (key2498, -2)]

def row7562 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

def row7563 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

def row7564 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

def row7565 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2566, 2), (key2578, 2)]

def row7566 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2566, 2), (key2578, 2)]

def row7567 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, 2), (key2578, 2)]

def row7568 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, 2), (key2578, 2)]

def row7569 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2566, 2), (key2578, 2)]

def row7570 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2566, 2), (key2578, 2)]

def row7571 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

def row7572 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

def row7573 : Integer.Sparse Key := [(key2353, 2), (key2359, 4), (key2448, -2), (key2454, -8), (key2515, -2), (key2566, 4), (key2578, 2)]

def row7574 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7575 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7576 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7577 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7578 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7579 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7580 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7581 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7582 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7583 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7584 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7585 : Integer.Sparse Key := [(key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2843, 4), (key2880, 2), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, 4), (key2968, 4), (key2989, 4), (key2995, -4), (key3002, -2)]

def row7586 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7587 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7588 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7589 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7590 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7591 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7592 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7593 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7594 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7595 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7596 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7597 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7598 : Integer.Sparse Key := [(key2390, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2593, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2929, 2), (key2968, -2), (key3002, 2)]

def row7599 : Integer.Sparse Key := [(key2390, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2593, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2929, 2), (key2968, -2), (key3002, 2)]

def row7600 : Integer.Sparse Key := [(key2437, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2593, -2), (key2598, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2968, -2), (key3002, 2)]

def row7601 : Integer.Sparse Key := [(key2437, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2593, -2), (key2598, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2968, -2), (key3002, 2)]

def row7602 : Integer.Sparse Key := [(key2390, 2), (key2437, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2580, 2), (key2593, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2968, -2)]

def row7603 : Integer.Sparse Key := [(key2390, 2), (key2437, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2580, 2), (key2593, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2968, -2)]

def row7604 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row7605 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row7606 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row7607 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row7608 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row7609 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row7610 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7611 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7612 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7613 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7614 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7615 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7616 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7617 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7618 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7619 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7620 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7621 : Integer.Sparse Key := [(key991, 6), (key1026, -24), (key1104, 12), (key1230, 6)]

def row7622 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7623 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7624 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7625 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7626 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7627 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7628 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7629 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7630 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7631 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7632 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7633 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7634 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7635 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7636 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7637 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7638 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7639 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7640 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7641 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7642 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7643 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7644 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7645 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, -18), (key1230, 6)]

def row7646 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7647 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7648 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7649 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7650 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7651 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7652 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7653 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7654 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7655 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7656 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7657 : Integer.Sparse Key := [(key993, 2), (key1001, 4), (key1028, -6), (key1036, -12), (key1071, -6), (key1106, 4), (key1114, 4), (key1150, 4), (key1232, 4), (key1242, 2)]

def row7658 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7659 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7660 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7661 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7662 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7663 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7664 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7665 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7666 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7667 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7668 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7669 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7670 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7671 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7672 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7673 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7674 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7675 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7676 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7677 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7678 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7679 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7680 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7681 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1071, 2), (key1106, -4), (key1114, -6), (key1123, -4), (key1150, -4), (key1232, 2), (key1235, 2), (key1242, 2)]

def row7682 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7683 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7684 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7685 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7686 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7687 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7688 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7689 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7690 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7691 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7692 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7693 : Integer.Sparse Key := [(key2610, -6), (key2626, 4), (key2635, 2), (key2700, 4), (key2721, 2), (key2803, -12), (key2824, -6), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7694 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7695 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7696 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7697 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7698 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7699 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7700 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7701 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7702 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7703 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7704 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7705 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7706 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7707 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7708 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7709 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7710 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7711 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7712 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7713 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7714 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7715 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7716 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7717 : Integer.Sparse Key := [(key2610, 2), (key2626, -4), (key2635, 2), (key2665, 2), (key2700, 2), (key2721, 2), (key2780, -4), (key2789, 2), (key2803, 2), (key2824, 2), (key2853, -6), (key2855, 2), (key2865, -4)]

def row7718 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7719 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7720 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7721 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7722 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7723 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7724 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7725 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7726 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7727 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7728 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7729 : Integer.Sparse Key := [(key2398, -6), (key2404, -12), (key2435, -6), (key2583, 2), (key2589, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key3019, 4), (key3028, 2)]

def row7730 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

def row7731 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

def row7732 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

def row7733 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

def row7734 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

def row7735 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, 2), (key3019, 2), (key3028, 2)]

def row7736 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

def row7737 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

def row7738 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

def row7739 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

def row7740 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

def row7741 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -6), (key2501, -6), (key2583, 2), (key2589, 2), (key2604, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3019, 2), (key3028, 2)]

def row7742 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2589, 2), (key2762, 2), (key2768, 2), (key2876, 2), (key2925, 2), (key3005, 2), (key3028, 2)]

def row7743 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2589, 2), (key2762, 2), (key2768, 2), (key2876, 2), (key2925, 2), (key3005, 2), (key3028, 2)]

def row7744 : Integer.Sparse Key := [(key2398, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2583, 2), (key2589, 2), (key2604, 2), (key2768, 2), (key2876, 2), (key2925, 2), (key3028, 2)]

def row7745 : Integer.Sparse Key := [(key2398, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2583, 2), (key2589, 2), (key2604, 2), (key2768, 2), (key2876, 2), (key2925, 2), (key3028, 2)]

def row7746 : Integer.Sparse Key := [(key2370, 2), (key2388, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2570, 2), (key2575, 2), (key2589, 2), (key2762, 2), (key2768, 2), (key2876, 2)]

def row7747 : Integer.Sparse Key := [(key2388, 2), (key2398, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2570, 2), (key2575, 2), (key2583, 2), (key2589, 2), (key2768, 2), (key2876, 2)]

def row7748 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2762, 2), (key2839, 2)]

def row7749 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2762, 2), (key2839, 2)]

def row7750 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, 2), (key2839, 2)]

def row7751 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, 2), (key2404, 2), (key2435, 2), (key2464, -6), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, 2), (key2839, 2)]

def row7752 : Integer.Sparse Key := [(key2370, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2762, 2)]

def row7753 : Integer.Sparse Key := [(key2376, 2), (key2388, 2), (key2398, 2), (key2404, 2), (key2435, 2), (key2464, -4), (key2470, -6), (key2478, -4), (key2501, -4), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, 2)]

def row7754 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7755 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7756 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7757 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -6), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7758 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -6), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7759 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -8), (key2851, 2), (key2858, 2), (key2868, 2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7760 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -8), (key2851, 2), (key2858, 2), (key2868, 2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7761 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -6), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7762 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -6), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7763 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7764 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7765 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7766 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7767 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7768 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7769 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7770 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7771 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7772 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7773 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7774 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7775 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7776 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7777 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7778 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 1), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7779 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 1), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7780 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 2), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7781 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 2), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7782 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 1), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7783 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 1), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7784 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7785 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7786 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7787 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7788 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7789 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7790 : Integer.Sparse Key := [(key2455, 24), (key2516, -24)]

def row7791 : Integer.Sparse Key := [(key2455, -6), (key2516, 6)]

def row7792 : Integer.Sparse Key := [(key2455, -6), (key2516, 6)]

def row7793 : Integer.Sparse Key := [(key2455, -6), (key2516, 6)]

def row7794 : Integer.Sparse Key := [(key2455, -6), (key2516, 6)]

def row7795 : Integer.Sparse Key := [(key968, -24), (key1082, 24)]

def row7796 : Integer.Sparse Key := [(key968, 6), (key1082, -6)]

def row7797 : Integer.Sparse Key := [(key968, 6), (key1082, -6)]

def row7798 : Integer.Sparse Key := [(key968, 6), (key1082, -6)]

def row7799 : Integer.Sparse Key := [(key968, 6), (key1082, -6)]

def row7800 : Integer.Sparse Key := [(key973, -24), (key1087, 24)]

def row7801 : Integer.Sparse Key := [(key973, 6), (key1087, -6)]

def row7802 : Integer.Sparse Key := [(key973, 6), (key1087, -6)]

def row7803 : Integer.Sparse Key := [(key973, 6), (key1087, -6)]

def row7804 : Integer.Sparse Key := [(key973, 6), (key1087, -6)]

def row7805 : Integer.Sparse Key := [(key2396, -24), (key2462, 24)]

def row7806 : Integer.Sparse Key := [(key2368, 6), (key2396, 6), (key2462, 12), (key2581, -6), (key2837, -18)]

def row7807 : Integer.Sparse Key := [(key2368, 4), (key2396, 4), (key2462, 4), (key2581, -4), (key2760, 2), (key2837, -10)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7808 : Integer.Sparse Key := [(key2368, 2), (key2396, 2), (key2581, -2), (key2760, 4), (key2837, -6)]

def row7809 : Integer.Sparse Key := [(key2760, 6), (key2837, -6)]

def row7810 : Integer.Sparse Key := [(key2355, -24), (key2450, 24)]

def row7811 : Integer.Sparse Key := [(key2355, 6), (key2450, -6)]

def row7812 : Integer.Sparse Key := [(key2355, 6), (key2450, -6)]

def row7813 : Integer.Sparse Key := [(key2355, 6), (key2450, -6)]

def row7814 : Integer.Sparse Key := [(key2355, 6), (key2450, -6)]

def row7815 : Integer.Sparse Key := [(key2764, -24), (key2841, 24)]

def row7816 : Integer.Sparse Key := [(key2764, 6), (key2841, -6)]

def row7817 : Integer.Sparse Key := [(key2764, 6), (key2841, -6)]

def row7818 : Integer.Sparse Key := [(key2764, 6), (key2841, -6)]

def row7819 : Integer.Sparse Key := [(key2764, 6), (key2841, -6)]

def row7820 : Integer.Sparse Key := [(key2351, -24), (key2446, 24)]

def row7821 : Integer.Sparse Key := [(key2351, 6), (key2446, -6)]

def row7822 : Integer.Sparse Key := [(key2351, 6), (key2446, -6)]

def row7823 : Integer.Sparse Key := [(key2351, 6), (key2446, -6)]

def row7824 : Integer.Sparse Key := [(key2351, 6), (key2446, -6)]

def row7825 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7826 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7827 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7828 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7829 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7830 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7831 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7832 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7833 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7834 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7835 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7836 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7837 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7838 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7839 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7840 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7841 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7842 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7843 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7844 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7845 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7846 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7847 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7848 : Integer.Sparse Key := [(key991, -24), (key1026, 6), (key1104, 12), (key1230, 6)]

def row7849 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7850 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7851 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7852 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7853 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7854 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7855 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7856 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7857 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7858 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7859 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7860 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 2), (key1036, 4), (key1106, 4), (key1114, 4), (key1123, 4), (key1232, 4), (key1235, 2)]

def row7861 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7862 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7863 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7864 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7865 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7866 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7867 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7868 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7869 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7870 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7871 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7872 : Integer.Sparse Key := [(key2665, -6), (key2700, -12), (key2721, -6), (key2780, 4), (key2789, 2), (key2803, 4), (key2824, 2), (key2853, 4), (key2855, 4), (key2865, 4)]

def row7873 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7874 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7875 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7876 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7877 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7878 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7879 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7880 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7881 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7882 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7883 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7884 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2762, 2), (key2768, 4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, 4), (key2925, 2)]

def row7885 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7886 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7887 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7888 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7889 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7890 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7891 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7892 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7893 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7894 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7895 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7896 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7897 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7898 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7899 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7900 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7901 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7902 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7903 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7904 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7905 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7906 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7907 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7908 : Integer.Sparse Key := [(key2585, -24), (key2764, 6), (key2841, 12), (key2873, 6)]

def row7909 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7910 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7911 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7912 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7913 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7914 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7915 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7916 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7917 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7918 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7919 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7920 : Integer.Sparse Key := [(key2585, 6), (key2764, -24), (key2841, 12), (key2873, 6)]

def row7921 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7922 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7923 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7924 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -6), (key2657, -2), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7925 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -6), (key2657, -2), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7926 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -8), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7927 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -8), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7928 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -6), (key2657, -2), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7929 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -6), (key2657, -2), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7930 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7931 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7932 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7933 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

def row7934 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

def row7935 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7936 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 6), (key3011, 2), (key3016, 2)]

def row7937 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 6), (key3011, 2), (key3016, 2)]

def row7938 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 8), (key3016, 2)]

def row7939 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 8), (key3016, 2)]

def row7940 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 6), (key3011, 2), (key3016, 2)]

def row7941 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 6), (key3011, 2), (key3016, 2)]

def row7942 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

def row7943 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

def row7944 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

def row7945 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7946 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7947 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7948 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7949 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7950 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7951 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7952 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7953 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7954 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7955 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7956 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7957 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7958 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7959 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7960 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7961 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7962 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7963 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7964 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7965 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7966 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7967 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7968 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7969 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7970 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7971 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7972 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7973 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7974 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7975 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7976 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7977 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7978 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7979 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7980 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7981 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7982 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7983 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7984 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7985 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7986 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7987 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7988 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7989 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7990 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7991 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7992 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

def row7993 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row7994 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row7995 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row7996 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row7997 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row7998 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row7999 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8000 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8001 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8002 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8003 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8004 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8005 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8006 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8007 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8008 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8009 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8010 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8011 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8012 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8013 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8014 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8015 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8016 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

def row8017 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8018 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8019 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8020 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8021 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8022 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8023 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8024 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8025 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8026 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8027 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8028 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

def row8029 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

def row8030 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

def row8031 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

def row8032 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

def row8033 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

def row8034 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

def row8035 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

def row8036 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

def row8037 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

def row8038 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

def row8039 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

def row8040 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

def row8041 : Integer.Sparse Key := [(key18, 2), (key35, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key212, 2), (key375, 2), (key381, 2), (key460, 2), (key490, 2), (key654, 2), (key663, 2)]

def row8042 : Integer.Sparse Key := [(key18, 2), (key35, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key212, 2), (key375, 2), (key381, 2), (key460, 2), (key490, 2), (key654, 2), (key663, 2)]

def row8043 : Integer.Sparse Key := [(key43, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key206, 2), (key212, 2), (key218, 2), (key381, 2), (key460, 2), (key490, 2), (key663, 2)]

def row8044 : Integer.Sparse Key := [(key43, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key206, 2), (key212, 2), (key218, 2), (key381, 2), (key460, 2), (key490, 2), (key663, 2)]

def row8045 : Integer.Sparse Key := [(key18, 2), (key35, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key196, 2), (key200, 2), (key212, 2), (key375, 2), (key381, 2), (key460, 2)]

def row8046 : Integer.Sparse Key := [(key35, 2), (key43, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key196, 2), (key200, 2), (key206, 2), (key212, 2), (key381, 2), (key460, 2)]

def row8047 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key375, 2), (key426, 2)]

def row8048 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key375, 2), (key426, 2)]

def row8049 : Integer.Sparse Key := [(key23, 2), (key35, 2), (key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key206, 2), (key426, 2)]

def row8050 : Integer.Sparse Key := [(key23, 2), (key35, 2), (key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key206, 2), (key426, 2)]

def row8051 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key48, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key375, 2)]

def row8052 : Integer.Sparse Key := [(key23, 2), (key35, 2), (key43, 2), (key48, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key206, 2)]

def row8053 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8161 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

end MUB6.Certificate.GramRows

end OAI
end


