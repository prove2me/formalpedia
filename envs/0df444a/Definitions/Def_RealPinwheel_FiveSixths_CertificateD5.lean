-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_CertificateD5
-- name    : RealPinwheel_FiveSixths_CertificateD5
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T03:54:46.301212+00:00
-- url     : https://prove2.me/theorems/4c497759-b788-4f24-8fb6-665d7393b036
-- title:
--   Five-sixths certificate words D5
-- statement:
--   This array stores the 216 explicit words and rational density-box annotations of certificate family D5.
--
--   $$|W|=216,\qquad\max_{w\in W}|w|=32.$$
--
--   These are finite data; validity and coverage require separate proofs.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Exact data: https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D5.txt

import Definitions.Def_RealPinwheel_FiveSixths_CycleCode

namespace RealPinwheel.FiveSixths

set_option maxRecDepth 100000
set_option maxHeartbeats 0
def certificateD5_0 : CycleCode := { word := "AABAABACAABAABADAABAABACAABAABAE", num := #[5, 1, 1, 1, 1], den := #[8, 4, 16, 32, 32], strict := #[false, true, false, false, false] }
def certificateD5_1 : CycleCode := { word := "AABABACBAABABADBAABABACBAABABAEB", num := #[1, 3, 1, 1, 1], den := #[2, 8, 16, 32, 32], strict := #[true, false, false, false, false] }
def certificateD5_2 : CycleCode := { word := "AAAABAAACAABAAADAAABAAACAAABAAE", num := #[17, 4, 2, 1, 1], den := #[23, 31, 31, 31, 31], strict := #[true, false, false, false, false] }
def certificateD5_3 : CycleCode := { word := "AAAABAAAACAAAABAAAADAAAABAAAAE", num := #[4, 1, 1, 1, 1], den := #[5, 10, 30, 30, 30], strict := #[false, false, false, false, false] }
def certificateD5_4 : CycleCode := { word := "AABAABACABAABAABADABAABAABAEAB", num := #[3, 3, 1, 1, 1], den := #[5, 10, 30, 30, 30], strict := #[true, false, false, false, false] }
def certificateD5_5 : CycleCode := { word := "AABABAEABABACABABAABADABABACAB", num := #[8, 1, 1, 1, 1], den := #[15, 3, 15, 30, 30], strict := #[true, true, false, false, false] }
def certificateD5_6 : CycleCode := { word := "AABABCABADABACBAABABCABAEABACB", num := #[5, 1, 2, 1, 1], den := #[11, 3, 15, 30, 30], strict := #[true, true, false, false, false] }
def certificateD5_7 : CycleCode := { word := "AABACABADABACABAABACABAEABACAB", num := #[8, 4, 2, 1, 1], den := #[15, 15, 15, 30, 30], strict := #[false, false, false, false, false] }
def certificateD5_8 : CycleCode := { word := "AABAEACABADABACAABAEADABACABAD", num := #[8, 1, 2, 2, 1], den := #[15, 5, 21, 21, 15], strict := #[false, true, true, true, false] }
def certificateD5_9 : CycleCode := { word := "AABCADBABCABACBAABCAEBABCABACB", num := #[3, 1, 1, 1, 1], den := #[8, 3, 5, 30, 30], strict := #[true, true, true, false, false] }
def certificateD5_10 : CycleCode := { word := "AAABAACAAABAADAAABAACAAABAAE", num := #[5, 1, 1, 1, 1], den := #[7, 7, 14, 28, 28], strict := #[false, false, false, false, false] }
def certificateD5_11 : CycleCode := { word := "AABAACAABACAADAABAACAABACAAE", num := #[9, 1, 1, 1, 1], den := #[14, 7, 8, 28, 28], strict := #[false, true, true, false, false] }
def certificateD5_12 : CycleCode := { word := "AABACAABADACABAABACAABAEACAB", num := #[4, 1, 1, 1, 1], den := #[7, 5, 7, 28, 28], strict := #[true, true, false, false, false] }
def certificateD5_13 : CycleCode := { word := "AABACABAABADABAABACABAABAEAB", num := #[4, 2, 1, 1, 1], den := #[7, 7, 14, 28, 28], strict := #[false, false, false, false, false] }
def certificateD5_14 : CycleCode := { word := "AABACABACADBACAABACABACAEBAC", num := #[1, 3, 3, 1, 1], den := #[2, 14, 14, 28, 28], strict := #[true, false, false, false, false] }
def certificateD5_15 : CycleCode := { word := "ABABABCABABABDABABABCABABABE", num := #[3, 3, 1, 1, 1], den := #[7, 7, 14, 28, 28], strict := #[false, false, false, false, false] }
def certificateD5_16 : CycleCode := { word := "ABABCABDABEABCABABDABCABEABD", num := #[5, 5, 1, 1, 1], den := #[14, 14, 10, 10, 14], strict := #[false, false, true, true, false] }
def certificateD5_17 : CycleCode := { word := "ABACABACBADABCABACABACBAEABC", num := #[3, 2, 1, 1, 1], den := #[7, 7, 5, 28, 28], strict := #[true, false, true, false, false] }
def certificateD5_18 : CycleCode := { word := "ABACABDACABBACABACABEACABBAC", num := #[3, 1, 3, 1, 1], den := #[7, 4, 14, 28, 28], strict := #[true, true, false, false, false] }
def certificateD5_19 : CycleCode := { word := "AAABAACABAAABADAABAAABAAEAB", num := #[2, 2, 1, 1, 1], den := #[3, 9, 27, 27, 27], strict := #[true, false, false, false, false] }
def certificateD5_20 : CycleCode := { word := "AABABACADABACAABABACAEABAC", num := #[7, 1, 2, 1, 1], den := #[13, 5, 13, 26, 26], strict := #[false, true, false, false, false] }
def certificateD5_21 : CycleCode := { word := "AABACAADABAACAABACAAEABAAC", num := #[8, 2, 1, 1, 1], den := #[13, 13, 7, 26, 26], strict := #[false, false, true, false, false] }
def certificateD5_22 : CycleCode := { word := "AABCABDACBABCAABCABEACBABC", num := #[4, 3, 3, 1, 1], den := #[11, 10, 13, 26, 26], strict := #[true, true, false, false, false] }
def certificateD5_23 : CycleCode := { word := "ABABCABADBACBABABCABAEBACB", num := #[5, 3, 2, 1, 1], den := #[13, 8, 13, 26, 26], strict := #[false, true, false, false, false] }
def certificateD5_24 : CycleCode := { word := "ABABCADBACABCABABCAEBACABC", num := #[5, 2, 2, 1, 1], den := #[13, 7, 9, 26, 26], strict := #[false, true, true, false, false] }
def certificateD5_25 : CycleCode := { word := "ABACABACABACDABACABACABACE", num := #[6, 3, 3, 1, 1], den := #[13, 13, 13, 26, 26], strict := #[false, false, false, false, false] }
def certificateD5_26 : CycleCode := { word := "ABACDABAECADBACABDACAEBADC", num := #[5, 4, 4, 2, 1], den := #[13, 21, 21, 13, 13], strict := #[false, true, true, false, false] }
def certificateD5_27 : CycleCode := { word := "ABCABCABCABCDABCABCABCABCE", num := #[4, 4, 4, 1, 1], den := #[13, 13, 13, 26, 26], strict := #[false, false, false, false, false] }
def certificateD5_28 : CycleCode := { word := "AABABDABABAABCABABABABAEB", num := #[6, 7, 1, 1, 1], den := #[13, 18, 25, 25, 25], strict := #[true, true, false, false, false] }
def certificateD5_29 : CycleCode := { word := "AACABADAACABAEABAADACABAE", num := #[14, 3, 1, 2, 1], den := #[25, 20, 10, 25, 13], strict := #[false, true, true, false, true] }
def certificateD5_30 : CycleCode := { word := "AAAAABAAAAACAAAAADAAAAAE", num := #[5, 1, 1, 1, 1], den := #[6, 24, 24, 24, 24], strict := #[false, false, false, false, false] }
def certificateD5_31 : CycleCode := { word := "AABAACAABAADAABAACAABAAE", num := #[2, 1, 1, 1, 1], den := #[3, 6, 12, 24, 24], strict := #[false, false, false, false, false] }
def certificateD5_32 : CycleCode := { word := "AABABEABABABACBABABADBAB", num := #[4, 5, 1, 1, 1], den := #[9, 12, 24, 24, 24], strict := #[true, true, false, false, false] }
def certificateD5_33 : CycleCode := { word := "AABACAABADABAABACAABAEAB", num := #[7, 1, 1, 1, 1], den := #[12, 4, 12, 24, 24], strict := #[false, true, false, false, false] }
def certificateD5_34 : CycleCode := { word := "AABACABADACBAABACABAEACB", num := #[1, 1, 1, 1, 1], den := #[2, 4, 6, 24, 24], strict := #[true, true, false, false, false] }
def certificateD5_35 : CycleCode := { word := "AABACBAABADBAABACBAABAEB", num := #[1, 1, 1, 1, 1], den := #[2, 3, 12, 24, 24], strict := #[true, false, false, false, false] }
def certificateD5_36 : CycleCode := { word := "AABCABABEABACBABABCABADB", num := #[9, 4, 2, 1, 1], den := #[22, 11, 17, 24, 24], strict := #[true, true, true, false, false] }
def certificateD5_37 : CycleCode := { word := "AABCADBACABCAABCAEBACABC", num := #[2, 1, 1, 1, 1], den := #[5, 4, 4, 24, 24], strict := #[true, false, true, false, false] }
def certificateD5_38 : CycleCode := { word := "AACABAADACABAACABAAEACAB", num := #[7, 1, 1, 1, 1], den := #[12, 6, 6, 24, 24], strict := #[false, true, true, false, false] }
def certificateD5_39 : CycleCode := { word := "ABABACBADABCABABACBAEABC", num := #[5, 1, 1, 1, 1], den := #[12, 3, 6, 24, 24], strict := #[false, true, false, false, false] }
def certificateD5_40 : CycleCode := { word := "ABACABADAEACABADABACAEAD", num := #[1, 1, 1, 1, 1], den := #[2, 7, 8, 8, 12], strict := #[false, true, false, false, false] }
def certificateD5_41 : CycleCode := { word := "ABCABCABDACBABCABCABEACB", num := #[1, 1, 1, 1, 1], den := #[3, 3, 4, 24, 24], strict := #[false, true, true, false, false] }
def certificateD5_42 : CycleCode := { word := "AAABAADAABAAAEAABAACAAB", num := #[16, 1, 1, 1, 1], den := #[23, 6, 23, 23, 23], strict := #[false, true, false, false, false] }
def certificateD5_43 : CycleCode := { word := "AABAADAABACAABAAEAABAC", num := #[7, 2, 1, 1, 1], den := #[11, 11, 11, 22, 22], strict := #[false, false, false, false, false] }
def certificateD5_44 : CycleCode := { word := "AABACADABACAABACAEABAC", num := #[6, 2, 2, 1, 1], den := #[11, 11, 11, 22, 22], strict := #[false, false, false, false, false] }
def certificateD5_45 : CycleCode := { word := "AABDABABACBAABEABABACB", num := #[4, 4, 1, 1, 1], den := #[9, 11, 11, 22, 22], strict := #[true, false, false, false, false] }
def certificateD5_46 : CycleCode := { word := "AADABACABAAEABADABACAB", num := #[6, 5, 1, 1, 1], den := #[11, 22, 12, 12, 22], strict := #[true, false, true, true, false] }
def certificateD5_47 : CycleCode := { word := "ABABACABADCABABACABAEC", num := #[5, 1, 2, 1, 1], den := #[11, 4, 11, 22, 22], strict := #[false, true, false, false, false] }
def certificateD5_48 : CycleCode := { word := "ABABCABDABCABABCABEABC", num := #[4, 4, 2, 1, 1], den := #[11, 11, 11, 22, 22], strict := #[false, false, false, false, false] }
def certificateD5_49 : CycleCode := { word := "ABACABACBADABACABACBAE", num := #[5, 3, 1, 1, 1], den := #[11, 11, 6, 22, 22], strict := #[false, false, true, false, false] }
def certificateD5_50 : CycleCode := { word := "ABCABCADBACABCABCAEBAC", num := #[4, 3, 1, 1, 1], den := #[11, 11, 4, 22, 22], strict := #[false, false, true, false, false] }
def certificateD5_51 : CycleCode := { word := "AACABADAAEABACAADABAE", num := #[4, 1, 2, 2, 2], den := #[7, 7, 21, 21, 21], strict := #[false, false, false, false, false] }
def certificateD5_52 : CycleCode := { word := "ABADBACABADBACABAEBAC", num := #[3, 2, 1, 1, 1], den := #[7, 7, 7, 13, 21], strict := #[false, false, false, true, false] }
def certificateD5_53 : CycleCode := { word := "AAABAADAACAAABAAEAAC", num := #[7, 1, 1, 1, 1], den := #[10, 10, 10, 20, 20], strict := #[false, false, false, false, false] }
def certificateD5_54 : CycleCode := { word := "AABADABACBAABAEABACB", num := #[1, 3, 1, 1, 1], den := #[2, 10, 10, 20, 20], strict := #[true, false, false, false, false] }
def certificateD5_55 : CycleCode := { word := "AABCADBACEABACABDACB", num := #[3, 1, 1, 1, 1], den := #[8, 4, 5, 10, 20], strict := #[true, true, false, true, false] }
def certificateD5_56 : CycleCode := { word := "AACABAADABAACABAAEAB", num := #[3, 1, 1, 1, 1], den := #[5, 5, 10, 20, 20], strict := #[false, false, false, false, false] }
def certificateD5_57 : CycleCode := { word := "ABABCABABDABABCABABE", num := #[2, 2, 1, 1, 1], den := #[5, 5, 10, 20, 20], strict := #[false, false, false, false, false] }
def certificateD5_58 : CycleCode := { word := "ABACBADABCABACBAEABC", num := #[2, 3, 1, 1, 1], den := #[5, 10, 5, 20, 20], strict := #[false, false, true, false, false] }
def certificateD5_59 : CycleCode := { word := "ABCAEADBACABDAEACBAD", num := #[2, 1, 3, 3, 1], den := #[5, 5, 20, 20, 10], strict := #[false, true, false, false, false] }
def certificateD5_60 : CycleCode := { word := "AAADACAABADAAEAACAB", num := #[5, 2, 1, 1, 1], den := #[8, 19, 10, 11, 19], strict := #[true, false, true, true, false] }
def certificateD5_61 : CycleCode := { word := "AAEACABACADABACADAB", num := #[10, 3, 1, 1, 1], den := #[19, 19, 8, 12, 19], strict := #[false, false, true, true, false] }
def certificateD5_62 : CycleCode := { word := "ABACABDABCABEABCADB", num := #[5, 5, 3, 1, 1], den := #[14, 16, 19, 10, 19], strict := #[true, true, false, true, false] }
def certificateD5_63 : CycleCode := { word := "AAABAADACAAABAAEAC", num := #[2, 1, 1, 1, 1], den := #[3, 9, 9, 18, 18], strict := #[true, false, false, false, false] }
def certificateD5_64 : CycleCode := { word := "AABACABADAEBACABAD", num := #[1, 2, 1, 1, 1], den := #[2, 9, 9, 9, 18], strict := #[true, false, false, false, false] }
def certificateD5_65 : CycleCode := { word := "AABACADABAACABAEAC", num := #[5, 1, 1, 1, 1], den := #[9, 6, 6, 18, 18], strict := #[false, true, true, false, false] }
def certificateD5_66 : CycleCode := { word := "AABACADABACAEABDAC", num := #[1, 1, 1, 1, 1], den := #[2, 6, 6, 9, 18], strict := #[true, false, true, false, false] }
def certificateD5_67 : CycleCode := { word := "AABACBADABAEBACABD", num := #[3, 5, 1, 1, 1], den := #[7, 18, 9, 9, 18], strict := #[true, false, true, true, false] }
def certificateD5_68 : CycleCode := { word := "AABADABACAABAEABAC", num := #[5, 2, 1, 1, 1], den := #[9, 9, 9, 18, 18], strict := #[false, false, false, false, false] }
def certificateD5_69 : CycleCode := { word := "AABCADBACABCABEACB", num := #[3, 5, 3, 1, 1], den := #[8, 18, 14, 18, 18], strict := #[true, false, true, false, false] }
def certificateD5_70 : CycleCode := { word := "AABDABACBAABEABACB", num := #[3, 1, 1, 1, 1], den := #[7, 3, 9, 18, 18], strict := #[true, false, false, false, false] }
def certificateD5_71 : CycleCode := { word := "AABDABCAEBACABDABC", num := #[3, 5, 1, 1, 1], den := #[8, 18, 6, 10, 18], strict := #[true, false, true, true, false] }
def certificateD5_72 : CycleCode := { word := "AACABAADABACAEABAD", num := #[6, 1, 1, 1, 1], den := #[11, 6, 9, 9, 18], strict := #[true, true, false, true, false] }
def certificateD5_73 : CycleCode := { word := "ABABACABABADABABAE", num := #[1, 1, 1, 1, 1], den := #[2, 3, 18, 18, 18], strict := #[false, true, false, false, false] }
def certificateD5_74 : CycleCode := { word := "ABABCAEBABADBACABD", num := #[7, 1, 1, 1, 1], den := #[18, 3, 9, 11, 18], strict := #[false, true, true, true, false] }
def certificateD5_75 : CycleCode := { word := "ABACABDACABACABEAC", num := #[4, 2, 2, 1, 1], den := #[9, 9, 9, 18, 18], strict := #[false, false, false, false, false] }
def certificateD5_76 : CycleCode := { word := "ABACADBACABADABCAE", num := #[4, 2, 1, 1, 1], den := #[9, 9, 6, 10, 18], strict := #[false, true, true, true, false] }
def certificateD5_77 : CycleCode := { word := "ABACDBACABDACEBADC", num := #[1, 2, 2, 1, 1], den := #[3, 9, 9, 6, 18], strict := #[true, true, true, false, false] }
def certificateD5_78 : CycleCode := { word := "ABACDBACBACABECABC", num := #[1, 5, 5, 1, 1], den := #[3, 18, 18, 18, 18], strict := #[true, false, false, false, false] }
def certificateD5_79 : CycleCode := { word := "ABADABBACABADABEAC", num := #[4, 1, 1, 1, 1], den := #[9, 4, 9, 9, 18], strict := #[false, true, false, false, false] }
def certificateD5_80 : CycleCode := { word := "ABADABCAEBACABDABC", num := #[5, 3, 1, 1, 1], den := #[13, 11, 6, 10, 18], strict := #[true, true, true, true, false] }
def certificateD5_81 : CycleCode := { word := "ABCABDACBABCABEACB", num := #[1, 1, 2, 1, 1], den := #[3, 3, 9, 18, 18], strict := #[false, true, false, false, false] }
def certificateD5_82 : CycleCode := { word := "ABCACBDACBEABCADBC", num := #[5, 5, 1, 1, 1], den := #[18, 18, 4, 9, 18], strict := #[false, false, true, false, false] }
def certificateD5_83 : CycleCode := { word := "ABCADBACBACABDACBE", num := #[1, 5, 3, 1, 1], den := #[3, 18, 14, 9, 18], strict := #[true, false, true, false, false] }
def certificateD5_84 : CycleCode := { word := "ABCADBACEABDACBADE", num := #[1, 2, 1, 1, 1], den := #[3, 9, 6, 6, 9], strict := #[false, false, true, true, false] }
def certificateD5_85 : CycleCode := { word := "ABCADBAECBADBACABD", num := #[1, 5, 1, 1, 1], den := #[3, 18, 6, 6, 18], strict := #[true, false, false, true, false] }
def certificateD5_86 : CycleCode := { word := "ABCDABECABDACBADCB", num := #[3, 4, 2, 1, 1], den := #[11, 15, 9, 6, 18], strict := #[true, true, true, true, false] }
def certificateD5_87 : CycleCode := { word := "ABDACABEACABDACBAC", num := #[7, 2, 3, 1, 1], den := #[18, 9, 14, 9, 18], strict := #[false, true, true, true, false] }
def certificateD5_88 : CycleCode := { word := "AAAABAAACAAADAAAE", num := #[13, 1, 1, 1, 1], den := #[17, 17, 17, 17, 17], strict := #[false, false, false, false, false] }
def certificateD5_89 : CycleCode := { word := "AABACADABAEACABAD", num := #[9, 3, 2, 1, 1], den := #[17, 17, 17, 9, 17], strict := #[false, false, false, true, false] }
def certificateD5_90 : CycleCode := { word := "AABACADBACABAEABC", num := #[5, 4, 1, 1, 1], den := #[11, 17, 6, 17, 17], strict := #[true, false, true, false, false] }
def certificateD5_91 : CycleCode := { word := "AABADAACAEABAADAC", num := #[10, 2, 2, 1, 1], den := #[17, 17, 17, 9, 17], strict := #[false, false, false, true, false] }
def certificateD5_92 : CycleCode := { word := "AABCABDACBACBAEBC", num := #[1, 5, 3, 1, 1], den := #[3, 17, 13, 17, 17], strict := #[true, false, true, false, false] }
def certificateD5_93 : CycleCode := { word := "AABCABDACBAEBACDB", num := #[1, 5, 3, 2, 1], den := #[3, 17, 17, 17, 17], strict := #[true, false, false, false, false] }
def certificateD5_94 : CycleCode := { word := "AABDABACABAEABACB", num := #[7, 2, 2, 1, 1], den := #[15, 7, 17, 17, 17], strict := #[true, true, false, false, false] }
def certificateD5_95 : CycleCode := { word := "AABDACABEACBADABC", num := #[2, 4, 3, 1, 1], den := #[5, 17, 17, 9, 17], strict := #[true, false, false, true, false] }
def certificateD5_96 : CycleCode := { word := "ABABACDABAECABADC", num := #[7, 3, 3, 2, 1], den := #[17, 14, 17, 17, 17], strict := #[false, true, false, false, false] }
def certificateD5_97 : CycleCode := { word := "ABABCABDABEACBABD", num := #[6, 1, 2, 2, 1], den := #[17, 3, 17, 17, 17], strict := #[false, true, false, false, false] }
def certificateD5_98 : CycleCode := { word := "ABACABADABACABEAD", num := #[8, 4, 2, 2, 1], den := #[17, 17, 17, 17, 17], strict := #[false, false, false, false, false] }
def certificateD5_99 : CycleCode := { word := "ABACADABACAEBADAC", num := #[8, 3, 1, 2, 1], den := #[17, 17, 6, 17, 17], strict := #[false, false, true, false, false] }
def certificateD5_100 : CycleCode := { word := "ABACBAEACBADABCAD", num := #[7, 3, 3, 1, 1], den := #[17, 13, 17, 11, 17], strict := #[false, true, false, true, false] }
def certificateD5_101 : CycleCode := { word := "ABADBACABDABAEBAC", num := #[7, 5, 1, 1, 1], den := #[17, 17, 9, 10, 17], strict := #[false, false, true, true, false] }
def certificateD5_102 : CycleCode := { word := "ABCABDABCDABEACBD", num := #[5, 2, 3, 1, 1], den := #[17, 7, 17, 6, 17], strict := #[false, true, false, true, false] }
def certificateD5_103 : CycleCode := { word := "ABCABDACBAEABCADB", num := #[6, 3, 3, 1, 1], den := #[17, 11, 17, 9, 17], strict := #[false, true, false, true, false] }
def certificateD5_104 : CycleCode := { word := "ABCABDACEBADCBACD", num := #[2, 3, 2, 3, 1], den := #[7, 13, 9, 17, 17], strict := #[true, true, true, false, false] }
def certificateD5_105 : CycleCode := { word := "ABCADBACABDACBACE", num := #[6, 4, 2, 1, 1], den := #[17, 17, 9, 10, 17], strict := #[false, false, true, true, false] }
def certificateD5_106 : CycleCode := { word := "ABCADBACEABDACBAD", num := #[6, 4, 3, 1, 1], den := #[17, 17, 17, 6, 17], strict := #[false, false, false, true, false] }
def certificateD5_107 : CycleCode := { word := "ABCADBCABEACBDACB", num := #[5, 2, 4, 2, 1], den := #[17, 7, 17, 17, 17], strict := #[false, true, false, false, false] }
def certificateD5_108 : CycleCode := { word := "ABCDABCDABCDABCDE", num := #[4, 4, 4, 4, 1], den := #[17, 17, 17, 17, 17], strict := #[false, false, false, false, false] }
def certificateD5_109 : CycleCode := { word := "AAABAAACAAADAAAE", num := #[3, 1, 1, 1, 1], den := #[4, 16, 16, 16, 16], strict := #[false, false, false, false, false] }
def certificateD5_110 : CycleCode := { word := "AABABDABACBABAEB", num := #[5, 3, 1, 1, 1], den := #[12, 8, 16, 16, 16], strict := #[true, false, false, false, false] }
def certificateD5_111 : CycleCode := { word := "AABACADABAEACBAD", num := #[1, 3, 1, 1, 1], den := #[2, 16, 8, 8, 16], strict := #[true, false, false, true, false] }
def certificateD5_112 : CycleCode := { word := "AABACADBAACABAEC", num := #[1, 3, 3, 1, 1], den := #[2, 16, 16, 16, 16], strict := #[true, false, false, false, false] }
def certificateD5_113 : CycleCode := { word := "AABCADBACBABEACB", num := #[5, 3, 3, 1, 1], den := #[14, 10, 16, 16, 16], strict := #[true, true, false, false, false] }
def certificateD5_114 : CycleCode := { word := "AABDACABACDABAEC", num := #[3, 3, 2, 1, 1], den := #[7, 16, 11, 8, 16], strict := #[true, false, true, true, false] }
def certificateD5_115 : CycleCode := { word := "AACBADABCABAECAB", num := #[5, 1, 3, 1, 1], den := #[12, 4, 16, 16, 16], strict := #[true, true, false, false, false] }
def certificateD5_116 : CycleCode := { word := "AACBAEADABCAEABD", num := #[3, 3, 1, 1, 1], den := #[7, 16, 8, 8, 8], strict := #[true, false, false, false, true] }
def certificateD5_117 : CycleCode := { word := "AADBABACABEABACB", num := #[3, 4, 1, 1, 1], den := #[7, 13, 8, 16, 16], strict := #[true, true, true, false, false] }
def certificateD5_118 : CycleCode := { word := "ABACABADABACABAE", num := #[1, 1, 1, 1, 1], den := #[2, 4, 8, 16, 16], strict := #[false, false, false, false, false] }
def certificateD5_119 : CycleCode := { word := "ABACBABDABACBABE", num := #[3, 3, 1, 1, 1], den := #[8, 8, 8, 16, 16], strict := #[false, false, false, false, false] }
def certificateD5_120 : CycleCode := { word := "ABACBADABAECABAD", num := #[7, 1, 1, 1, 1], den := #[16, 4, 8, 8, 16], strict := #[false, true, false, true, false] }
def certificateD5_121 : CycleCode := { word := "ABACBADACBAEBACD", num := #[3, 1, 3, 1, 1], den := #[8, 4, 16, 8, 16], strict := #[true, true, false, true, false] }
def certificateD5_122 : CycleCode := { word := "ABACBAEBADABCABD", num := #[3, 5, 1, 1, 1], den := #[8, 16, 8, 9, 16], strict := #[false, false, true, true, false] }
def certificateD5_123 : CycleCode := { word := "ABADCAEBACADBAEC", num := #[3, 3, 3, 1, 1], den := #[8, 16, 16, 8, 8], strict := #[false, false, false, false, false] }
def certificateD5_124 : CycleCode := { word := "ABCABCADBACBACBE", num := #[5, 5, 1, 1, 1], den := #[16, 16, 4, 16, 16], strict := #[false, false, true, false, false] }
def certificateD5_125 : CycleCode := { word := "ABCABCADBCAEBACD", num := #[5, 1, 1, 1, 1], den := #[16, 4, 4, 8, 16], strict := #[false, true, true, false, false] }
def certificateD5_126 : CycleCode := { word := "ABCABDABCABDACBE", num := #[5, 5, 3, 1, 1], den := #[16, 16, 16, 9, 16], strict := #[false, false, false, true, false] }
def certificateD5_127 : CycleCode := { word := "ABCABDAEBACBADBE", num := #[5, 5, 1, 1, 1], den := #[16, 16, 8, 8, 8], strict := #[false, false, false, false, false] }
def certificateD5_128 : CycleCode := { word := "ABCABDEACBADBCAD", num := #[3, 1, 3, 2, 1], den := #[10, 4, 16, 11, 16], strict := #[true, true, false, true, false] }
def certificateD5_129 : CycleCode := { word := "ABCAEBADCABEACBD", num := #[5, 1, 3, 1, 1], den := #[16, 4, 16, 8, 8], strict := #[false, true, false, false, true] }
def certificateD5_130 : CycleCode := { word := "ABCDABCEADBCABDC", num := #[1, 1, 1, 3, 1], den := #[4, 4, 4, 16, 16], strict := #[false, true, true, false, false] }
def certificateD5_131 : CycleCode := { word := "ABCEADBCABDEACBD", num := #[1, 1, 3, 3, 1], den := #[4, 4, 16, 16, 8], strict := #[false, true, false, false, false] }
def certificateD5_132 : CycleCode := { word := "ABDACBACABEACBAC", num := #[3, 1, 1, 1, 1], den := #[8, 4, 4, 16, 16], strict := #[false, false, true, false, false] }
def certificateD5_133 : CycleCode := { word := "AABACAADABAACAE", num := #[3, 2, 2, 1, 1], den := #[5, 15, 15, 15, 15], strict := #[false, false, false, false, false] }
def certificateD5_134 : CycleCode := { word := "AABACADBAEACABD", num := #[4, 1, 2, 2, 1], den := #[9, 5, 15, 15, 15], strict := #[true, true, false, false, false] }
def certificateD5_135 : CycleCode := { word := "AABADABACABAEAB", num := #[8, 4, 1, 1, 1], den := #[15, 15, 15, 15, 15], strict := #[false, false, false, false, false] }
def certificateD5_136 : CycleCode := { word := "AABCABAEABACABD", num := #[6, 4, 2, 1, 1], den := #[13, 15, 15, 15, 15], strict := #[true, false, false, false, false] }
def certificateD5_137 : CycleCode := { word := "AACABADABACAEAB", num := #[8, 1, 2, 1, 1], den := #[15, 5, 15, 15, 15], strict := #[false, true, false, false, false] }
def certificateD5_138 : CycleCode := { word := "AACABADAEACABAD", num := #[8, 2, 2, 2, 1], den := #[15, 15, 15, 15, 15], strict := #[false, false, false, false, false] }
def certificateD5_139 : CycleCode := { word := "ABABCABABDABABE", num := #[2, 2, 1, 1, 1], den := #[5, 5, 15, 15, 15], strict := #[false, false, false, false, false] }
def certificateD5_140 : CycleCode := { word := "ABACABDACBACABE", num := #[2, 4, 1, 1, 1], den := #[5, 15, 6, 15, 15], strict := #[true, false, true, false, false] }
def certificateD5_141 : CycleCode := { word := "ABACADABAECABAD", num := #[7, 1, 2, 1, 1], den := #[15, 5, 15, 8, 15], strict := #[false, true, false, true, false] }
def certificateD5_142 : CycleCode := { word := "ABACADBACAEBADC", num := #[2, 1, 1, 2, 1], den := #[5, 5, 5, 15, 15], strict := #[true, false, true, false, false] }
def certificateD5_143 : CycleCode := { word := "ABADABCAEBADABC", num := #[2, 4, 2, 2, 1], den := #[5, 15, 15, 15, 15], strict := #[true, false, false, false, false] }
def certificateD5_144 : CycleCode := { word := "ABADCABDACEBADC", num := #[1, 1, 1, 1, 1], den := #[3, 5, 5, 5, 15], strict := #[true, false, false, true, false] }
def certificateD5_145 : CycleCode := { word := "ABCABDABEACBADB", num := #[1, 1, 2, 2, 1], den := #[3, 3, 15, 15, 15], strict := #[false, true, false, false, false] }
def certificateD5_146 : CycleCode := { word := "ABCABDCABECABDC", num := #[4, 4, 4, 2, 1], den := #[15, 15, 15, 15, 15], strict := #[false, false, false, false, false] }
def certificateD5_147 : CycleCode := { word := "ABCADBACABDACBE", num := #[1, 4, 1, 1, 1], den := #[3, 15, 5, 8, 15], strict := #[true, false, false, true, false] }
def certificateD5_148 : CycleCode := { word := "ABCADBACEABDACB", num := #[1, 1, 1, 2, 1], den := #[3, 4, 5, 15, 15], strict := #[false, true, true, false, false] }
def certificateD5_149 : CycleCode := { word := "ABCDABECABDACBE", num := #[4, 4, 1, 2, 2], den := #[15, 15, 5, 15, 15], strict := #[false, false, false, false, false] }
def certificateD5_150 : CycleCode := { word := "ABCDABECADBACBD", num := #[4, 1, 1, 1, 1], den := #[15, 4, 5, 5, 15], strict := #[false, true, false, true, false] }
def certificateD5_151 : CycleCode := { word := "AAABAADAAACAAE", num := #[5, 1, 1, 1, 1], den := #[7, 14, 14, 14, 14], strict := #[false, false, false, false, false] }
def certificateD5_152 : CycleCode := { word := "AABAACAEAABAAD", num := #[9, 1, 1, 1, 1], den := #[14, 7, 14, 14, 14], strict := #[false, true, false, false, false] }
def certificateD5_153 : CycleCode := { word := "AABACAEABAABAD", num := #[4, 1, 1, 1, 1], den := #[7, 5, 14, 14, 14], strict := #[true, true, false, false, false] }
def certificateD5_154 : CycleCode := { word := "AADABACAAEABAC", num := #[4, 1, 1, 1, 1], den := #[7, 7, 7, 14, 14], strict := #[false, false, false, false, false] }
def certificateD5_155 : CycleCode := { word := "AADABACABAEACB", num := #[1, 3, 1, 1, 1], den := #[2, 14, 7, 14, 14], strict := #[true, false, true, false, false] }
def certificateD5_156 : CycleCode := { word := "ABACAEBACABADC", num := #[3, 3, 3, 1, 1], den := #[7, 14, 14, 14, 14], strict := #[false, false, false, false, false] }
def certificateD5_157 : CycleCode := { word := "ABACBADCABBACE", num := #[5, 1, 3, 1, 1], den := #[14, 4, 14, 14, 14], strict := #[false, true, false, false, false] }
def certificateD5_158 : CycleCode := { word := "ABADBACAEABDAC", num := #[3, 1, 1, 1, 1], den := #[7, 5, 7, 7, 14], strict := #[false, true, false, true, false] }
def certificateD5_159 : CycleCode := { word := "ABADBACBABEABC", num := #[5, 5, 1, 1, 1], den := #[14, 14, 7, 14, 14], strict := #[false, false, false, false, false] }
def certificateD5_160 : CycleCode := { word := "ABCABCADBACBAE", num := #[5, 2, 1, 1, 1], den := #[14, 7, 5, 14, 14], strict := #[false, false, true, false, false] }
def certificateD5_161 : CycleCode := { word := "ABCABCDABCABCE", num := #[2, 2, 2, 1, 1], den := #[7, 7, 7, 14, 14], strict := #[false, false, false, false, false] }
def certificateD5_162 : CycleCode := { word := "ABCABDAEBACBAD", num := #[5, 2, 1, 1, 1], den := #[14, 7, 7, 7, 14], strict := #[false, false, true, true, false] }
def certificateD5_163 : CycleCode := { word := "ABCADABEACBADE", num := #[5, 3, 1, 1, 1], den := #[14, 14, 7, 7, 7], strict := #[false, false, false, true, true] }
def certificateD5_164 : CycleCode := { word := "ABCADBACEABDAC", num := #[5, 3, 1, 1, 1], den := #[14, 14, 5, 7, 14], strict := #[false, false, true, false, false] }
def certificateD5_165 : CycleCode := { word := "ABCDABECABDACB", num := #[2, 3, 3, 1, 1], den := #[7, 11, 14, 7, 14], strict := #[true, true, false, false, false] }
def certificateD5_166 : CycleCode := { word := "ABCDABECDABCDE", num := #[3, 3, 3, 3, 1], den := #[14, 14, 14, 14, 7], strict := #[false, false, false, false, false] }
def certificateD5_167 : CycleCode := { word := "ABDACEBADCABDC", num := #[2, 3, 3, 1, 1], den := #[7, 14, 14, 5, 14], strict := #[false, false, false, true, false] }
def certificateD5_168 : CycleCode := { word := "ABDCAEBACDBAEC", num := #[2, 3, 3, 1, 1], den := #[7, 14, 14, 7, 7], strict := #[false, false, false, false, false] }
def certificateD5_169 : CycleCode := { word := "AABACADABACAE", num := #[7, 2, 2, 1, 1], den := #[13, 13, 13, 13, 13], strict := #[false, false, false, false, false] }
def certificateD5_170 : CycleCode := { word := "AABACBADABAEB", num := #[4, 4, 1, 1, 1], den := #[9, 13, 13, 13, 13], strict := #[true, false, false, false, false] }
def certificateD5_171 : CycleCode := { word := "AABADAACABAAE", num := #[8, 2, 1, 1, 1], den := #[13, 13, 13, 13, 13], strict := #[false, false, false, false, false] }
def certificateD5_172 : CycleCode := { word := "ABABDABACBAEB", num := #[5, 3, 1, 1, 1], den := #[13, 8, 13, 13, 13], strict := #[false, true, false, false, false] }
def certificateD5_173 : CycleCode := { word := "ABACABADABCAE", num := #[6, 3, 2, 1, 1], den := #[13, 13, 13, 13, 13], strict := #[false, false, false, false, false] }
def certificateD5_174 : CycleCode := { word := "ABACADAEBACAD", num := #[6, 2, 2, 2, 1], den := #[13, 13, 13, 13, 13], strict := #[false, false, false, false, false] }
def certificateD5_175 : CycleCode := { word := "ABACDBAECABDC", num := #[3, 3, 3, 2, 1], den := #[10, 13, 13, 13, 13], strict := #[true, false, false, false, false] }
def certificateD5_176 : CycleCode := { word := "ABADBACABEABC", num := #[5, 4, 2, 1, 1], den := #[13, 13, 13, 13, 13], strict := #[false, false, false, false, false] }
def certificateD5_177 : CycleCode := { word := "ABCABDABECABD", num := #[4, 4, 2, 2, 1], den := #[13, 13, 13, 13, 13], strict := #[false, false, false, false, false] }
def certificateD5_178 : CycleCode := { word := "ABCABDACBABCE", num := #[4, 3, 3, 1, 1], den := #[13, 10, 13, 13, 13], strict := #[false, true, false, false, false] }
def certificateD5_179 : CycleCode := { word := "ABCADABEACBAD", num := #[5, 3, 2, 1, 1], den := #[13, 13, 13, 7, 13], strict := #[false, false, false, true, false] }
def certificateD5_180 : CycleCode := { word := "ABCADBACEABDC", num := #[4, 3, 2, 2, 1], den := #[13, 13, 9, 13, 13], strict := #[false, false, true, false, false] }
def certificateD5_181 : CycleCode := { word := "ABEACBDAEBACD", num := #[4, 3, 2, 2, 2], den := #[13, 13, 13, 13, 13], strict := #[false, false, false, false, false] }
def certificateD5_182 : CycleCode := { word := "ACBDAEBCCADBE", num := #[3, 3, 2, 2, 2], den := #[13, 13, 11, 13, 13], strict := #[false, false, true, false, false] }
def certificateD5_183 : CycleCode := { word := "AABAACAADAAE", num := #[2, 1, 1, 1, 1], den := #[3, 12, 12, 12, 12], strict := #[false, false, false, false, false] }
def certificateD5_184 : CycleCode := { word := "AABDACBAEABC", num := #[2, 1, 1, 1, 1], den := #[5, 4, 6, 12, 12], strict := #[true, false, false, false, false] }
def certificateD5_185 : CycleCode := { word := "AACAEABAADAB", num := #[7, 1, 1, 1, 1], den := #[12, 6, 12, 12, 12], strict := #[false, true, false, false, false] }
def certificateD5_186 : CycleCode := { word := "ABABADBACABE", num := #[5, 1, 1, 1, 1], den := #[12, 3, 12, 12, 12], strict := #[false, true, false, false, false] }
def certificateD5_187 : CycleCode := { word := "ABACABADABAE", num := #[1, 1, 1, 1, 1], den := #[2, 4, 12, 12, 12], strict := #[false, false, false, false, false] }
def certificateD5_188 : CycleCode := { word := "ABACABDAEABC", num := #[5, 1, 1, 1, 1], den := #[12, 4, 7, 12, 12], strict := #[false, true, true, false, false] }
def certificateD5_189 : CycleCode := { word := "ABCABDABCABE", num := #[1, 1, 1, 1, 1], den := #[3, 3, 6, 12, 12], strict := #[false, false, false, false, false] }
def certificateD5_190 : CycleCode := { word := "ABCABDACBACE", num := #[1, 1, 1, 1, 1], den := #[3, 4, 4, 12, 12], strict := #[false, true, true, false, false] }
def certificateD5_191 : CycleCode := { word := "ABCADBAECBAD", num := #[1, 1, 1, 1, 1], den := #[3, 4, 6, 6, 12], strict := #[true, false, false, true, false] }
def certificateD5_192 : CycleCode := { word := "ABCAEADBACAD", num := #[5, 1, 1, 1, 1], den := #[12, 6, 6, 6, 12], strict := #[false, false, true, true, false] }
def certificateD5_193 : CycleCode := { word := "ABCDABCEADBC", num := #[1, 1, 1, 1, 1], den := #[4, 4, 4, 6, 12], strict := #[false, true, true, false, false] }
def certificateD5_194 : CycleCode := { word := "ACBDAEBCADBE", num := #[1, 1, 1, 1, 1], den := #[4, 4, 6, 6, 6], strict := #[false, false, false, false, false] }
def certificateD5_195 : CycleCode := { word := "ABABDABCABE", num := #[4, 4, 1, 1, 1], den := #[11, 11, 11, 11, 11], strict := #[false, false, false, false, false] }
def certificateD5_196 : CycleCode := { word := "ABACABADABE", num := #[5, 3, 1, 1, 1], den := #[11, 11, 11, 11, 11], strict := #[false, false, false, false, false] }
def certificateD5_197 : CycleCode := { word := "ABACADBACAE", num := #[5, 2, 2, 1, 1], den := #[11, 11, 11, 11, 11], strict := #[false, false, false, false, false] }
def certificateD5_198 : CycleCode := { word := "ABCABDACBAE", num := #[4, 3, 2, 1, 1], den := #[11, 11, 11, 11, 11], strict := #[false, false, false, false, false] }
def certificateD5_199 : CycleCode := { word := "ABCABDCABCE", num := #[3, 3, 3, 1, 1], den := #[11, 11, 11, 11, 11], strict := #[false, false, false, false, false] }
def certificateD5_200 : CycleCode := { word := "ABCADABCAED", num := #[4, 2, 2, 2, 1], den := #[11, 11, 11, 11, 11], strict := #[false, false, false, false, false] }
def certificateD5_201 : CycleCode := { word := "ABEACDBAECD", num := #[3, 2, 2, 2, 2], den := #[11, 11, 11, 11, 11], strict := #[false, false, false, false, false] }
def certificateD5_202 : CycleCode := { word := "ABAEBACABD", num := #[2, 3, 1, 1, 1], den := #[5, 10, 10, 10, 10], strict := #[false, false, false, false, false] }
def certificateD5_203 : CycleCode := { word := "ABCADBACBE", num := #[3, 3, 1, 1, 1], den := #[10, 10, 5, 10, 10], strict := #[false, false, false, false, false] }
def certificateD5_204 : CycleCode := { word := "ABDACEBADC", num := #[3, 1, 1, 1, 1], den := #[10, 5, 5, 5, 10], strict := #[false, false, false, true, false] }
def certificateD5_205 : CycleCode := { word := "ABACDABAE", num := #[4, 2, 1, 1, 1], den := #[9, 9, 9, 9, 9], strict := #[false, false, false, false, false] }
def certificateD5_206 : CycleCode := { word := "ABCABDABE", num := #[1, 1, 1, 1, 1], den := #[3, 3, 9, 9, 9], strict := #[false, false, false, false, false] }
def certificateD5_207 : CycleCode := { word := "ABCADBACE", num := #[1, 2, 2, 1, 1], den := #[3, 9, 9, 9, 9], strict := #[false, false, false, false, false] }
def certificateD5_208 : CycleCode := { word := "ADBCAEDBC", num := #[2, 2, 2, 2, 1], den := #[9, 9, 9, 9, 9], strict := #[false, false, false, false, false] }
def certificateD5_209 : CycleCode := { word := "ABACADAE", num := #[1, 1, 1, 1, 1], den := #[2, 8, 8, 8, 8], strict := #[false, false, false, false, false] }
def certificateD5_210 : CycleCode := { word := "ABCADBAE", num := #[3, 1, 1, 1, 1], den := #[8, 4, 8, 8, 8], strict := #[false, false, false, false, false] }
def certificateD5_211 : CycleCode := { word := "ABCDABCE", num := #[1, 1, 1, 1, 1], den := #[4, 4, 4, 8, 8], strict := #[false, false, false, false, false] }
def certificateD5_212 : CycleCode := { word := "ABAECAD", num := #[3, 1, 1, 1, 1], den := #[7, 7, 7, 7, 7], strict := #[false, false, false, false, false] }
def certificateD5_213 : CycleCode := { word := "ABDACBE", num := #[2, 2, 1, 1, 1], den := #[7, 7, 7, 7, 7], strict := #[false, false, false, false, false] }
def certificateD5_214 : CycleCode := { word := "ABCADE", num := #[1, 1, 1, 1, 1], den := #[3, 6, 6, 6, 6], strict := #[false, false, false, false, false] }
def certificateD5_215 : CycleCode := { word := "AEBCD", num := #[1, 1, 1, 1, 1], den := #[5, 5, 5, 5, 5], strict := #[false, false, false, false, false] }

def certificateD5 : Array CycleCode := #[certificateD5_0, certificateD5_1, certificateD5_2, certificateD5_3, certificateD5_4, certificateD5_5, certificateD5_6, certificateD5_7, certificateD5_8, certificateD5_9, certificateD5_10, certificateD5_11, certificateD5_12, certificateD5_13, certificateD5_14, certificateD5_15, certificateD5_16, certificateD5_17, certificateD5_18, certificateD5_19, certificateD5_20, certificateD5_21, certificateD5_22, certificateD5_23, certificateD5_24, certificateD5_25, certificateD5_26, certificateD5_27, certificateD5_28, certificateD5_29, certificateD5_30, certificateD5_31, certificateD5_32, certificateD5_33, certificateD5_34, certificateD5_35, certificateD5_36, certificateD5_37, certificateD5_38, certificateD5_39, certificateD5_40, certificateD5_41, certificateD5_42, certificateD5_43, certificateD5_44, certificateD5_45, certificateD5_46, certificateD5_47, certificateD5_48, certificateD5_49, certificateD5_50, certificateD5_51, certificateD5_52, certificateD5_53, certificateD5_54, certificateD5_55, certificateD5_56, certificateD5_57, certificateD5_58, certificateD5_59, certificateD5_60, certificateD5_61, certificateD5_62, certificateD5_63, certificateD5_64, certificateD5_65, certificateD5_66, certificateD5_67, certificateD5_68, certificateD5_69, certificateD5_70, certificateD5_71, certificateD5_72, certificateD5_73, certificateD5_74, certificateD5_75, certificateD5_76, certificateD5_77, certificateD5_78, certificateD5_79, certificateD5_80, certificateD5_81, certificateD5_82, certificateD5_83, certificateD5_84, certificateD5_85, certificateD5_86, certificateD5_87, certificateD5_88, certificateD5_89, certificateD5_90, certificateD5_91, certificateD5_92, certificateD5_93, certificateD5_94, certificateD5_95, certificateD5_96, certificateD5_97, certificateD5_98, certificateD5_99, certificateD5_100, certificateD5_101, certificateD5_102, certificateD5_103, certificateD5_104, certificateD5_105, certificateD5_106, certificateD5_107, certificateD5_108, certificateD5_109, certificateD5_110, certificateD5_111, certificateD5_112, certificateD5_113, certificateD5_114, certificateD5_115, certificateD5_116, certificateD5_117, certificateD5_118, certificateD5_119, certificateD5_120, certificateD5_121, certificateD5_122, certificateD5_123, certificateD5_124, certificateD5_125, certificateD5_126, certificateD5_127, certificateD5_128, certificateD5_129, certificateD5_130, certificateD5_131, certificateD5_132, certificateD5_133, certificateD5_134, certificateD5_135, certificateD5_136, certificateD5_137, certificateD5_138, certificateD5_139, certificateD5_140, certificateD5_141, certificateD5_142, certificateD5_143, certificateD5_144, certificateD5_145, certificateD5_146, certificateD5_147, certificateD5_148, certificateD5_149, certificateD5_150, certificateD5_151, certificateD5_152, certificateD5_153, certificateD5_154, certificateD5_155, certificateD5_156, certificateD5_157, certificateD5_158, certificateD5_159, certificateD5_160, certificateD5_161, certificateD5_162, certificateD5_163, certificateD5_164, certificateD5_165, certificateD5_166, certificateD5_167, certificateD5_168, certificateD5_169, certificateD5_170, certificateD5_171, certificateD5_172, certificateD5_173, certificateD5_174, certificateD5_175, certificateD5_176, certificateD5_177, certificateD5_178, certificateD5_179, certificateD5_180, certificateD5_181, certificateD5_182, certificateD5_183, certificateD5_184, certificateD5_185, certificateD5_186, certificateD5_187, certificateD5_188, certificateD5_189, certificateD5_190, certificateD5_191, certificateD5_192, certificateD5_193, certificateD5_194, certificateD5_195, certificateD5_196, certificateD5_197, certificateD5_198, certificateD5_199, certificateD5_200, certificateD5_201, certificateD5_202, certificateD5_203, certificateD5_204, certificateD5_205, certificateD5_206, certificateD5_207, certificateD5_208, certificateD5_209, certificateD5_210, certificateD5_211, certificateD5_212, certificateD5_213, certificateD5_214, certificateD5_215]

end RealPinwheel.FiveSixths


