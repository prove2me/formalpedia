-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_CertificateD4
-- name    : RealPinwheel_FiveSixths_CertificateD4
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T03:48:14.285321+00:00
-- url     : https://prove2.me/theorems/10f53e28-971a-4a03-b054-fa091d89bf99
-- title:
--   Four-task five-sixths certificate words
-- statement:
--   This array stores the sixty-nine four-task words and rational density-box annotations in the source certificate family.
--
--   $$|W_4|=69,\qquad\max_{w\in W_4}|w|=18.$$
--
--   These are finite data; the validity and coverage assertions require separate proofs.
-- source:
--   Fujiwara et al., STOC 2027 submission #885, Section 4 Table 1, printed p. 10 (PDF p. 11), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf; exact data https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D4.txt

import Definitions.Def_RealPinwheel_FiveSixths_CycleCode

namespace RealPinwheel.FiveSixths

set_option maxRecDepth 100000
set_option maxHeartbeats 0
def certificateD4_0 : CycleCode := { word := "AAAAABAAAAACAAAAAD", num := #[5, 1, 1, 1], den := #[6, 18, 18, 18], strict := #[false, false, false, false] }
def certificateD4_1 : CycleCode := { word := "AAAABAAAACAAADAAAB", num := #[7, 1, 1, 1], den := #[9, 12, 18, 18], strict := #[true, true, false, false] }
def certificateD4_2 : CycleCode := { word := "AAABAACABAAABAADAB", num := #[2, 2, 1, 1], den := #[3, 9, 18, 18], strict := #[true, false, false, false] }
def certificateD4_3 : CycleCode := { word := "AABABACABAABABADAB", num := #[5, 1, 1, 1], den := #[9, 3, 18, 18], strict := #[false, true, false, false] }
def certificateD4_4 : CycleCode := { word := "ABACDBACBACABDCABC", num := #[1, 5, 5, 1], den := #[3, 18, 18, 9], strict := #[true, false, false, false] }
def certificateD4_5 : CycleCode := { word := "AAABAAABAACAABAAD", num := #[7, 1, 1, 1], den := #[10, 6, 17, 17], strict := #[true, true, false, false] }
def certificateD4_6 : CycleCode := { word := "AABABDABABABABACB", num := #[6, 2, 1, 1], den := #[13, 5, 17, 17], strict := #[true, true, false, false] }
def certificateD4_7 : CycleCode := { word := "AAABAAACAAABAAAD", num := #[3, 1, 1, 1], den := #[4, 8, 16, 16], strict := #[false, false, false, false] }
def certificateD4_8 : CycleCode := { word := "AABAABACAABAABAD", num := #[5, 1, 1, 1], den := #[8, 4, 16, 16], strict := #[false, true, false, false] }
def certificateD4_9 : CycleCode := { word := "AABABACBAABABADB", num := #[1, 3, 1, 1], den := #[2, 8, 16, 16], strict := #[true, false, false, false] }
def certificateD4_10 : CycleCode := { word := "AABABCABADBABACB", num := #[5, 3, 1, 1], den := #[12, 8, 8, 16], strict := #[true, false, true, false] }
def certificateD4_11 : CycleCode := { word := "ABABABACBABABABD", num := #[7, 7, 1, 1], den := #[16, 16, 16, 16], strict := #[false, false, false, false] }
def certificateD4_12 : CycleCode := { word := "AAABADABAABACAB", num := #[7, 4, 1, 1], den := #[12, 15, 15, 15], strict := #[true, false, false, false] }
def certificateD4_13 : CycleCode := { word := "AABABCABADABACB", num := #[5, 1, 2, 1], den := #[11, 3, 15, 15], strict := #[true, true, false, false] }
def certificateD4_14 : CycleCode := { word := "AABACABADABACAB", num := #[8, 4, 2, 1], den := #[15, 15, 15, 15], strict := #[false, false, false, false] }
def certificateD4_15 : CycleCode := { word := "AABCADBABCABACB", num := #[3, 1, 1, 1], den := #[8, 3, 5, 15], strict := #[true, true, true, false] }
def certificateD4_16 : CycleCode := { word := "AAABAACAAABAAD", num := #[5, 1, 1, 1], den := #[7, 7, 14, 14], strict := #[false, false, false, false] }
def certificateD4_17 : CycleCode := { word := "AABAACAABACAAD", num := #[9, 1, 1, 1], den := #[14, 7, 8, 14], strict := #[false, true, true, false] }
def certificateD4_18 : CycleCode := { word := "AABACAABADACAB", num := #[4, 1, 1, 1], den := #[7, 5, 7, 14], strict := #[true, true, false, false] }
def certificateD4_19 : CycleCode := { word := "AABACABAABADAB", num := #[4, 2, 1, 1], den := #[7, 7, 14, 14], strict := #[false, false, false, false] }
def certificateD4_20 : CycleCode := { word := "AABACABACADBAC", num := #[1, 3, 3, 1], den := #[2, 14, 14, 14], strict := #[true, false, false, false] }
def certificateD4_21 : CycleCode := { word := "AABACABADABCAB", num := #[1, 2, 1, 1], den := #[2, 7, 7, 14], strict := #[true, true, false, false] }
def certificateD4_22 : CycleCode := { word := "ABACABACBADABC", num := #[3, 2, 1, 1], den := #[7, 7, 5, 14], strict := #[true, false, true, false] }
def certificateD4_23 : CycleCode := { word := "ABACABDACABACD", num := #[3, 3, 3, 1], den := #[7, 14, 14, 7], strict := #[false, false, false, false] }
def certificateD4_24 : CycleCode := { word := "ABACABDACABBAC", num := #[3, 1, 3, 1], den := #[7, 4, 14, 14], strict := #[true, true, false, false] }
def certificateD4_25 : CycleCode := { word := "AABABACADABAC", num := #[7, 1, 2, 1], den := #[13, 5, 13, 13], strict := #[false, true, false, false] }
def certificateD4_26 : CycleCode := { word := "AABACAADABAAC", num := #[8, 2, 1, 1], den := #[13, 13, 7, 13], strict := #[false, false, true, false] }
def certificateD4_27 : CycleCode := { word := "AABCABDACBABC", num := #[4, 3, 3, 1], den := #[11, 10, 13, 13], strict := #[true, true, false, false] }
def certificateD4_28 : CycleCode := { word := "ABABCABADBACB", num := #[5, 3, 2, 1], den := #[13, 8, 13, 13], strict := #[false, true, false, false] }
def certificateD4_29 : CycleCode := { word := "ABABCADBACABC", num := #[5, 2, 2, 1], den := #[13, 7, 9, 13], strict := #[false, true, true, false] }
def certificateD4_30 : CycleCode := { word := "ABACABACABACD", num := #[6, 3, 3, 1], den := #[13, 13, 13, 13], strict := #[false, false, false, false] }
def certificateD4_31 : CycleCode := { word := "ABACABADABCAD", num := #[6, 3, 2, 1], den := #[13, 13, 13, 7], strict := #[false, false, false, true] }
def certificateD4_32 : CycleCode := { word := "ABCABCABCABCD", num := #[4, 4, 4, 1], den := #[13, 13, 13, 13], strict := #[false, false, false, false] }
def certificateD4_33 : CycleCode := { word := "AABAACAABAAD", num := #[2, 1, 1, 1], den := #[3, 6, 12, 12], strict := #[false, false, false, false] }
def certificateD4_34 : CycleCode := { word := "AABACAABADAB", num := #[7, 1, 1, 1], den := #[12, 4, 12, 12], strict := #[false, true, false, false] }
def certificateD4_35 : CycleCode := { word := "AABACABADABC", num := #[1, 1, 1, 1], den := #[2, 4, 6, 12], strict := #[true, false, true, false] }
def certificateD4_36 : CycleCode := { word := "AABACBAABADB", num := #[1, 1, 1, 1], den := #[2, 3, 12, 12], strict := #[true, false, false, false] }
def certificateD4_37 : CycleCode := { word := "AABCADBACABC", num := #[2, 1, 1, 1], den := #[5, 4, 4, 12], strict := #[true, false, true, false] }
def certificateD4_38 : CycleCode := { word := "AACABAADACAB", num := #[7, 1, 1, 1], den := #[12, 6, 6, 12], strict := #[false, true, true, false] }
def certificateD4_39 : CycleCode := { word := "ABABACBABABD", num := #[5, 5, 1, 1], den := #[12, 12, 12, 12], strict := #[false, false, false, false] }
def certificateD4_40 : CycleCode := { word := "ABABACBADABC", num := #[5, 1, 1, 1], den := #[12, 3, 6, 12], strict := #[false, true, false, false] }
def certificateD4_41 : CycleCode := { word := "ABCABCABDACB", num := #[1, 1, 1, 1], den := #[3, 3, 4, 12], strict := #[false, true, true, false] }
def certificateD4_42 : CycleCode := { word := "ABCABDACBACD", num := #[1, 1, 1, 1], den := #[3, 4, 4, 6], strict := #[false, true, true, false] }
def certificateD4_43 : CycleCode := { word := "AABAADAABAC", num := #[7, 2, 1, 1], den := #[11, 11, 11, 11], strict := #[false, false, false, false] }
def certificateD4_44 : CycleCode := { word := "AABACADABAC", num := #[6, 2, 2, 1], den := #[11, 11, 11, 11], strict := #[false, false, false, false] }
def certificateD4_45 : CycleCode := { word := "AABCABABADB", num := #[4, 4, 1, 1], den := #[9, 11, 11, 11], strict := #[true, false, false, false] }
def certificateD4_46 : CycleCode := { word := "ABABACABADC", num := #[5, 1, 2, 1], den := #[11, 4, 11, 11], strict := #[false, true, false, false] }
def certificateD4_47 : CycleCode := { word := "ABACABACBAD", num := #[5, 3, 1, 1], den := #[11, 11, 6, 11], strict := #[false, false, true, false] }
def certificateD4_48 : CycleCode := { word := "ABACBABCABD", num := #[4, 4, 1, 1], den := #[11, 11, 6, 11], strict := #[false, false, true, false] }
def certificateD4_49 : CycleCode := { word := "ABCABCADBAC", num := #[4, 3, 1, 1], den := #[11, 11, 4, 11], strict := #[false, false, true, false] }
def certificateD4_50 : CycleCode := { word := "ABCABDACBAD", num := #[4, 3, 2, 2], den := #[11, 11, 11, 11], strict := #[false, false, false, false] }
def certificateD4_51 : CycleCode := { word := "AAABAACAAD", num := #[7, 1, 1, 1], den := #[10, 10, 10, 10], strict := #[false, false, false, false] }
def certificateD4_52 : CycleCode := { word := "AABACAABAD", num := #[3, 1, 1, 1], den := #[5, 5, 10, 10], strict := #[false, false, false, false] }
def certificateD4_53 : CycleCode := { word := "AABACABADB", num := #[1, 3, 1, 1], den := #[2, 10, 10, 10], strict := #[true, false, false, false] }
def certificateD4_54 : CycleCode := { word := "ABACBADABC", num := #[2, 3, 1, 1], den := #[5, 10, 5, 10], strict := #[false, false, true, false] }
def certificateD4_55 : CycleCode := { word := "ABCADBACBD", num := #[3, 3, 1, 1], den := #[10, 10, 5, 5], strict := #[false, false, false, false] }
def certificateD4_56 : CycleCode := { word := "AABAACAAD", num := #[2, 1, 1, 1], den := #[3, 9, 9, 9], strict := #[false, false, false, false] }
def certificateD4_57 : CycleCode := { word := "AABACABAD", num := #[5, 2, 1, 1], den := #[9, 9, 9, 9], strict := #[false, false, false, false] }
def certificateD4_58 : CycleCode := { word := "ABCADBACD", num := #[1, 2, 2, 2], den := #[3, 9, 9, 9], strict := #[false, false, false, false] }
def certificateD4_59 : CycleCode := { word := "ABABCABD", num := #[3, 3, 1, 1], den := #[8, 8, 8, 8], strict := #[false, false, false, false] }
def certificateD4_60 : CycleCode := { word := "ABACABAD", num := #[1, 1, 1, 1], den := #[2, 4, 8, 8], strict := #[false, false, false, false] }
def certificateD4_61 : CycleCode := { word := "ABCADBAC", num := #[3, 1, 1, 1], den := #[8, 4, 4, 8], strict := #[false, false, true, false] }
def certificateD4_62 : CycleCode := { word := "AACABAD", num := #[4, 1, 1, 1], den := #[7, 7, 7, 7], strict := #[false, false, false, false] }
def certificateD4_63 : CycleCode := { word := "ABACABD", num := #[3, 2, 1, 1], den := #[7, 7, 7, 7], strict := #[false, false, false, false] }
def certificateD4_64 : CycleCode := { word := "ABCABCD", num := #[2, 2, 2, 1], den := #[7, 7, 7, 7], strict := #[false, false, false, false] }
def certificateD4_65 : CycleCode := { word := "ABACAD", num := #[1, 1, 1, 1], den := #[2, 6, 6, 6], strict := #[false, false, false, false] }
def certificateD4_66 : CycleCode := { word := "ABCABD", num := #[1, 1, 1, 1], den := #[3, 3, 6, 6], strict := #[false, false, false, false] }
def certificateD4_67 : CycleCode := { word := "ABCAD", num := #[2, 1, 1, 1], den := #[5, 5, 5, 5], strict := #[false, false, false, false] }
def certificateD4_68 : CycleCode := { word := "ADBC", num := #[1, 1, 1, 1], den := #[4, 4, 4, 4], strict := #[false, false, false, false] }

def certificateD4 : Array CycleCode := #[certificateD4_0, certificateD4_1, certificateD4_2, certificateD4_3, certificateD4_4, certificateD4_5, certificateD4_6, certificateD4_7, certificateD4_8, certificateD4_9, certificateD4_10, certificateD4_11, certificateD4_12, certificateD4_13, certificateD4_14, certificateD4_15, certificateD4_16, certificateD4_17, certificateD4_18, certificateD4_19, certificateD4_20, certificateD4_21, certificateD4_22, certificateD4_23, certificateD4_24, certificateD4_25, certificateD4_26, certificateD4_27, certificateD4_28, certificateD4_29, certificateD4_30, certificateD4_31, certificateD4_32, certificateD4_33, certificateD4_34, certificateD4_35, certificateD4_36, certificateD4_37, certificateD4_38, certificateD4_39, certificateD4_40, certificateD4_41, certificateD4_42, certificateD4_43, certificateD4_44, certificateD4_45, certificateD4_46, certificateD4_47, certificateD4_48, certificateD4_49, certificateD4_50, certificateD4_51, certificateD4_52, certificateD4_53, certificateD4_54, certificateD4_55, certificateD4_56, certificateD4_57, certificateD4_58, certificateD4_59, certificateD4_60, certificateD4_61, certificateD4_62, certificateD4_63, certificateD4_64, certificateD4_65, certificateD4_66, certificateD4_67, certificateD4_68]

end RealPinwheel.FiveSixths


