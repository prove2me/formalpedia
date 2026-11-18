-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD4
-- name    : RealPinwheel_FiveSixths_CodeFunctionD4
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:26:55.381479+00:00
-- url     : https://prove2.me/theorems/c0b0f2ac-423f-4102-8632-98c279055442
-- title:
--   Balanced lookup for certificate D4
-- statement:
--   This balanced lookup returns the annotated word code with zero-based index $j$ in source family D4, for $0\le j<69$.
--
--   $$j\longmapsto c_j.$$
--
--   It provides the same finite word and rational bound data as the array representation while allowing efficient exact lookup in kernel computations. Values outside the stated index range are unused by the covering checker.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Exact data: https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D4.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD4
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def codeTreeD4 : StepTree CycleCode := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf certificateD4_0) (.leaf certificateD4_1)) (.branch 3 (.leaf certificateD4_2) (.leaf certificateD4_3))) (.branch 6 (.branch 5 (.leaf certificateD4_4) (.leaf certificateD4_5)) (.branch 7 (.leaf certificateD4_6) (.leaf certificateD4_7)))) (.branch 12 (.branch 10 (.branch 9 (.leaf certificateD4_8) (.leaf certificateD4_9)) (.branch 11 (.leaf certificateD4_10) (.leaf certificateD4_11))) (.branch 14 (.branch 13 (.leaf certificateD4_12) (.leaf certificateD4_13)) (.branch 15 (.leaf certificateD4_14) (.branch 16 (.leaf certificateD4_15) (.leaf certificateD4_16)))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf certificateD4_17) (.leaf certificateD4_18)) (.branch 20 (.leaf certificateD4_19) (.leaf certificateD4_20))) (.branch 23 (.branch 22 (.leaf certificateD4_21) (.leaf certificateD4_22)) (.branch 24 (.leaf certificateD4_23) (.leaf certificateD4_24)))) (.branch 29 (.branch 27 (.branch 26 (.leaf certificateD4_25) (.leaf certificateD4_26)) (.branch 28 (.leaf certificateD4_27) (.leaf certificateD4_28))) (.branch 31 (.branch 30 (.leaf certificateD4_29) (.leaf certificateD4_30)) (.branch 32 (.leaf certificateD4_31) (.branch 33 (.leaf certificateD4_32) (.leaf certificateD4_33))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf certificateD4_34) (.leaf certificateD4_35)) (.branch 37 (.leaf certificateD4_36) (.leaf certificateD4_37))) (.branch 40 (.branch 39 (.leaf certificateD4_38) (.leaf certificateD4_39)) (.branch 41 (.leaf certificateD4_40) (.leaf certificateD4_41)))) (.branch 46 (.branch 44 (.branch 43 (.leaf certificateD4_42) (.leaf certificateD4_43)) (.branch 45 (.leaf certificateD4_44) (.leaf certificateD4_45))) (.branch 48 (.branch 47 (.leaf certificateD4_46) (.leaf certificateD4_47)) (.branch 49 (.leaf certificateD4_48) (.branch 50 (.leaf certificateD4_49) (.leaf certificateD4_50)))))) (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf certificateD4_51) (.leaf certificateD4_52)) (.branch 54 (.leaf certificateD4_53) (.leaf certificateD4_54))) (.branch 57 (.branch 56 (.leaf certificateD4_55) (.leaf certificateD4_56)) (.branch 58 (.leaf certificateD4_57) (.branch 59 (.leaf certificateD4_58) (.leaf certificateD4_59))))) (.branch 64 (.branch 62 (.branch 61 (.leaf certificateD4_60) (.leaf certificateD4_61)) (.branch 63 (.leaf certificateD4_62) (.leaf certificateD4_63))) (.branch 66 (.branch 65 (.leaf certificateD4_64) (.leaf certificateD4_65)) (.branch 67 (.leaf certificateD4_66) (.branch 68 (.leaf certificateD4_67) (.leaf certificateD4_68))))))))
def codeFunctionD4 (j : ℕ) : CycleCode := codeTreeD4.eval j
end RealPinwheel.FiveSixths


