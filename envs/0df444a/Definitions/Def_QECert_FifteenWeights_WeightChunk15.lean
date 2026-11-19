-- Prove2me | Definitions.Def_QECert_FifteenWeights_WeightChunk15
-- name    : QECert_FifteenWeights_WeightChunk15
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:57:33.554813+00:00
-- url     : https://prove2.me/theorems/433eb26e-9666-428d-994f-1ca571f62e57
-- title:
--   Code
-- statement:
--   Definitions and structural lemmas for Code, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean

import Definitions.Def_QECert_FifteenWeights_CoreWeights
set_option autoImplicit false
set_option maxHeartbeats 200000
open QEC QEC.Coding QEC.Distillation.BK15
open scoped BigOperators
namespace QEC.Distillation.BK15.CertifiedWeights
private theorem certificate_960 : HammingWeight (l2CoefficientMap (certificateCoefficient 960)) = 6 := by
  decide +kernel
private theorem certificate_961 : HammingWeight (l2CoefficientMap (certificateCoefficient 961)) = 10 := by
  decide +kernel
private theorem certificate_962 : HammingWeight (l2CoefficientMap (certificateCoefficient 962)) = 6 := by
  decide +kernel
private theorem certificate_963 : HammingWeight (l2CoefficientMap (certificateCoefficient 963)) = 6 := by
  decide +kernel
private theorem certificate_964 : HammingWeight (l2CoefficientMap (certificateCoefficient 964)) = 6 := by
  decide +kernel
private theorem certificate_965 : HammingWeight (l2CoefficientMap (certificateCoefficient 965)) = 6 := by
  decide +kernel
private theorem certificate_966 : HammingWeight (l2CoefficientMap (certificateCoefficient 966)) = 10 := by
  decide +kernel
private theorem certificate_967 : HammingWeight (l2CoefficientMap (certificateCoefficient 967)) = 6 := by
  decide +kernel
private theorem certificate_968 : HammingWeight (l2CoefficientMap (certificateCoefficient 968)) = 6 := by
  decide +kernel
private theorem certificate_969 : HammingWeight (l2CoefficientMap (certificateCoefficient 969)) = 6 := by
  decide +kernel
private theorem certificate_970 : HammingWeight (l2CoefficientMap (certificateCoefficient 970)) = 6 := by
  decide +kernel
private theorem certificate_971 : HammingWeight (l2CoefficientMap (certificateCoefficient 971)) = 10 := by
  decide +kernel
private theorem certificate_972 : HammingWeight (l2CoefficientMap (certificateCoefficient 972)) = 6 := by
  decide +kernel
private theorem certificate_973 : HammingWeight (l2CoefficientMap (certificateCoefficient 973)) = 10 := by
  decide +kernel
private theorem certificate_974 : HammingWeight (l2CoefficientMap (certificateCoefficient 974)) = 10 := by
  decide +kernel
private theorem certificate_975 : HammingWeight (l2CoefficientMap (certificateCoefficient 975)) = 10 := by
  decide +kernel
private theorem certificate_976 : HammingWeight (l2CoefficientMap (certificateCoefficient 976)) = 8 := by
  decide +kernel
private theorem certificate_977 : HammingWeight (l2CoefficientMap (certificateCoefficient 977)) = 8 := by
  decide +kernel
private theorem certificate_978 : HammingWeight (l2CoefficientMap (certificateCoefficient 978)) = 4 := by
  decide +kernel
private theorem certificate_979 : HammingWeight (l2CoefficientMap (certificateCoefficient 979)) = 8 := by
  decide +kernel
private theorem certificate_980 : HammingWeight (l2CoefficientMap (certificateCoefficient 980)) = 8 := by
  decide +kernel
private theorem certificate_981 : HammingWeight (l2CoefficientMap (certificateCoefficient 981)) = 4 := by
  decide +kernel
private theorem certificate_982 : HammingWeight (l2CoefficientMap (certificateCoefficient 982)) = 8 := by
  decide +kernel
private theorem certificate_983 : HammingWeight (l2CoefficientMap (certificateCoefficient 983)) = 8 := by
  decide +kernel
private theorem certificate_984 : HammingWeight (l2CoefficientMap (certificateCoefficient 984)) = 4 := by
  decide +kernel
private theorem certificate_985 : HammingWeight (l2CoefficientMap (certificateCoefficient 985)) = 8 := by
  decide +kernel
private theorem certificate_986 : HammingWeight (l2CoefficientMap (certificateCoefficient 986)) = 8 := by
  decide +kernel
private theorem certificate_987 : HammingWeight (l2CoefficientMap (certificateCoefficient 987)) = 8 := by
  decide +kernel
private theorem certificate_988 : HammingWeight (l2CoefficientMap (certificateCoefficient 988)) = 8 := by
  decide +kernel
private theorem certificate_989 : HammingWeight (l2CoefficientMap (certificateCoefficient 989)) = 8 := by
  decide +kernel
private theorem certificate_990 : HammingWeight (l2CoefficientMap (certificateCoefficient 990)) = 8 := by
  decide +kernel
private theorem certificate_991 : HammingWeight (l2CoefficientMap (certificateCoefficient 991)) = 12 := by
  decide +kernel
private theorem certificate_992 : HammingWeight (l2CoefficientMap (certificateCoefficient 992)) = 8 := by
  decide +kernel
private theorem certificate_993 : HammingWeight (l2CoefficientMap (certificateCoefficient 993)) = 8 := by
  decide +kernel
private theorem certificate_994 : HammingWeight (l2CoefficientMap (certificateCoefficient 994)) = 8 := by
  decide +kernel
private theorem certificate_995 : HammingWeight (l2CoefficientMap (certificateCoefficient 995)) = 4 := by
  decide +kernel
private theorem certificate_996 : HammingWeight (l2CoefficientMap (certificateCoefficient 996)) = 4 := by
  decide +kernel
private theorem certificate_997 : HammingWeight (l2CoefficientMap (certificateCoefficient 997)) = 8 := by
  decide +kernel
private theorem certificate_998 : HammingWeight (l2CoefficientMap (certificateCoefficient 998)) = 8 := by
  decide +kernel
private theorem certificate_999 : HammingWeight (l2CoefficientMap (certificateCoefficient 999)) = 8 := by
  decide +kernel
private theorem certificate_1000 : HammingWeight (l2CoefficientMap (certificateCoefficient 1000)) = 4 := by
  decide +kernel
private theorem certificate_1001 : HammingWeight (l2CoefficientMap (certificateCoefficient 1001)) = 8 := by
  decide +kernel
private theorem certificate_1002 : HammingWeight (l2CoefficientMap (certificateCoefficient 1002)) = 8 := by
  decide +kernel
private theorem certificate_1003 : HammingWeight (l2CoefficientMap (certificateCoefficient 1003)) = 8 := by
  decide +kernel
private theorem certificate_1004 : HammingWeight (l2CoefficientMap (certificateCoefficient 1004)) = 8 := by
  decide +kernel
private theorem certificate_1005 : HammingWeight (l2CoefficientMap (certificateCoefficient 1005)) = 8 := by
  decide +kernel
private theorem certificate_1006 : HammingWeight (l2CoefficientMap (certificateCoefficient 1006)) = 8 := by
  decide +kernel
private theorem certificate_1007 : HammingWeight (l2CoefficientMap (certificateCoefficient 1007)) = 12 := by
  decide +kernel
private theorem certificate_1008 : HammingWeight (l2CoefficientMap (certificateCoefficient 1008)) = 10 := by
  decide +kernel
private theorem certificate_1009 : HammingWeight (l2CoefficientMap (certificateCoefficient 1009)) = 6 := by
  decide +kernel
private theorem certificate_1010 : HammingWeight (l2CoefficientMap (certificateCoefficient 1010)) = 6 := by
  decide +kernel
private theorem certificate_1011 : HammingWeight (l2CoefficientMap (certificateCoefficient 1011)) = 6 := by
  decide +kernel
private theorem certificate_1012 : HammingWeight (l2CoefficientMap (certificateCoefficient 1012)) = 6 := by
  decide +kernel
private theorem certificate_1013 : HammingWeight (l2CoefficientMap (certificateCoefficient 1013)) = 6 := by
  decide +kernel
private theorem certificate_1014 : HammingWeight (l2CoefficientMap (certificateCoefficient 1014)) = 6 := by
  decide +kernel
private theorem certificate_1015 : HammingWeight (l2CoefficientMap (certificateCoefficient 1015)) = 10 := by
  decide +kernel
private theorem certificate_1016 : HammingWeight (l2CoefficientMap (certificateCoefficient 1016)) = 6 := by
  decide +kernel
private theorem certificate_1017 : HammingWeight (l2CoefficientMap (certificateCoefficient 1017)) = 6 := by
  decide +kernel
private theorem certificate_1018 : HammingWeight (l2CoefficientMap (certificateCoefficient 1018)) = 6 := by
  decide +kernel
private theorem certificate_1019 : HammingWeight (l2CoefficientMap (certificateCoefficient 1019)) = 10 := by
  decide +kernel
private theorem certificate_1020 : HammingWeight (l2CoefficientMap (certificateCoefficient 1020)) = 6 := by
  decide +kernel
private theorem certificate_1021 : HammingWeight (l2CoefficientMap (certificateCoefficient 1021)) = 10 := by
  decide +kernel
private theorem certificate_1022 : HammingWeight (l2CoefficientMap (certificateCoefficient 1022)) = 10 := by
  decide +kernel
private theorem certificate_1023 : HammingWeight (l2CoefficientMap (certificateCoefficient 1023)) = 10 := by
  decide +kernel
theorem word_table_block_15 (j : Fin 64) : HammingWeight (l2CoefficientMap (certificateCoefficient (15 * 64 + j.val))) = certificateWeightBlock 15 j := by
  change HammingWeight (l2CoefficientMap (certificateCoefficient (15 * 64 + j.val))) = (![6, 10, 6, 6, 6, 6, 10, 6, 6, 6, 6, 10, 6, 10, 10, 10, 8, 8, 4, 8, 8, 4, 8, 8, 4, 8, 8, 8, 8, 8, 8, 12, 8, 8, 8, 4, 4, 8, 8, 8, 4, 8, 8, 8, 8, 8, 8, 12, 10, 6, 6, 6, 6, 6, 6, 10, 6, 6, 6, 10, 6, 10, 10, 10] : Fin 64 → Nat) j
  fin_cases j
  · exact certificate_960
  · exact certificate_961
  · exact certificate_962
  · exact certificate_963
  · exact certificate_964
  · exact certificate_965
  · exact certificate_966
  · exact certificate_967
  · exact certificate_968
  · exact certificate_969
  · exact certificate_970
  · exact certificate_971
  · exact certificate_972
  · exact certificate_973
  · exact certificate_974
  · exact certificate_975
  · exact certificate_976
  · exact certificate_977
  · exact certificate_978
  · exact certificate_979
  · exact certificate_980
  · exact certificate_981
  · exact certificate_982
  · exact certificate_983
  · exact certificate_984
  · exact certificate_985
  · exact certificate_986
  · exact certificate_987
  · exact certificate_988
  · exact certificate_989
  · exact certificate_990
  · exact certificate_991
  · exact certificate_992
  · exact certificate_993
  · exact certificate_994
  · exact certificate_995
  · exact certificate_996
  · exact certificate_997
  · exact certificate_998
  · exact certificate_999
  · exact certificate_1000
  · exact certificate_1001
  · exact certificate_1002
  · exact certificate_1003
  · exact certificate_1004
  · exact certificate_1005
  · exact certificate_1006
  · exact certificate_1007
  · exact certificate_1008
  · exact certificate_1009
  · exact certificate_1010
  · exact certificate_1011
  · exact certificate_1012
  · exact certificate_1013
  · exact certificate_1014
  · exact certificate_1015
  · exact certificate_1016
  · exact certificate_1017
  · exact certificate_1018
  · exact certificate_1019
  · exact certificate_1020
  · exact certificate_1021
  · exact certificate_1022
  · exact certificate_1023


end QEC.Distillation.BK15.CertifiedWeights


