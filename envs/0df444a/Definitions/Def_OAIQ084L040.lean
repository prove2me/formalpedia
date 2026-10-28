-- Prove2me | Definitions.Def_OAIQ084L040
-- name    : OAIQ084L040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:36:05.034+00:00
-- url     : https://prove2.me/theorems/64f1b7cb-81a1-49ec-af48-8a0053a9d4c4
-- title:
--   Definitions bundle OAIQ084L040 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 9 definitions. The definitions and types are `OAI.LaughlinFock.fourZData_12`, `OAI.LaughlinFock.fourZData_13`, `OAI.LaughlinFock.fourZData_14`, `OAI.LaughlinFock.fourZData_15`, `OAI.LaughlinFock.fourZData_16`, `OAI.LaughlinFock.fourZData_17`, `OAI.LaughlinFock.fourZData_19`, `OAI.LaughlinFock.fourZData_22`, `OAI.LaughlinFock.fourZData_23`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_Certificate12Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate12Data.lean), [`LaughlinFock_Certificate13Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate13Data.lean), [`LaughlinFock_Certificate14Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate14Data.lean), [`LaughlinFock_Certificate15Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate15Data.lean), [`LaughlinFock_Certificate16Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate16Data.lean), [`LaughlinFock_Certificate17Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate17Data.lean), [`LaughlinFock_Certificate19Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate19Data.lean), [`LaughlinFock_Certificate22Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate22Data.lean), [`LaughlinFock_Certificate23Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate23Data.lean).
--
--   **Imports.** It imports the bundle `OAIQ084L012` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.LaughlinFock.integer_certificate_12`, `OAI.LaughlinFock.integer_certificate_13`, `OAI.LaughlinFock.integer_certificate_14`, `OAI.LaughlinFock.integer_certificate_15`, `OAI.LaughlinFock.integer_certificate_16`, `OAI.LaughlinFock.integer_certificate_17`, `OAI.LaughlinFock.integer_certificate_19`, `OAI.LaughlinFock.integer_certificate_22` and `OAI.LaughlinFock.integer_certificate_23`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ084L012

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate12Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate12 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourZData_12 : Matrix (CopyLabel 12) (CopyLabel 12) ℚ :=
  copyMatrixData 12 [
    [0, 0, 0, 0, 0, 0],
    [0, 272160, 0, 0, -17010, (467775/8)],
    [0, 0, 18900, (-14175/2), 0, (155925/16)],
    [0, 0, (-14175/2), (42525/16), 0, (-467775/128)],
    [0, -17010, 0, 0, (8505/8), (-467775/128)],
    [0, (467775/8), (155925/16), (-467775/128), (-467775/128), (36018675/2048)]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate13Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate13 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourZData_13 : Matrix (CopyLabel 13) (CopyLabel 13) ℚ :=
  copyMatrixData 13 [
    [479001600, 0, 0, 0, 0, -467775, (30405375/4)],
    [0, 2721600, 0, 0, -42525, 0, (18243225/16)],
    [0, 0, 151200, -14175, (-127575/4), (779625/16), (6081075/64)],
    [0, 0, -14175, (14175/4), 0, 0, (-6081075/256)],
    [0, -42525, (-127575/4), 0, (365715/32), (-4209975/256), (-18243225/1024)],
    [-467775, 0, (779625/16), 0, (-4209975/256), (3274425/128), (-30405375/4096)],
    [(30405375/4), (18243225/16), (6081075/64), (-6081075/256), (-18243225/1024), (-30405375/4096), (12411474075/16384)]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate14Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate14 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourZData_14 : Matrix (CopyLabel 14) (CopyLabel 14) ℚ :=
  copyMatrixData 14 [
    [0, 0, 0, 0, 0, 0, 0],
    [0, 29937600, 0, 0, 0, (-2338875/4), (6081075/2)],
    [0, 0, 1360800, 0, -170100, 0, (6081075/8)],
    [0, 0, 0, (694575/8), (-297675/4), (3274425/64), 0],
    [0, 0, -170100, (-297675/4), 85050, (-1403325/32), (-6081075/64)],
    [0, (-2338875/4), 0, (3274425/64), (-1403325/32), (42567525/1024), (-30405375/512)],
    [0, (6081075/2), (6081075/8), 0, (-6081075/64), (-30405375/512), (1502025525/2048)]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate15Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate15 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourZData_15 : Matrix (CopyLabel 15) (CopyLabel 15) ℚ :=
  copyMatrixData 15 [
    [87178291200, 0, 0, 0, 0, 0, (-42567525/2), (1915538625/4)],
    [0, 359251200, 0, 0, 0, -1403325, 0, (638512875/8)],
    [0, 0, 13608000, 0, (-637875/2), (-2338875/2), (91216125/32), (638512875/64)],
    [0, 0, 0, 1389150, (-2679075/4), 0, (42567525/64), 0],
    [0, 0, (-637875/2), (-2679075/4), (5485725/16), 0, (-164189025/512), (-638512875/1024)],
    [0, -1403325, (-2338875/2), 0, 0, (42567525/256), (-200675475/512), (-638512875/2048)],
    [(-42567525/2), 0, (91216125/32), (42567525/64), (-164189025/512), (-200675475/512), (10477692225/8192), (-1915538625/16384)],
    [(1915538625/4), (638512875/8), (638512875/64), 0, (-638512875/1024), (-638512875/2048), (-1915538625/16384), (653198671125/16384)]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate16Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate16 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourZData_16 : Matrix (CopyLabel 16) (CopyLabel 16) ℚ :=
  copyMatrixData 16 [
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 4670265600, 0, 0, 0, 0, (-54729675/2), (3192564375/16)],
    [0, 0, 149688000, 0, 0, (-11694375/2), 0, (1915538625/32)],
    [0, 0, 0, 14288400, -2679075, (-49116375/16), (127702575/32), (1915538625/256)],
    [0, 0, 0, -2679075, 893025, 0, 0, (-638512875/256)],
    [0, 0, (-11694375/2), (-49116375/16), 0, (222193125/128), (-1003377375/512), (-9577693125/4096)],
    [0, (-54729675/2), 0, (127702575/32), 0, (-1003377375/512), (346621275/128), (-9577693125/8192)],
    [0, (3192564375/16), (1915538625/32), (1915538625/256), (-638512875/256), (-9577693125/4096), (-9577693125/8192), (2584061605125/65536)]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate17Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate17 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourZData_17 : Matrix (CopyLabel 17) (CopyLabel 17) ℚ :=
  copyMatrixData 17 [
    [20922789888000, 0, 0, 0, 0, 0, 0, -1277025750, (75983032125/2)],
    [0, 65383718400, 0, 0, 0, 0, (-127702575/2), 0, (54273594375/8)],
    [0, 0, 1796256000, 0, 0, (-21049875/2), (-456080625/8), (3192564375/16), (32564156625/32)],
    [0, 0, 0, 142884000, -4465125, (-49116375/2), 0, (4469590125/64), (10854718875/128)],
    [0, 0, 0, -4465125, (41972175/4), (-147349125/16), (383107725/64), 0, (-10854718875/512)],
    [0, 0, (-21049875/2), (-49116375/2), (-147349125/16), 14033250, (-3010132125/512), (-7023641625/512), (-32564156625/2048)],
    [0, (-127702575/2), (-456080625/8), 0, (383107725/64), (-3010132125/512), (13883094225/2048), (-41503336875/4096), (-54273594375/8192)],
    [-1277025750, 0, (3192564375/16), (4469590125/64), 0, (-7023641625/512), (-41503336875/4096), (1221475129875/16384), (-75983032125/32768)],
    [(75983032125/2), (54273594375/8), (32564156625/32), (10854718875/128), (-10854718875/512), (-32564156625/2048), (-54273594375/8192), (-75983032125/32768), (355589735626125/131072)]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate19Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate19 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourZData_19 : Matrix (CopyLabel 19) (CopyLabel 19) ℚ :=
  copyMatrixData 19 [
    [6402373705728000, 0, 0, 0, 0, 0, 0, 0, -97692469875, 3712313855250],
    [0, 15692092416000, 0, 0, 0, 0, 0, -3831077250, 0, (5568470782875/8)],
    [0, 0, 326918592000, 0, 0, 0, (-1915538625/4), (-28733079375/8), (271367971875/16), (1856156927625/16)],
    [0, 0, 0, 18860688000, 0, -147349125, (-9577693125/8), 0, (227949096375/32), (1856156927625/128)],
    [0, 0, 0, 0, (4942893375/2), (-1326142125/2), (-17239847625/32), (40226311125/64), (293077409625/256), 0],
    [0, 0, 0, -147349125, (-1326142125/2), (4469590125/16), 0, 0, (-119401907625/256), (-1856156927625/2048)],
    [0, 0, (-1915538625/4), (-9577693125/8), (-17239847625/32), 0, (443036719125/1024), (-821766070125/2048), (-2116670180625/4096), (-1856156927625/4096)],
    [0, -3831077250, (-28733079375/8), 0, (40226311125/64), 0, (-821766070125/2048), (1089941477625/2048), (-2442311746875/8192), (-5568470782875/32768)],
    [-97692469875, 0, (271367971875/16), (227949096375/32), (293077409625/256), (-119401907625/256), (-2116670180625/4096), (-2442311746875/8192), (346645447273125/65536), (-1856156927625/32768)],
    [3712313855250, (5568470782875/8), (1856156927625/16), (1856156927625/128), 0, (-1856156927625/2048), (-1856156927625/4096), (-5568470782875/32768), (-1856156927625/32768), (121635819624193875/524288)]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate22Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate22 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourZData_22 : Matrix (CopyLabel 22) (CopyLabel 22) ℚ :=
  copyMatrixData 22 [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 91233825306624000, 0, 0, 0, 0, 0, 0, 0, (-50116237045875/4), 194896477400625],
    [0, 0, 1333827855360000, 0, 0, 0, 0, 0, -1302566265000, 0, (584689432201875/8)],
    [0, 0, 0, 51489678240000, 0, 0, 0, (-4223762668125/16), (-3419236445625/4), (194896477400625/64), (584689432201875/32)],
    [0, 0, 0, 0, 4413400992000, 0, -103439085750, (-3016973334375/8), 0, (50116237045875/32), (194896477400625/64)],
    [0, 0, 0, 0, 0, (5616211899375/8), (-948191619375/4), (-19912024006875/128), (5373085843125/32), (306265893058125/1024), 0],
    [0, 0, 0, 0, -103439085750, (-948191619375/4), (1948102781625/16), 0, 0, (-72390120177375/512), (-584689432201875/2048)],
    [0, 0, 0, (-4223762668125/16), (-3016973334375/8), (-19912024006875/128), 0, (680025789568125/4096), (-133350221379375/1024), (-2923447161009375/16384), (-1364275341804375/8192)],
    [0, 0, -1302566265000, (-3419236445625/4), 0, (5373085843125/32), 0, (-133350221379375/1024), (22306447288125/128), (-473320016544375/4096), (-584689432201875/8192)],
    [0, (-50116237045875/4), 0, (194896477400625/64), (50116237045875/32), (306265893058125/1024), (-72390120177375/512), (-2923447161009375/16384), (-473320016544375/4096), (349382562329926125/262144), (-1754068296605625/65536)],
    [0, 194896477400625, (584689432201875/8), (584689432201875/32), (194896477400625/64), 0, (-584689432201875/2048), (-1364275341804375/8192), (-584689432201875/8192), (-1754068296605625/65536), (12767863130992344375/524288)]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate23Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate23 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourZData_23 : Matrix (CopyLabel 23) (CopyLabel 23) ℚ :=
  copyMatrixData 23 [
    [1124000727777607680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-2143861251406875/2), (246544043911790625/4)],
    [0, 1824676506132480000, 0, 0, 0, 0, 0, 0, 0, -27842353914375, 0, (49308808782358125/4)],
    [0, 0, 24008901396480000, 0, 0, 0, 0, 0, (-4396161144375/2), -27842353914375, (6821376709021875/32), (147926426347074375/64)],
    [0, 0, 0, 823834851840000, 0, 0, 0, -402263111250, (-23934655119375/4), 0, (6821376709021875/64), (49308808782358125/128)],
    [0, 0, 0, 0, 61787613888000, 0, (-603394666875/4), (-16291656005625/8), (-51288546684375/16), (116937886440375/16), (15786614669450625/512), (49308808782358125/1024)],
    [0, 0, 0, 0, 0, (18453267669375/2), (-4740958096875/4), (-33186706678125/16), 0, (918797679174375/256), (2143861251406875/512), 0],
    [0, 0, 0, 0, (-603394666875/4), (-4740958096875/4), (65597620213125/64), (-86285437363125/128), (209550347881875/512), 0, (-12668271031040625/8192), (-49308808782358125/16384)],
    [0, 0, 0, -402263111250, (-16291656005625/8), (-33186706678125/16), (-86285437363125/128), 1609052445000, (-488950811724375/1024), (-2533654206208125/2048), (-26311024449084375/16384), (-49308808782358125/32768)],
    [0, 0, (-4396161144375/2), (-23934655119375/4), (-51288546684375/16), 0, (209550347881875/512), (-488950811724375/1024), (1734529802630625/2048), (-2366600082721875/2048), (-115963404053371875/131072), (-147926426347074375/262144)],
    [0, -27842353914375, -27842353914375, 0, (116937886440375/16), (918797679174375/256), 0, (-2533654206208125/2048), (-2366600082721875/2048), (316372667529043125/65536), (-25921231494283125/65536), (-49308808782358125/262144)],
    [(-2143861251406875/2), 0, (6821376709021875/32), (6821376709021875/64), (15786614669450625/512), (2143861251406875/512), (-12668271031040625/8192), (-26311024449084375/16384), (-115963404053371875/131072), (-25921231494283125/65536), (101850365435360416875/2097152), (-246544043911790625/4194304)],
    [(246544043911790625/4), (49308808782358125/4), (147926426347074375/64), (49308808782358125/128), (49308808782358125/1024), 0, (-49308808782358125/16384), (-49308808782358125/32768), (-147926426347074375/262144), (-49308808782358125/262144), (-246544043911790625/4194304), (25851868812458629565625/8388608)]
  ]

end LaughlinFock
end

end OAI
end


