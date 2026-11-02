-- Prove2me | Definitions.Def_OAIQ106D044
-- name    : OAIQ106D044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:22:28.243248+00:00
-- url     : https://prove2.me/theorems/b74e53cb-ef04-49e9-993b-e1f149c1946a
-- title:
--   Definitions bundle OAIQ106D044 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 567 declarations of OpenAI's Lean: 567 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1423`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1424`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1425`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1426`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1427`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1428`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1429`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1430`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1431`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1432`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1433`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1434`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1435`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1436`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1437`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1438`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1439`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1440`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1441`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1442`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1443`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1444`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1445`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1446`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1447`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1448`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1449`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix145`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1450`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1451`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1452`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1453`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1454`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1455`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1456`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1457`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1458`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1459`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix146`, `OAI.MUB6.Certificate.PairSemantics.pivotMatrix1460` and 527 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Sound0`, `MutuallyUnbiased_PairSemantics_Sound2`, `MutuallyUnbiased_PairSemantics_Sound22`, `MutuallyUnbiased_PairSemantics_Sound23`, `MutuallyUnbiased_PairSemantics_Sound24`, `MutuallyUnbiased_PairSemantics_Sound25`, `MutuallyUnbiased_PairSemantics_Sound26`, `MutuallyUnbiased_PairSemantics_Sound27`, `MutuallyUnbiased_PairSemantics_Sound28`, `MutuallyUnbiased_PairSemantics_Sound29`, `MutuallyUnbiased_PairSemantics_Sound3`, `MutuallyUnbiased_PairSemantics_Sound30`, `MutuallyUnbiased_PairSources_Data`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D140`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]

def pivotMatrix15 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-4, 4], ![2, -2], ![3, -3]]

def pivotMatrix16 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-4, 4], ![1, -1], ![2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix145 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![2, 0, -2]]

def pivotMatrix146 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 2, -2], ![2, -1, -1]]

def pivotMatrix147 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 3, -3], ![2, -2, 0]]

def pivotMatrix148 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![1, -2, 1], ![1, 3, -4]]

def pivotMatrix149 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix150 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix153 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![0, 2, -2], ![1, 1, -2]]

def pivotMatrix155 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![0, 3, -3], ![1, 0, -1]]

def pivotMatrix156 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -2, 4], ![0, 4, -4], ![1, -2, 1]]

def pivotMatrix157 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![0, 4, -4], ![1, -1, 0]]

def pivotMatrix158 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 3, -4], ![2, -3, 1]]

def pivotMatrix165 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![0, -2, 2], ![1, 4, -5]]

def pivotMatrix166 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -1, 3], ![0, -2, 2], ![1, 3, -4]]

def pivotMatrix168 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![2, 1, -3]]

def pivotMatrix169 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 2, -2], ![2, 0, -2]]

def pivotMatrix170 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 3, -3], ![2, -1, -1]]

def pivotMatrix171 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 4, -4], ![2, -2, 0]]

def pivotMatrix172 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![1, -2, 1], ![1, 4, -5]]

def pivotMatrix173 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix174 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix175 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![1, 1, -2], ![1, 1, -2]]

def pivotMatrix176 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![2, -1, -1]]

def pivotMatrix177 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 2, -2], ![2, -2, 0]]

def pivotMatrix178 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 3, -3], ![2, -3, 1]]

def pivotMatrix179 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![1, -3, 2], ![1, 3, -4]]

def pivotMatrix180 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![1, -2, 1], ![1, 2, -3]]

def pivotMatrix181 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix185 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![0, 2, -2], ![1, 0, -1]]

def pivotMatrix187 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -1, 3], ![0, 3, -3], ![1, -2, 1]]

def pivotMatrix188 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![0, 3, -3], ![1, -1, 0]]

def pivotMatrix189 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, -1, 3], ![0, 4, -4], ![1, -3, 2]]

def pivotMatrix190 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -1, 3], ![0, 4, -4], ![1, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix194 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![-2, 0, 2], ![0, -3, 3], ![1, 4, -5]]

def pivotMatrix195 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![-2, 0, 2], ![0, -3, 3], ![1, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1423 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def pivotMatrix1424 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix1425 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix1426 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def pivotMatrix1427 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def pivotMatrix1428 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def pivotMatrix1429 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1430 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix1431 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1432 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1433 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1434 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1435 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def pivotMatrix1436 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def pivotMatrix1437 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix1438 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1439 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def pivotMatrix1440 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def pivotMatrix1441 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def pivotMatrix1442 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix1443 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def pivotMatrix1444 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def pivotMatrix1445 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, -1, 5], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1446 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix1447 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix1448 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1449 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix1450 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def pivotMatrix1451 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def pivotMatrix1452 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix1453 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, -1, 5], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix1454 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def pivotMatrix1455 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def pivotMatrix1456 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def pivotMatrix1457 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def pivotMatrix1458 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def pivotMatrix1459 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def pivotMatrix1460 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def pivotMatrix1461 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def pivotMatrix1462 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def pivotMatrix1463 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def pivotMatrix1464 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix1465 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def pivotMatrix1466 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def pivotMatrix1467 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def pivotMatrix1468 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1469 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix1470 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1471 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1472 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def pivotMatrix1473 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 0, 0, -2]]

def pivotMatrix1474 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def pivotMatrix1475 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def pivotMatrix1476 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1477 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix1478 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix1479 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def pivotMatrix1480 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix1481 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def pivotMatrix1482 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def pivotMatrix1483 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def pivotMatrix1484 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def pivotMatrix1485 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def pivotMatrix1486 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def pivotMatrix1487 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix1488 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def pivotMatrix1489 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def pivotMatrix1490 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix1491 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 1, -3]]

def pivotMatrix1492 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def pivotMatrix1493 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def pivotMatrix1494 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def pivotMatrix1495 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def pivotMatrix1496 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix1497 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix1498 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def pivotMatrix1499 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1500 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1501 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix1502 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix1503 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def pivotMatrix1504 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1505 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix1506 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix1507 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def pivotMatrix1508 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix1509 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def pivotMatrix1510 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix1511 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix1512 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 1, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix1513 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 1, 3], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix1514 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix1515 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1516 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 2, 2], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix1517 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def pivotMatrix1518 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix1519 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1520 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix1521 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1522 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -2, 2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def pivotMatrix1523 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -2, 2, 2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix1524 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 2, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix1525 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -2, 2, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix1526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix1527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix1528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix1530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix1531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1532 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def pivotMatrix1533 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix1534 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1535 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1536 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def pivotMatrix1537 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix1538 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1539 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1540 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1541 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def pivotMatrix1542 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1543 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix1544 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def pivotMatrix1545 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def pivotMatrix1546 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix1547 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def pivotMatrix1548 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def pivotMatrix1549 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def pivotMatrix1550 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def pivotMatrix1551 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def pivotMatrix1552 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def pivotMatrix1553 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def pivotMatrix1554 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix1555 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix1556 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def pivotMatrix1557 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1558 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix1559 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1560 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix1561 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix1562 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix1563 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def pivotMatrix1564 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def pivotMatrix1565 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def pivotMatrix1566 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def pivotMatrix1567 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def pivotMatrix1568 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def pivotMatrix1569 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def pivotMatrix1570 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def pivotMatrix1571 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def pivotMatrix1572 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1573 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1574 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def pivotMatrix1575 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix1576 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix1577 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def pivotMatrix1578 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def pivotMatrix1579 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def pivotMatrix1580 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix1581 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix1582 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def pivotMatrix1583 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -1, -1, 0]]

def pivotMatrix1584 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def pivotMatrix1585 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def pivotMatrix1586 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def pivotMatrix1587 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def pivotMatrix1588 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def pivotMatrix1589 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def pivotMatrix1590 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def pivotMatrix1591 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def pivotMatrix1592 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix1593 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -2, 0]]

def pivotMatrix1594 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def pivotMatrix1595 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix1596 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def pivotMatrix1597 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix1598 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def pivotMatrix1599 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1600 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def pivotMatrix1601 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def pivotMatrix1602 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def pivotMatrix1603 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix1604 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix1605 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, -1, 4], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix1606 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def pivotMatrix1607 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def pivotMatrix1608 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def pivotMatrix1609 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def pivotMatrix1610 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def pivotMatrix1611 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def pivotMatrix1612 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def pivotMatrix1613 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix1614 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix1615 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def pivotMatrix1616 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix1617 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, -1, 4], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix1618 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def pivotMatrix1619 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def pivotMatrix1620 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 2, -2], ![2, 1, 0, -3]]

def pivotMatrix1621 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def pivotMatrix1622 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def pivotMatrix1623 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, -1, -1]]

def pivotMatrix1624 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def pivotMatrix1625 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix1626 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def pivotMatrix1627 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def pivotMatrix1628 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def pivotMatrix1629 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def pivotMatrix1630 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def pivotMatrix1631 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def pivotMatrix1632 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def pivotMatrix1633 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def pivotMatrix1634 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def pivotMatrix1635 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def pivotMatrix1636 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def pivotMatrix1637 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix1638 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def pivotMatrix1639 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def pivotMatrix1640 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix1641 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix1642 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def pivotMatrix1643 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix1644 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 0, 3], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def pivotMatrix1645 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def pivotMatrix1646 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def pivotMatrix1647 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1648 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix1649 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix1650 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def pivotMatrix1651 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def pivotMatrix1652 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix1653 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix1654 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix1655 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix1656 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def pivotMatrix1657 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def pivotMatrix1658 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 2, 0, -3]]

def pivotMatrix1659 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 2, 0, -3]]

def pivotMatrix1660 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def pivotMatrix1661 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def pivotMatrix1662 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 2, -2]]

def pivotMatrix1663 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1664 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, -1, 1, -2]]

def pivotMatrix1665 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -1, -2]]

def pivotMatrix1666 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def pivotMatrix1667 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 3, -4]]

def pivotMatrix1668 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def pivotMatrix1669 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix1670 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def pivotMatrix1671 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 0, 3], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix1672 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def pivotMatrix1673 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def pivotMatrix1674 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def pivotMatrix1675 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def pivotMatrix1676 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def pivotMatrix1677 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def pivotMatrix1678 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix1679 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def pivotMatrix1680 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def pivotMatrix1681 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def pivotMatrix1682 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def pivotMatrix1683 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix1684 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def pivotMatrix1685 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def pivotMatrix1686 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix1687 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix1688 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix1689 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def pivotMatrix1690 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix1691 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def pivotMatrix1692 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 1, -2]]

def pivotMatrix1693 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def pivotMatrix1694 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def pivotMatrix1695 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def pivotMatrix1696 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def pivotMatrix1697 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def pivotMatrix1698 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix1699 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def pivotMatrix1700 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def pivotMatrix1701 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix1702 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix1703 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def pivotMatrix1704 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def pivotMatrix1705 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def pivotMatrix1706 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def pivotMatrix1707 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def pivotMatrix1708 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def pivotMatrix1709 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def pivotMatrix1710 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def pivotMatrix1711 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def pivotMatrix1712 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def pivotMatrix1713 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def pivotMatrix1714 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def pivotMatrix1715 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def pivotMatrix1716 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def pivotMatrix1717 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def pivotMatrix1718 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def pivotMatrix1719 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix1720 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def pivotMatrix1721 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def pivotMatrix1722 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix1723 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix1724 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 0, 3], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def pivotMatrix1725 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def pivotMatrix1726 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix1727 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1728 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def pivotMatrix1729 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1730 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix1731 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1732 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1733 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def pivotMatrix1734 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def pivotMatrix1735 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix1736 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def pivotMatrix1737 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def pivotMatrix1738 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def pivotMatrix1739 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def pivotMatrix1740 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix1741 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def pivotMatrix1742 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def pivotMatrix1743 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def pivotMatrix1744 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix1745 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix1746 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def pivotMatrix1747 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1748 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def pivotMatrix1749 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def pivotMatrix1750 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def pivotMatrix1751 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def pivotMatrix1752 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def pivotMatrix1753 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def pivotMatrix1754 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def pivotMatrix1755 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def pivotMatrix1756 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def pivotMatrix1757 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def pivotMatrix1758 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix1759 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def pivotMatrix1760 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def pivotMatrix1761 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def pivotMatrix1762 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def pivotMatrix1763 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def pivotMatrix1764 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def pivotMatrix1765 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def pivotMatrix1766 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def pivotMatrix1767 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def pivotMatrix1768 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix1769 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def pivotMatrix1770 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def pivotMatrix1771 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix1772 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix1773 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix1774 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix1775 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def pivotMatrix1776 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix1777 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix1778 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 1, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix1779 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def pivotMatrix1780 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def pivotMatrix1781 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def pivotMatrix1782 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def pivotMatrix1783 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def pivotMatrix1784 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def pivotMatrix1785 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def pivotMatrix1786 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def pivotMatrix1787 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def pivotMatrix1788 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def pivotMatrix1789 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def pivotMatrix1790 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix1791 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1792 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def pivotMatrix1793 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix1794 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def pivotMatrix1795 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def pivotMatrix1796 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def pivotMatrix1797 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix1798 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix1799 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def pivotMatrix1800 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def pivotMatrix1801 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix1802 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def pivotMatrix1803 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix1804 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix1805 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def pivotMatrix1806 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def pivotMatrix1807 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def pivotMatrix1808 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def pivotMatrix1809 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, -1, 0]]

def pivotMatrix1810 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def pivotMatrix1811 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def pivotMatrix1812 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def pivotMatrix1813 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def pivotMatrix1814 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def pivotMatrix1815 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def pivotMatrix1816 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def pivotMatrix1817 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def pivotMatrix1818 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def pivotMatrix1819 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix1820 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def pivotMatrix1821 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def pivotMatrix1822 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def pivotMatrix1823 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def pivotMatrix1824 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def pivotMatrix1825 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def pivotMatrix1826 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix1827 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix1828 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix1829 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def pivotMatrix1830 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def pivotMatrix1831 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def pivotMatrix1832 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def pivotMatrix1833 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def pivotMatrix1834 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix1835 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def pivotMatrix1836 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def pivotMatrix1837 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix1838 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix1839 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def pivotMatrix1840 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def pivotMatrix1841 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def pivotMatrix1842 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, -1, 2, 1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def pivotMatrix1843 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def pivotMatrix1844 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, -1, 2, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def pivotMatrix1845 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def pivotMatrix1846 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def pivotMatrix1847 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 2, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def pivotMatrix1848 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, -1, 2, 1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def pivotMatrix1849 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def pivotMatrix1850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def pivotMatrix1851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def pivotMatrix1852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def pivotMatrix1853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def pivotMatrix1854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix1855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix1857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def pivotMatrix1858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def pivotMatrix1859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix1860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix1861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix1862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def pivotMatrix1863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1864 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]

def pivotMatrix1865 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def pivotMatrix1866 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def pivotMatrix1867 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix1868 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1869 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1870 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def pivotMatrix1871 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1872 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1873 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def pivotMatrix1874 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def pivotMatrix1875 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def pivotMatrix1876 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def pivotMatrix1877 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def pivotMatrix1878 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1879 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1880 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def pivotMatrix1881 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def pivotMatrix1882 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def pivotMatrix1883 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def pivotMatrix1884 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def pivotMatrix1885 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def pivotMatrix1886 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix1887 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix1888 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]

def pivotMatrix1889 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def pivotMatrix1890 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def pivotMatrix1891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def pivotMatrix1892 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def pivotMatrix1893 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def pivotMatrix1894 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def pivotMatrix1895 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def pivotMatrix1896 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def pivotMatrix1897 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1898 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def pivotMatrix1899 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def pivotMatrix1900 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def pivotMatrix1901 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def pivotMatrix1902 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def pivotMatrix1903 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

def pivotMatrix1904 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def pivotMatrix1905 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def pivotMatrix1906 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def pivotMatrix1907 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def pivotMatrix1908 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def pivotMatrix1909 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def pivotMatrix1910 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def pivotMatrix1911 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix1912 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def pivotMatrix1913 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def pivotMatrix1914 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def pivotMatrix1915 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def pivotMatrix1916 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -2, 4], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix1917 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def pivotMatrix1918 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 1, -1]]

def pivotMatrix1919 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotMatrix1920 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def pivotMatrix1921 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def pivotMatrix1922 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def pivotMatrix1923 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def pivotMatrix1924 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def pivotMatrix1925 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def pivotMatrix1926 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def pivotMatrix1927 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix1928 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def pivotMatrix1929 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def pivotMatrix1930 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def pivotMatrix1931 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def pivotMatrix1932 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def pivotMatrix1933 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def pivotMatrix1934 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def pivotMatrix1935 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def pivotMatrix1936 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def pivotMatrix1937 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def pivotMatrix1938 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def pivotMatrix1939 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -2, 4], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def pivotMatrix1940 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def pivotMatrix1941 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def pivotMatrix1942 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def pivotMatrix1943 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def pivotMatrix1944 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def pivotMatrix1945 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def pivotMatrix1946 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def pivotMatrix1947 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def pivotMatrix1948 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def pivotMatrix1949 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def pivotMatrix1950 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def pivotMatrix1951 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

def coordinateChunk4 : Array (Fin 909) := #[751, 753, 760, 764, 783, 784, 794, 796, 798, 810, 811, 812, 818, 855, 870]

end MUB6.Certificate.PairSourceBridge

end OAI
end


