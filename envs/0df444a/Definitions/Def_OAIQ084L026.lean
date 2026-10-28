-- Prove2me | Definitions.Def_OAIQ084L026
-- name    : OAIQ084L026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:32:03.75606+00:00
-- url     : https://prove2.me/theorems/378138ed-5867-417b-a940-9492efcb1f60
-- title:
--   Definitions bundle OAIQ084L026 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.LaughlinFock.fourLData_7`, `OAI.LaughlinFock.fourLData_8`, `OAI.LaughlinFock.fourLData_9`, `OAI.LaughlinFock.fourPivotData_18`, `OAI.LaughlinFock.fourZData_2`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_Certificate02`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate02.lean), [`LaughlinFock_Certificate07Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate07Data.lean), [`LaughlinFock_Certificate08Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate08Data.lean), [`LaughlinFock_Certificate09Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate09Data.lean), [`LaughlinFock_Certificate18Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/Certificate18Data.lean).
--
--   **Imports.** It imports the bundles `OAIQ084L007` and `OAIQ084L012` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.LaughlinFock.certificate_four`, `OAI.LaughlinFock.integer_certificate_18`, `OAI.LaughlinFock.integer_certificate_8` and `OAI.LaughlinFock.integer_certificate_9`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ084L007
import Definitions.Def_OAIQ084L012

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate02. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourZData_2 : Matrix (CopyLabel 2) (CopyLabel 2) ℚ :=
  copyMatrixData 2 [
    [0]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate07Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate07 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourLData_7 : Matrix (CopyLabel 7) (CopyLabel 7) ℚ :=
  copyMatrixData 7 [
    [1, 0, 0, 0],
    [0, 1, 0, 0],
    [(-1/16), 0, 1, 0],
    [(7/32), 0, 0, 1]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate08Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate08 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourLData_8 : Matrix (CopyLabel 8) (CopyLabel 8) ℚ :=
  copyMatrixData 8 [
    [1, 0, 0, 0],
    [0, 1, 0, 0],
    [0, (-1/2), 1, 0],
    [0, (7/16), 0, 1]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate09Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate09 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourLData_9 : Matrix (CopyLabel 9) (CopyLabel 9) ℚ :=
  copyMatrixData 9 [
    [1, 0, 0, 0, 0],
    [(37662092511230861665070264137/10232154760876942507977290094024), 1, 0, 0, 0],
    [(-37662092511230861665070264137/40928619043507770031909160376096), (-1/4), 1, 0, 0],
    [(-1/64), 0, 0, 1, 0],
    [(91990693387227940258827681287/852679563406411875664774174502), (21/32), 0, 0, 1]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate18Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate18 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourPivotData_18 : CopyLabel 18 → ℚ :=
  copyDiagonalData 18 [0, (529420090801322601943717510296441/1342177280000000000000000), (1825508977455450555482950761488085609309912116452353/939190534155657292386245961318400000000000000), (634112851077230835083076540751443720400590647267061851980158422784839038977/264413005479661783187925833055772197996063252341692825600000000000000), (1805223415065741149552457967199157259864225890085126920594418139801440468653639717926856458667/14689184830089407840620485026734484503843164384846111492635426800841768960000000000000000), (44794141803382999890132162011222314683603629634860904805225482207148310449269562829938841063801523/732723746690172410470962146368056949475623112784066325889815517034689443240682501792408314839040), 0, 0, 0]

end LaughlinFock
end

end OAI
end


