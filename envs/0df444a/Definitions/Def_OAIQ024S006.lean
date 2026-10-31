-- Prove2me | Definitions.Def_OAIQ024S006
-- name    : OAIQ024S006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:20:27.578982+00:00
-- url     : https://prove2.me/theorems/2550f97c-c02e-473b-8af6-c284bba6fe44
-- title:
--   Definitions bundle OAIQ024S006 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 10 definitions. The definitions and types are `OAI.SKRatio.Certificate.Data.J2K1.blocks`, `OAI.SKRatio.Certificate.Data.J2K2.blocks`, `OAI.SKRatio.Certificate.Data.J2K3.blocks`, `OAI.SKRatio.Certificate.Data.J2K6.blocks`, `OAI.SKRatio.Certificate.Data.J2K6.expression`, `OAI.SKRatio.Certificate.X2`, `OAI.SKRatio.Certificate.X3`, `OAI.SKRatio.Certificate.X4`, `OAI.SKRatio.Certificate.normalizedBox`, `OAI.SKRatio.Certificate.normalizerBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: [`SKRatio_Certificates_CertifiedBatches`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/CertifiedBatches.lean), [`SKRatio_Certificates_CertifiedConstants`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/CertifiedConstants.lean), [`SKRatio_Certificates_ScalarDataJ2K1`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ2K1.lean), [`SKRatio_Certificates_ScalarDataJ2K2`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ2K2.lean), [`SKRatio_Certificates_ScalarDataJ2K3`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ2K3.lean), [`SKRatio_Certificates_ScalarDataJ2K6`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ2K6.lean).
--
--   **Imports.** It imports the bundle `OAIQ024S000` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ024S016`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ024S000

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedBatches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real Set MeasureTheory
namespace SKRatio.Certificate

def normalizerBox : Box := ⟨39894227/100000000,39894229/100000000⟩

def normalizedBox (B : Box) : Box := Box.mul normalizerBox (B.widen (1/1000000))

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

def X2 : Enclosures where
  av := ⟨207709/250000,208459/250000⟩
  gv := ⟨26771/50000,26921/50000⟩
  mv := ⟨21177/200000,21777/200000⟩
  rv := ⟨0,47/2000⟩
  vs := ⟨0,181/1000⟩
  gs := ⟨0,103/1000⟩
  ms := ⟨0,127/500⟩
  fs := ⟨0,397/500⟩

def X3 : Enclosures where
  av := ⟨405599/500000,407099/500000⟩
  gv := ⟨132171/250000,132921/250000⟩
  mv := ⟨7051/62500,14477/125000⟩
  rv := ⟨0,13/500⟩
  vs := ⟨0,49/250⟩
  gs := ⟨0,109/1000⟩
  ms := ⟨0,32/125⟩
  fs := ⟨0,207/250⟩

def X4 : Enclosures where
  av := ⟨397223/500000,398723/500000⟩
  gv := ⟨522571/1000000,525571/1000000⟩
  mv := ⟨118053/1000000,121053/1000000⟩
  rv := ⟨0,7/250⟩
  vs := ⟨0,209/1000⟩
  gs := ⟨0,23/200⟩
  ms := ⟨0,257/1000⟩
  fs := ⟨0,171/200⟩

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ2K1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J2K1

def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨-1/1000000,1/1000000⟩
  | 9 => ⟨-1/1000000,1/1000000⟩
  | 10 => ⟨0,1/1000000⟩
  | 11 => ⟨3/1000000,1/250000⟩
  | 12 => ⟨19/500000,41/1000000⟩
  | 13 => ⟨319/1000000,33/100000⟩
  | 14 => ⟨2037/1000000,2083/1000000⟩
  | 15 => ⟨2469/250000,10021/1000000⟩
  | 16 => ⟨18041/500000,1137/31250⟩
  | 17 => ⟨24537/250000,19699/200000⟩
  | 18 => ⟨196257/1000000,196459/1000000⟩
  | 19 => ⟨285153/1000000,142877/500000⟩
  | 20 => ⟨29937/100000,300131/1000000⟩
  | 21 => ⟨56613/250000,226887/1000000⟩
  | 22 => ⟨24687/200000,123957/1000000⟩
  | 23 => ⟨24387/500000,4933/100000⟩
  | 24 => ⟨3531/250000,2889/200000⟩
  | 25 => ⟨303/100000,631/200000⟩
  | 26 => ⟨243/500000,261/500000⟩
  | 27 => ⟨29/500000,67/1000000⟩
  | 28 => ⟨1/200000,7/1000000⟩
  | 29 => ⟨0,1/1000000⟩
  | 30 => ⟨-1/1000000,1/1000000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

end SKRatio.Certificate.Data.J2K1

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ2K2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J2K2

def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨-1/1000000,1/1000000⟩
  | 9 => ⟨-1/1000000,1/1000000⟩
  | 10 => ⟨-1/1000000,0⟩
  | 11 => ⟨-1/100000,-1/125000⟩
  | 12 => ⟨-19/200000,-9/100000⟩
  | 13 => ⟨-89/125000,-173/250000⟩
  | 14 => ⟨-3947/1000000,-969/250000⟩
  | 15 => ⟨-3889/250000,-1541/100000⟩
  | 16 => ⟨-41393/1000000,-8253/200000⟩
  | 17 => ⟨-33693/500000,-8371/125000⟩
  | 18 => ⟨-46641/1000000,-46029/1000000⟩
  | 19 => ⟨10371/250000,41771/1000000⟩
  | 20 => ⟨12771/100000,2007/15625⟩
  | 21 => ⟨136969/1000000,68799/500000⟩
  | 22 => ⟨86737/1000000,43527/500000⟩
  | 23 => ⟨36433/1000000,3683/100000⟩
  | 24 => ⟨10773/1000000,2203/200000⟩
  | 25 => ⟨29/12500,1207/500000⟩
  | 26 => ⟨371/1000000,199/500000⟩
  | 27 => ⟨11/250000,51/1000000⟩
  | 28 => ⟨3/1000000,3/500000⟩
  | 29 => ⟨0,1/1000000⟩
  | 30 => ⟨-1/1000000,1/1000000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

end SKRatio.Certificate.Data.J2K2

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ2K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J2K3

def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨-1/1000000,1/1000000⟩
  | 9 => ⟨-1/1000000,1/1000000⟩
  | 10 => ⟨-1/1000000,1/1000000⟩
  | 11 => ⟨-1/1000000,1/1000000⟩
  | 12 => ⟨0,1/500000⟩
  | 13 => ⟨11/1000000,13/1000000⟩
  | 14 => ⟨97/1000000,13/125000⟩
  | 15 => ⟨573/1000000,597/1000000⟩
  | 16 => ⟨2221/1000000,91/40000⟩
  | 17 => ⟨521/100000,5299/1000000⟩
  | 18 => ⟨1579/250000,6459/1000000⟩
  | 19 => ⟨2523/1000000,671/250000⟩
  | 20 => ⟨647/1000000,519/500000⟩
  | 21 => ⟨357/50000,1939/250000⟩
  | 22 => ⟨2527/200000,269/20000⟩
  | 23 => ⟨4979/500000,5311/500000⟩
  | 24 => ⟨4483/1000000,241/50000⟩
  | 25 => ⟨1283/1000000,351/250000⟩
  | 26 => ⟨247/1000000,141/500000⟩
  | 27 => ⟨33/1000000,21/500000⟩
  | 28 => ⟨1/500000,1/200000⟩
  | 29 => ⟨0,1/1000000⟩
  | 30 => ⟨-1/1000000,1/1000000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

end SKRatio.Certificate.Data.J2K3

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ2K6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J2K6

def expression : Expr := integrandExpr (89/200) (52021/62500) (13423/25000) (21477/200000) (81561/125000) 6
def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨-1/1000000,1/1000000⟩
  | 9 => ⟨-1/1000000,1/1000000⟩
  | 10 => ⟨0,1/1000000⟩
  | 11 => ⟨3/1000000,1/200000⟩
  | 12 => ⟨41/1000000,11/250000⟩
  | 13 => ⟨353/1000000,183/500000⟩
  | 14 => ⟨553/250000,113/50000⟩
  | 15 => ⟨4761/500000,77/8000⟩
  | 16 => ⟨25549/1000000,12831/500000⟩
  | 17 => ⟨4607/125000,9293/250000⟩
  | 18 => ⟨10651/500000,2687/125000⟩
  | 19 => ⟨399/200000,2297/1000000⟩
  | 20 => ⟨13057/1000000,531/40000⟩
  | 21 => ⟨3119/125000,12647/500000⟩
  | 22 => ⟨16689/1000000,3379/200000⟩
  | 23 => ⟨2737/500000,5687/1000000⟩
  | 24 => ⟨959/1000000,213/200000⟩
  | 25 => ⟨79/1000000,11/100000⟩
  | 26 => ⟨-1/1000000,7/1000000⟩
  | 27 => ⟨-1/1000000,1/1000000⟩
  | 28 => ⟨-1/1000000,1/1000000⟩
  | 29 => ⟨-1/1000000,1/1000000⟩
  | 30 => ⟨-1/1000000,1/1000000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

end SKRatio.Certificate.Data.J2K6

end

end OAI
end


