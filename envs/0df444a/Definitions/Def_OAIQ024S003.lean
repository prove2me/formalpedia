-- Prove2me | Definitions.Def_OAIQ024S003
-- name    : OAIQ024S003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:19:39.864167+00:00
-- url     : https://prove2.me/theorems/a01e880a-a8d2-454e-aa1f-5ab577580d3f
-- title:
--   Definitions bundle OAIQ024S003 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 definitions. The definitions and types are `OAI.SKRatio.Certificate.Data.J0K7.blocks`, `OAI.SKRatio.Certificate.Data.J1K0.blocks`, `OAI.SKRatio.Certificate.Data.J1K1.blocks`, `OAI.SKRatio.Certificate.Data.J1K4.blocks`, `OAI.SKRatio.Certificate.X0`, `OAI.SKRatio.Certificate.X1`, `OAI.SKRatio.Certificate.sumBoxes`, `OAI.SKRatio.Scalar.l`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: [`SKRatio_Certificates_CertifiedBatches`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/CertifiedBatches.lean), [`SKRatio_Certificates_CertifiedConstants`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/CertifiedConstants.lean), [`SKRatio_Certificates_ScalarDataJ0K7`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ0K7.lean), [`SKRatio_Certificates_ScalarDataJ1K0`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ1K0.lean), [`SKRatio_Certificates_ScalarDataJ1K1`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ1K1.lean), [`SKRatio_Certificates_ScalarDataJ1K4`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ1K4.lean), [`SKRatio_Variational_ScalarCoherent`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Variational/ScalarCoherent.lean).
--
--   **Imports.** It imports the bundles `OAIQ024S000` and `OAIQ024S001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ024S016`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ024S000
import Definitions.Def_OAIQ024S001

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

def sumBoxes (B : ℕ → Box) : ℕ → Box
  | 0 => Box.rat 0
  | n+1 => Box.add (sumBoxes B n) (B n)

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarCoherent
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def l (β : ℝ) : ℝ := ∫ h, multiplier h ∂fieldLaw β

end SKRatio.Scalar

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

def X0 : Enclosures where
  av := ⟨2777/3125,22291/25000⟩
  gv := ⟨110463/200000,111063/200000⟩
  mv := ⟨9979/125000,5177/62500⟩
  rv := ⟨0,33/2000⟩
  vs := ⟨0,13/100⟩
  gs := ⟨0,43/500⟩
  ms := ⟨0,239/1000⟩
  fs := ⟨0,333/500⟩

def X1 : Enclosures where
  av := ⟨214787/250000,215537/250000⟩
  gv := ⟨544267/1000000,547267/1000000⟩
  mv := ⟨94251/1000000,97251/1000000⟩
  rv := ⟨0,1/50⟩
  vs := ⟨0,157/1000⟩
  gs := ⟨0,19/200⟩
  ms := ⟨0,249/1000⟩
  fs := ⟨0,737/1000⟩

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K7

def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨0,1/1000000⟩
  | 9 => ⟨3/1000000,1/200000⟩
  | 10 => ⟨1/25000,43/1000000⟩
  | 11 => ⟨331/1000000,343/1000000⟩
  | 12 => ⟨2103/1000000,539/250000⟩
  | 13 => ⟨159/15625,10349/1000000⟩
  | 14 => ⟨36733/1000000,18551/500000⟩
  | 15 => ⟨95661/1000000,9607/100000⟩
  | 16 => ⟨169931/1000000,85339/500000⟩
  | 17 => ⟨187633/1000000,18879/100000⟩
  | 18 => ⟨103601/1000000,104181/1000000⟩
  | 19 => ⟨2517/200000,13583/1000000⟩
  | 20 => ⟨2251/62500,36649/1000000⟩
  | 21 => ⟨15061/125000,1517/12500⟩
  | 22 => ⟨144411/1000000,29073/200000⟩
  | 23 => ⟨99259/1000000,4989/50000⟩
  | 24 => ⟨45617/1000000,23043/500000⟩
  | 25 => ⟨15183/1000000,7737/500000⟩
  | 26 => ⟨767/200000,247/62500⟩
  | 27 => ⟨377/500000,197/250000⟩
  | 28 => ⟨117/1000000,1/8000⟩
  | 29 => ⟨7/500000,1/62500⟩
  | 30 => ⟨1/1000000,1/500000⟩
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

end SKRatio.Certificate.Data.J0K7

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K0

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
  | 10 => ⟨0,1/500000⟩
  | 11 => ⟨3/250000,7/500000⟩
  | 12 => ⟨127/1000000,133/1000000⟩
  | 13 => ⟨983/1000000,1011/1000000⟩
  | 14 => ⟨5779/1000000,5893/1000000⟩
  | 15 => ⟨2561/100000,6481/250000⟩
  | 16 => ⟨84641/1000000,42591/500000⟩
  | 17 => ⟨20639/100000,41363/200000⟩
  | 18 => ⟨45939/125000,367957/1000000⟩
  | 19 => ⟨237757/500000,9531/20000⟩
  | 20 => ⟨223663/500000,112051/250000⟩
  | 21 => ⟨307183/1000000,30751/100000⟩
  | 22 => ⟨154943/1000000,155529/1000000⟩
  | 23 => ⟨58037/1000000,58573/1000000⟩
  | 24 => ⟨16321/1000000,16603/1000000⟩
  | 25 => ⟨3477/1000000,3579/1000000⟩
  | 26 => ⟨113/200000,37/62500⟩
  | 27 => ⟨7/100000,19/250000⟩
  | 28 => ⟨3/500000,1/125000⟩
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

end SKRatio.Certificate.Data.J1K0

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K1

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
  | 11 => ⟨1/250000,3/500000⟩
  | 12 => ⟨3/62500,51/1000000⟩
  | 13 => ⟨6/15625,397/1000000⟩
  | 14 => ⟨2337/1000000,2387/1000000⟩
  | 15 => ⟨677/62500,10979/1000000⟩
  | 16 => ⟨37989/1000000,19141/500000⟩
  | 17 => ⟨3999/40000,12537/125000⟩
  | 18 => ⟨195577/1000000,195763/1000000⟩
  | 19 => ⟨281997/1000000,282549/1000000⟩
  | 20 => ⟨149257/500000,74803/250000⟩
  | 21 => ⟨231371/1000000,46351/200000⟩
  | 22 => ⟨3279/25000,26313/200000⟩
  | 23 => ⟨2181/40000,55011/1000000⟩
  | 24 => ⟨16743/1000000,8521/500000⟩
  | 25 => ⟨3827/1000000,3947/1000000⟩
  | 26 => ⟨41/62500,691/1000000⟩
  | 27 => ⟨21/250000,93/1000000⟩
  | 28 => ⟨1/125000,1/100000⟩
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

end SKRatio.Certificate.Data.J1K1

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K4

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
  | 9 => ⟨0,1/1000000⟩
  | 10 => ⟨1/250000,1/200000⟩
  | 11 => ⟨1/31250,7/200000⟩
  | 12 => ⟨23/125000,19/100000⟩
  | 13 => ⟨181/250000,367/500000⟩
  | 14 => ⟨1817/1000000,1833/1000000⟩
  | 15 => ⟨2481/1000000,1259/500000⟩
  | 16 => ⟨287/250000,591/500000⟩
  | 17 => ⟨537/1000000,151/250000⟩
  | 18 => ⟨1337/250000,1079/200000⟩
  | 19 => ⟨8343/1000000,8429/1000000⟩
  | 20 => ⟨29/10000,149/50000⟩
  | 21 => ⟨621/500000,691/500000⟩
  | 22 => ⟨8421/1000000,4289/500000⟩
  | 23 => ⟨3101/250000,6301/500000⟩
  | 24 => ⟨8983/1000000,9099/1000000⟩
  | 25 => ⟨997/250000,4059/1000000⟩
  | 26 => ⟨1197/1000000,1231/1000000⟩
  | 27 => ⟨4/15625,67/250000⟩
  | 28 => ⟨1/25000,43/1000000⟩
  | 29 => ⟨1/250000,3/500000⟩
  | 30 => ⟨0,1/1000000⟩
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

end SKRatio.Certificate.Data.J1K4

end

end OAI
end


