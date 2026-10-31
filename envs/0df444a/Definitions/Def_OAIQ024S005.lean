-- Prove2me | Definitions.Def_OAIQ024S005
-- name    : OAIQ024S005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:19:14.500743+00:00
-- url     : https://prove2.me/theorems/82fae391-3299-4a71-9f28-e52898cd4aea
-- title:
--   Definitions bundle OAIQ024S005 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 9 definitions. The definitions and types are `OAI.SKRatio.Certificate.Data.J1K6.blocks`, `OAI.SKRatio.Certificate.Data.J1K7.blocks`, `OAI.SKRatio.Certificate.Data.J2K0.blocks`, `OAI.SKRatio.Certificate.Data.J2K4.blocks`, `OAI.SKRatio.Certificate.Jet.rat`, `OAI.SKRatio.Certificate.Jet.sq`, `OAI.SKRatio.Certificate.Jet.tanh`, `OAI.SKRatio.Certificate.Jet.tanhBox`, `OAI.SKRatio.Certificate.Jet.var`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: [`SKRatio_Certificates_CertifiedJet`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/CertifiedJet.lean), [`SKRatio_Certificates_ScalarDataJ1K6`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ1K6.lean), [`SKRatio_Certificates_ScalarDataJ1K7`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ1K7.lean), [`SKRatio_Certificates_ScalarDataJ2K0`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ2K0.lean), [`SKRatio_Certificates_ScalarDataJ2K4`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ2K4.lean).
--
--   **Imports.** It imports the bundle `OAIQ024S000` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ024S016`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ024S000

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real
namespace SKRatio.Certificate

namespace Jet
open Box

def rat (q : ℚ) : Jet := ⟨Box.rat q,Box.rat 0,Box.rat 0⟩
def var (B : Box) : Jet := ⟨B,Box.rat 1,Box.rat 0⟩
def sq (A : Jet) : Jet := ⟨Box.sq A.val,Box.mul (Box.rat 2) (Box.mul A.val A.der),
  Box.mul (Box.rat 2) (Box.add (Box.sq A.der) (Box.mul A.val A.sec))⟩

def tanhBox (A : Box) : Option Box := do
  let E ← Box.exp (Box.mul (Box.rat 2) A)
  let D ← Box.inv (Box.add E (Box.rat 1))
  return Box.mul (Box.sub E (Box.rat 1)) D

def tanh (A : Jet) : Option Jet := do
  let B ← tanhBox A.val
  let V := Box.sub (Box.rat 1) (Box.sq B)
  return ⟨B,Box.mul V A.der,Box.sub (Box.mul V A.sec)
    (Box.mul (Box.rat 2) (Box.mul B (Box.mul V (Box.sq A.der))))⟩

end Jet

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K6

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
  | 12 => ⟨49/1000000,13/250000⟩
  | 13 => ⟨1/2500,413/1000000⟩
  | 14 => ⟨2343/1000000,2389/1000000⟩
  | 15 => ⟨937/100000,9457/1000000⟩
  | 16 => ⟨23607/1000000,4741/200000⟩
  | 17 => ⟨33071/1000000,3333/100000⟩
  | 18 => ⟨19919/1000000,803/40000⟩
  | 19 => ⟨1041/500000,2327/1000000⟩
  | 20 => ⟨4969/500000,10101/1000000⟩
  | 21 => ⟨5821/250000,11783/500000⟩
  | 22 => ⟨18807/1000000,1897/100000⟩
  | 23 => ⟨7711/1000000,7873/1000000⟩
  | 24 => ⟨227/125000,383/200000⟩
  | 25 => ⟨251/1000000,57/200000⟩
  | 26 => ⟨9/500000,13/500000⟩
  | 27 => ⟨0,1/500000⟩
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

end SKRatio.Certificate.Data.J1K6

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K7

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
  | 9 => ⟨1/250000,1/200000⟩
  | 10 => ⟨11/250000,3/62500⟩
  | 11 => ⟨369/1000000,383/1000000⟩
  | 12 => ⟨473/200000,1213/500000⟩
  | 13 => ⟨11663/1000000,5933/500000⟩
  | 14 => ⟨1733/40000,43781/1000000⟩
  | 15 => ⟨116837/1000000,58691/500000⟩
  | 16 => ⟨21459/100000,107769/500000⟩
  | 17 => ⟨241471/1000000,60761/250000⟩
  | 18 => ⟨131229/1000000,66019/500000⟩
  | 19 => ⟨2887/200000,7907/500000⟩
  | 20 => ⟨51879/1000000,10543/200000⟩
  | 21 => ⟨77211/500000,31151/200000⟩
  | 22 => ⟨42457/250000,34217/200000⟩
  | 23 => ⟨108519/1000000,109261/1000000⟩
  | 24 => ⟨23631/500000,9589/200000⟩
  | 25 => ⟨7649/500000,3921/250000⟩
  | 26 => ⟨1927/500000,4001/1000000⟩
  | 27 => ⟨771/1000000,813/1000000⟩
  | 28 => ⟨61/500000,33/250000⟩
  | 29 => ⟨3/200000,9/500000⟩
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

end SKRatio.Certificate.Data.J1K7

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ2K0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J2K0

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
  | 11 => ⟨9/1000000,11/1000000⟩
  | 12 => ⟨101/1000000,107/1000000⟩
  | 13 => ⟨827/1000000,853/1000000⟩
  | 14 => ⟨511/100000,2609/500000⟩
  | 15 => ⟨4741/200000,24017/1000000⟩
  | 16 => ⟨4071/50000,81981/1000000⟩
  | 17 => ⟨102009/500000,20447/100000⟩
  | 18 => ⟨14707/40000,184081/500000⟩
  | 19 => ⟨473169/1000000,237137/500000⟩
  | 20 => ⟨217631/500000,21807/50000⟩
  | 21 => ⟨57617/200000,288453/1000000⟩
  | 22 => ⟨138603/1000000,69631/500000⟩
  | 23 => ⟨4923/100000,49781/1000000⟩
  | 24 => ⟨3273/250000,13367/1000000⟩
  | 25 => ⟨527/200000,683/250000⟩
  | 26 => ⟨101/250000,43/100000⟩
  | 27 => ⟨47/1000000,53/1000000⟩
  | 28 => ⟨1/250000,3/500000⟩
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

end SKRatio.Certificate.Data.J2K0

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ2K4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J2K4

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
  | 11 => ⟨17/500000,9/250000⟩
  | 12 => ⟨99/500000,51/250000⟩
  | 13 => ⟨201/250000,163/200000⟩
  | 14 => ⟨83/40000,2093/1000000⟩
  | 15 => ⟨2857/1000000,2901/1000000⟩
  | 16 => ⟨1217/1000000,63/50000⟩
  | 17 => ⟨247/250000,1081/1000000⟩
  | 18 => ⟨2057/250000,4149/500000⟩
  | 19 => ⟨2901/250000,733/62500⟩
  | 20 => ⟨3337/1000000,867/250000⟩
  | 21 => ⟨2367/1000000,1283/500000⟩
  | 22 => ⟨1567/125000,3197/250000⟩
  | 23 => ⟨8221/500000,16721/1000000⟩
  | 24 => ⟨10971/1000000,2781/250000⟩
  | 25 => ⟨913/200000,2329/500000⟩
  | 26 => ⟨1303/1000000,21/15625⟩
  | 27 => ⟨67/250000,281/1000000⟩
  | 28 => ⟨1/25000,11/250000⟩
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

end SKRatio.Certificate.Data.J2K4

end

end OAI
end


