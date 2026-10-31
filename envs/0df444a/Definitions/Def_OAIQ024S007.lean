-- Prove2me | Definitions.Def_OAIQ024S007
-- name    : OAIQ024S007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:20:41.262179+00:00
-- url     : https://prove2.me/theorems/a91ae965-857e-47d3-af4d-35ecc233b9f4
-- title:
--   Definitions bundle OAIQ024S007 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 11 definitions. The definitions and types are `OAI.SKRatio.Certificate.Data.J2K5.blocks`, `OAI.SKRatio.Certificate.Data.J2K7.blocks`, `OAI.SKRatio.Certificate.Data.J3K0.blocks`, `OAI.SKRatio.Certificate.Data.J3K3.expression`, `OAI.SKRatio.Certificate.Data.J4K10.expression`, `OAI.SKRatio.Certificate.Data.J4K11.expression`, `OAI.SKRatio.Certificate.Data.J4K3.expression`, `OAI.SKRatio.Certificate.Jet.add`, `OAI.SKRatio.Certificate.Jet.exp`, `OAI.SKRatio.Certificate.Jet.inv`, `OAI.SKRatio.Certificate.Jet.mul`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: [`SKRatio_Certificates_CertifiedJet`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/CertifiedJet.lean), [`SKRatio_Certificates_ScalarDataJ2K5`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ2K5.lean), [`SKRatio_Certificates_ScalarDataJ2K7`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ2K7.lean), [`SKRatio_Certificates_ScalarDataJ3K0`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ3K0.lean), [`SKRatio_Certificates_ScalarDataJ3K3`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ3K3.lean), [`SKRatio_Certificates_ScalarDataJ4K10`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K10.lean), [`SKRatio_Certificates_ScalarDataJ4K11`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K11.lean), [`SKRatio_Certificates_ScalarDataJ4K3`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K3.lean).
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

def add (A B : Jet) : Jet := ⟨Box.add A.val B.val,Box.add A.der B.der,Box.add A.sec B.sec⟩
def mul (A B : Jet) : Jet :=
  ⟨Box.mul A.val B.val,
   Box.add (Box.mul A.der B.val) (Box.mul A.val B.der),
   Box.add (Box.add (Box.mul A.sec B.val) (Box.mul (Box.rat 2) (Box.mul A.der B.der))) (Box.mul A.val B.sec)⟩
def inv (A : Jet) : Option Jet := do
  let B ← Box.inv A.val
  return ⟨B,Box.neg (Box.mul A.der (Box.sq B)),
    Box.sub (Box.mul (Box.rat 2) (Box.mul (Box.sq A.der) (Box.mul B (Box.sq B)))) (Box.mul A.sec (Box.sq B))⟩
def exp (A : Jet) : Option Jet := do
  let B ← Box.exp A.val
  return ⟨B,Box.mul B A.der,Box.mul B (Box.add A.sec (Box.sq A.der))⟩

end Jet

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ2K5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J2K5

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
  | 10 => ⟨1/1000000,3/1000000⟩
  | 11 => ⟨1/62500,9/500000⟩
  | 12 => ⟨53/500000,11/100000⟩
  | 13 => ⟨249/500000,507/1000000⟩
  | 14 => ⟨1661/1000000,419/250000⟩
  | 15 => ⟨37/10000,93/25000⟩
  | 16 => ⟨983/200000,2481/500000⟩
  | 17 => ⟨1493/500000,1511/500000⟩
  | 18 => ⟨161/500000,373/1000000⟩
  | 19 => ⟨873/500000,1783/1000000⟩
  | 20 => ⟨3691/1000000,1883/500000⟩
  | 21 => ⟨53/31250,899/500000⟩
  | 22 => ⟨69/1000000,117/500000⟩
  | 23 => ⟨993/1000000,57/50000⟩
  | 24 => ⟨767/500000,1649/1000000⟩
  | 25 => ⟨97/100000,41/40000⟩
  | 26 => ⟨351/1000000,47/125000⟩
  | 27 => ⟨83/1000000,23/250000⟩
  | 28 => ⟨13/1000000,1/62500⟩
  | 29 => ⟨1/1000000,3/1000000⟩
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

end SKRatio.Certificate.Data.J2K5

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ2K7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J2K7

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
  | 9 => ⟨1/250000,3/500000⟩
  | 10 => ⟨3/62500,13/250000⟩
  | 11 => ⟨399/1000000,207/500000⟩
  | 12 => ⟨2569/1000000,527/200000⟩
  | 13 => ⟨1283/100000,6529/500000⟩
  | 14 => ⟨12191/250000,493/10000⟩
  | 15 => ⟨67813/500000,13631/100000⟩
  | 16 => ⟨16061/62500,6453/25000⟩
  | 17 => ⟨7353/25000,296147/1000000⟩
  | 18 => ⟨19569/125000,9851/62500⟩
  | 19 => ⟨1947/125000,543/31250⟩
  | 20 => ⟨70169/1000000,1781/25000⟩
  | 21 => ⟨11569/62500,186983/1000000⟩
  | 22 => ⟨186533/1000000,188099/1000000⟩
  | 23 => ⟨22261/200000,112401/1000000⟩
  | 24 => ⟨5811/125000,23713/500000⟩
  | 25 => ⟨3717/250000,7679/500000⟩
  | 26 => ⟨3791/1000000,3973/1000000⟩
  | 27 => ⟨389/500000,83/100000⟩
  | 28 => ⟨127/1000000,7/50000⟩
  | 29 => ⟨1/62500,19/1000000⟩
  | 30 => ⟨1/1000000,3/1000000⟩
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

end SKRatio.Certificate.Data.J2K7

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K0

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
  | 11 => ⟨7/1000000,9/1000000⟩
  | 12 => ⟨87/1000000,23/250000⟩
  | 13 => ⟨737/1000000,761/1000000⟩
  | 14 => ⟨471/100000,4813/1000000⟩
  | 15 => ⟨2253/100000,11421/500000⟩
  | 16 => ⟨79433/1000000,8001/100000⟩
  | 17 => ⟨202701/1000000,203171/1000000⟩
  | 18 => ⟨183977/500000,14739/40000⟩
  | 19 => ⟨235497/500000,472147/1000000⟩
  | 20 => ⟨85153/200000,213319/500000⟩
  | 21 => ⟨274223/1000000,274629/1000000⟩
  | 22 => ⟨127561/1000000,12827/100000⟩
  | 23 => ⟨43669/1000000,44229/1000000⟩
  | 24 => ⟨559/50000,11453/1000000⟩
  | 25 => ⟨433/200000,2261/1000000⟩
  | 26 => ⟨319/1000000,69/200000⟩
  | 27 => ⟨7/200000,21/500000⟩
  | 28 => ⟨1/500000,1/200000⟩
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

end SKRatio.Certificate.Data.J3K0

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K3

def expression : Expr := integrandExpr (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 3

end SKRatio.Certificate.Data.J3K3

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K10

def expression : Expr := integrandExpr (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 10

end SKRatio.Certificate.Data.J4K10

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K11

def expression : Expr := integrandExpr (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 11

end SKRatio.Certificate.Data.J4K11

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K3

def expression : Expr := integrandExpr (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 3

end SKRatio.Certificate.Data.J4K3

end

end OAI
end


