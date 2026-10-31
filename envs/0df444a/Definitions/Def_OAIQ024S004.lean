-- Prove2me | Definitions.Def_OAIQ024S004
-- name    : OAIQ024S004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:19:11.772261+00:00
-- url     : https://prove2.me/theorems/50874693-7579-45a9-b358-f11a480e8ced
-- title:
--   Definitions bundle OAIQ024S004 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 20 definitions and 1 instance. The definitions and types are `OAI.SKRatio.Certificate.Data.J1K2.blocks`, `OAI.SKRatio.Certificate.Data.J1K3.blocks`, `OAI.SKRatio.Certificate.Data.J1K5.blocks`, `OAI.SKRatio.Certificate.Data.J1K5.expression`, `OAI.SKRatio.Certificate.Data.J1K7.expression`, `OAI.SKRatio.Certificate.Data.J2K1.expression`, `OAI.SKRatio.Certificate.Data.J2K2.expression`, `OAI.SKRatio.Certificate.Data.J2K3.expression`, `OAI.SKRatio.Certificate.Data.J2K4.expression`, `OAI.SKRatio.Certificate.Data.J2K5.expression`, `OAI.SKRatio.Certificate.Data.J2K7.expression`, `OAI.SKRatio.Certificate.Data.J3K0.expression`, `OAI.SKRatio.Certificate.Data.J3K1.expression`, `OAI.SKRatio.Certificate.Data.J3K2.expression`, `OAI.SKRatio.Certificate.Data.J3K4.expression`, `OAI.SKRatio.Certificate.Expr.der`, `OAI.SKRatio.Certificate.Fixed.Mem`, `OAI.SKRatio.Scalar.G`, `OAI.SKRatio.Scalar.R`, `OAI.SKRatio.Scalar.a`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `SKRatio_Certificates_CertifiedFunctions`, `SKRatio_Certificates_CertifiedJet`, `SKRatio_Certificates_FixedExp`, `SKRatio_Certificates_ScalarDataJ1K2`, `SKRatio_Certificates_ScalarDataJ1K3`, `SKRatio_Certificates_ScalarDataJ1K5`, `SKRatio_Certificates_ScalarDataJ1K7`, `SKRatio_Certificates_ScalarDataJ2K1`, `SKRatio_Certificates_ScalarDataJ2K2`, `SKRatio_Certificates_ScalarDataJ2K3`, `SKRatio_Certificates_ScalarDataJ2K4`, `SKRatio_Certificates_ScalarDataJ2K5`, `SKRatio_Certificates_ScalarDataJ2K7`, `SKRatio_Certificates_ScalarDataJ3K0`, `SKRatio_Certificates_ScalarDataJ3K1`, `SKRatio_Certificates_ScalarDataJ3K2`, `SKRatio_Certificates_ScalarDataJ3K4`, `SKRatio_Variational_ScalarCoherent`.
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
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_FixedExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real
namespace SKRatio.Certificate.Fixed

def Mem (A : I) (x : ℝ) : Prop := (A.lo:ℝ)/(S:ℝ) ≤ x ∧ x ≤ (A.hi:ℝ)/(S:ℝ)
end SKRatio.Certificate.Fixed

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedJet
attribute [-instance] _root_.OAI.SKRatio.Certificate.Expr.instAdd _root_.OAI.SKRatio.Certificate.Expr.instDiv _root_.OAI.SKRatio.Certificate.Expr.instMul _root_.OAI.SKRatio.Certificate.Expr.instOfNat _root_.OAI.SKRatio.Certificate.Expr.instSub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real
namespace SKRatio.Certificate

namespace Expr

def der (e : Expr) (x : ℝ) : ℝ := match e with
  | rat _ => 0
  | var => 1
  | add a b => a.der x+b.der x
  | neg a => -a.der x
  | mul a b => a.der x*b.val x+a.val x*b.der x
  | sq a => 2*a.val x*a.der x
  | inv a => -a.der x*((a.val x)⁻¹)^2
  | exp a => Real.exp (a.val x)*a.der x
  | tanh a => (1-(Real.tanh (a.val x))^2)*a.der x

end Expr
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

def a (β : ℝ) : ℝ := ∫ h, v h ∂fieldLaw β

def G (β : ℝ) : ℝ := ∫ h, g h ∂fieldLaw β

def R (β : ℝ) : ℝ := ∫ h, rho h ∂fieldLaw β

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate
open Scalar

namespace Expr
instance instNeg : Neg Expr := ⟨Expr.neg⟩
end Expr

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K2

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
  | 10 => ⟨-1/500000,0⟩
  | 11 => ⟨-13/1000000,-11/1000000⟩
  | 12 => ⟨-57/500000,-109/1000000⟩
  | 13 => ⟨-811/1000000,-789/1000000⟩
  | 14 => ⟨-2121/500000,-4171/1000000⟩
  | 15 => ⟨-15871/1000000,-1967/125000⟩
  | 16 => ⟨-40599/1000000,-40483/1000000⟩
  | 17 => ⟨-16293/250000,-32403/500000⟩
  | 18 => ⟨-48501/1000000,-47957/1000000⟩
  | 19 => ⟨911/31250,147/5000⟩
  | 20 => ⟨6969/62500,112111/1000000⟩
  | 21 => ⟨32273/250000,129669/1000000⟩
  | 22 => ⟨43943/500000,17627/200000⟩
  | 23 => ⟨159/4000,10019/250000⟩
  | 24 => ⟨6323/500000,12869/1000000⟩
  | 25 => ⟨117/40000,3017/1000000⟩
  | 26 => ⟨251/500000,529/1000000⟩
  | 27 => ⟨1/15625,71/1000000⟩
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

end SKRatio.Certificate.Data.J1K2

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K3

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
  | 12 => ⟨1/1000000,1/500000⟩
  | 13 => ⟨3/200000,9/500000⟩
  | 14 => ⟨61/500000,129/1000000⟩
  | 15 => ⟨13/20000,673/1000000⟩
  | 16 => ⟨1163/500000,2373/1000000⟩
  | 17 => ⟨5209/1000000,2641/500000⟩
  | 18 => ⟨6441/1000000,3279/500000⟩
  | 19 => ⟨159/50000,3293/1000000⟩
  | 20 => ⟨129/500000,131/250000⟩
  | 21 => ⟨791/200000,2177/500000⟩
  | 22 => ⟨221/25000,4693/500000⟩
  | 23 => ⟨101/12500,8569/1000000⟩
  | 24 => ⟨4141/1000000,4407/1000000⟩
  | 25 => ⟨669/500000,1437/1000000⟩
  | 26 => ⟨29/100000,319/1000000⟩
  | 27 => ⟨43/1000000,51/1000000⟩
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

end SKRatio.Certificate.Data.J1K3

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K5

def expression : Expr := integrandExpr (2/5) (107581/125000) (545767/1000000) (95751/1000000) (616697/1000000) 5
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
  | 11 => ⟨3/200000,17/1000000⟩
  | 12 => ⟨1/10000,13/125000⟩
  | 13 => ⟨93/200000,473/1000000⟩
  | 14 => ⟨761/500000,307/200000⟩
  | 15 => ⟨3357/1000000,27/8000⟩
  | 16 => ⟨181/40000,913/200000⟩
  | 17 => ⟨749/250000,3027/1000000⟩
  | 18 => ⟨217/500000,473/1000000⟩
  | 19 => ⟨249/250000,16/15625⟩
  | 20 => ⟨1431/500000,91/31250⟩
  | 21 => ⟨471/250000,1941/1000000⟩
  | 22 => ⟨177/1000000,11/40000⟩
  | 23 => ⟨157/500000,399/1000000⟩
  | 24 => ⟨403/500000,877/1000000⟩
  | 25 => ⟨627/1000000,133/200000⟩
  | 26 => ⟨13/50000,11/40000⟩
  | 27 => ⟨67/1000000,37/500000⟩
  | 28 => ⟨3/250000,7/500000⟩
  | 29 => ⟨1/1000000,1/500000⟩
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

end SKRatio.Certificate.Data.J1K5

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

def expression : Expr := integrandExpr (2/5) (107581/125000) (545767/1000000) (95751/1000000) (616697/1000000) 7

end SKRatio.Certificate.Data.J1K7

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

def expression : Expr := integrandExpr (89/200) (52021/62500) (13423/25000) (21477/200000) (81561/125000) 1

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

def expression : Expr := integrandExpr (89/200) (52021/62500) (13423/25000) (21477/200000) (81561/125000) 2

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

def expression : Expr := integrandExpr (89/200) (52021/62500) (13423/25000) (21477/200000) (81561/125000) 3

end SKRatio.Certificate.Data.J2K3

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

def expression : Expr := integrandExpr (89/200) (52021/62500) (13423/25000) (21477/200000) (81561/125000) 4

end SKRatio.Certificate.Data.J2K4

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

def expression : Expr := integrandExpr (89/200) (52021/62500) (13423/25000) (21477/200000) (81561/125000) 5

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

def expression : Expr := integrandExpr (89/200) (52021/62500) (13423/25000) (21477/200000) (81561/125000) 7

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

def expression : Expr := integrandExpr (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 0

end SKRatio.Certificate.Data.J3K0

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K1

def expression : Expr := integrandExpr (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 1

end SKRatio.Certificate.Data.J3K1

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K2

def expression : Expr := integrandExpr (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 2

end SKRatio.Certificate.Data.J3K2

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K4

def expression : Expr := integrandExpr (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 4

end SKRatio.Certificate.Data.J3K4

end

end OAI
end


