-- Prove2me | Definitions.Def_OAIQ024S008
-- name    : OAIQ024S008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:20:55.831502+00:00
-- url     : https://prove2.me/theorems/b6b8b61a-6e6f-404a-adfa-b664e27b4f90
-- title:
--   Definitions bundle OAIQ024S008 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 25 definitions and 2 instances. The definitions and types are `OAI.SKRatio.Certificate.Data.J3K1.blocks`, `OAI.SKRatio.Certificate.Data.J3K2.blocks`, `OAI.SKRatio.Certificate.Data.J3K3.blocks`, `OAI.SKRatio.Certificate.Data.J3K4.blocks`, `OAI.SKRatio.Certificate.Data.J3K5.expression`, `OAI.SKRatio.Certificate.Data.J3K6.expression`, `OAI.SKRatio.Planted.augmented`, `OAI.SKRatio.Planted.augmentedDiagonal`, `OAI.SKRatio.Planted.augmentedDisorder`, `OAI.SKRatio.Planted.augmentedField`, `OAI.SKRatio.Planted.badWeight`, `OAI.SKRatio.Planted.compactForm`, `OAI.SKRatio.Planted.deterministicForm`, `OAI.SKRatio.Planted.diagonalLaw`, `OAI.SKRatio.Planted.gauge`, `OAI.SKRatio.Planted.law`, `OAI.SKRatio.Planted.meanVarianceKernel`, `OAI.SKRatio.Planted.otherEnd`, `OAI.SKRatio.Planted.reducedForm`, `OAI.SKRatio.Planted.standardSample`, `OAI.SKRatio.Planted.varianceKernel`, `OAI.SKRatio.Scalar.cost`, `OAI.SKRatio.Scalar.diagonal`, `OAI.SKRatio.Scalar.gSignFactor`, `OAI.SKRatio.Scalar.signMeanG`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `SKRatio_Certificates_ScalarDataJ3K1`, `SKRatio_Certificates_ScalarDataJ3K2`, `SKRatio_Certificates_ScalarDataJ3K3`, `SKRatio_Certificates_ScalarDataJ3K4`, `SKRatio_Certificates_ScalarDataJ3K5`, `SKRatio_Certificates_ScalarDataJ3K6`, `SKRatio_Entropy_LogPartition`, `SKRatio_Gaussian_Planted`, `SKRatio_Matrices_AugmentedSquares`, `SKRatio_Matrices_PlantedGOE`, `SKRatio_Matrices_RowGeometry`, `SKRatio_Quantization_BinProjected`, `SKRatio_Variational_CompactField`, `SKRatio_Variational_FormAlgebra`, `SKRatio_Variational_ReducedForm`, `SKRatio_Variational_ScalarMonotone`, `SKRatio_Variational_ScalarReduction`.
--
--   **Imports.** It imports the published bundle `Def_SKRatio`; the bundles `OAIQ024S000` and `OAIQ024S001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ024S016`; the statements `OAI.SKRatio.Bins.random_binForm_tail`, `OAI.SKRatio.Certificate.diagonal_envelope`, `OAI.SKRatio.Planted.augmented_norm_rare` and `OAI.SKRatio.Planted.reduced_error_rare`; the proofs of `OAI.SKRatio.Bins.random_binForm_tail`, `OAI.SKRatio.Planted.augmented_norm_rare` and `OAI.SKRatio.Planted.residual_norm_rare`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S000
import Definitions.Def_OAIQ024S001

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_Planted
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def gauge (x : Spin n) (g : Disorder n) : Disorder n :=
  fun e => spinValue (x e.1.1)*g e*spinValue (x e.1.2)

def law (β : ℝ) (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal (β^2/(n:ℝ)) (Real.toNNReal (β^2/n)))

instance law_probability (β : ℝ) (n : ℕ) : IsProbabilityMeasure (law β n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

def badWeight (B : Set (Disorder n)) (g : Disorder n) : ℝ :=
  ∑ x : Spin n, if gauge x g ∈ B then weight g 0 x else 0

end SKRatio.Planted

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarReduction
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

section Probability
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

def diagonal (β : ℝ) (h : ℝ) : ℝ :=
  β^2 * ∫ t, v t^2/(w h+w t) ∂μ

def cost (β : ℝ) (t : ℝ) : ℝ :=
  ∫ h, (β^2/4)*(v h+v t)^2/(multiplier h) ∂μ

end Probability

end SKRatio.Scalar

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
  | 11 => ⟨1/500000,1/250000⟩
  | 12 => ⟨1/31250,7/200000⟩
  | 13 => ⟨141/500000,293/1000000⟩
  | 14 => ⟨1861/1000000,381/200000⟩
  | 15 => ⟨4653/500000,9449/1000000⟩
  | 16 => ⟨34943/1000000,8813/250000⟩
  | 17 => ⟨97171/1000000,19507/200000⟩
  | 18 => ⟨197039/1000000,197253/1000000⟩
  | 19 => ⟨287301/1000000,143971/500000⟩
  | 20 => ⟨37399/125000,300001/1000000⟩
  | 21 => ⟨221923/1000000,111203/500000⟩
  | 22 => ⟨5871/50000,59017/500000⟩
  | 23 => ⟨5589/125000,22659/500000⟩
  | 24 => ⟨12423/1000000,12759/1000000⟩
  | 25 => ⟨319/125000,2679/1000000⟩
  | 26 => ⟨391/1000000,427/1000000⟩
  | 27 => ⟨11/250000,53/1000000⟩
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
  | 11 => ⟨-9/1000000,-7/1000000⟩
  | 12 => ⟨-83/1000000,-79/1000000⟩
  | 13 => ⟨-13/20000,-631/1000000⟩
  | 14 => ⟨-3743/1000000,-459/125000⟩
  | 15 => ⟨-1909/125000,-15119/1000000⟩
  | 16 => ⟨-41723/1000000,-8317/200000⟩
  | 17 => ⟨-34241/500000,-68027/1000000⟩
  | 18 => ⟨-44613/1000000,-10989/250000⟩
  | 19 => ⟨12631/250000,25429/500000⟩
  | 20 => ⟨68973/500000,138777/1000000⟩
  | 21 => ⟨140351/1000000,8813/62500⟩
  | 22 => ⟨42251/500000,21221/250000⟩
  | 23 => ⟨33749/1000000,34191/1000000⟩
  | 24 => ⟨4751/500000,1951/200000⟩
  | 25 => ⟨61/31250,2047/1000000⟩
  | 26 => ⟨149/500000,13/40000⟩
  | 27 => ⟨17/500000,1/25000⟩
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

end SKRatio.Certificate.Data.J3K2

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
  | 13 => ⟨9/1000000,11/1000000⟩
  | 14 => ⟨21/250000,9/100000⟩
  | 15 => ⟨263/500000,11/20000⟩
  | 16 => ⟨2151/1000000,221/100000⟩
  | 17 => ⟨13/2500,5303/1000000⟩
  | 18 => ⟨6191/1000000,6353/1000000⟩
  | 19 => ⟨519/250000,57/25000⟩
  | 20 => ⟨159/125000,1771/1000000⟩
  | 21 => ⟨9813/1000000,1063/100000⟩
  | 22 => ⟨15223/1000000,813/50000⟩
  | 23 => ⟨10911/1000000,1463/125000⟩
  | 24 => ⟨451/100000,153/31250⟩
  | 25 => ⟨119/100000,83/62500⟩
  | 26 => ⟨211/1000000,63/250000⟩
  | 27 => ⟨13/500000,9/250000⟩
  | 28 => ⟨1/500000,1/250000⟩
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

end SKRatio.Certificate.Data.J3K3

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
  | 12 => ⟨51/250000,209/1000000⟩
  | 13 => ⟨841/1000000,853/1000000⟩
  | 14 => ⟨2211/1000000,223/100000⟩
  | 15 => ⟨763/250000,3101/1000000⟩
  | 16 => ⟨1219/1000000,127/100000⟩
  | 17 => ⟨287/200000,31/20000⟩
  | 18 => ⟨10643/1000000,2683/250000⟩
  | 19 => ⟨2801/200000,7079/500000⟩
  | 20 => ⟨701/200000,23/6250⟩
  | 21 => ⟨3467/1000000,371/100000⟩
  | 22 => ⟨7849/500000,8017/500000⟩
  | 23 => ⟨4779/250000,19453/1000000⟩
  | 24 => ⟨12109/1000000,192/15625⟩
  | 25 => ⟨4843/1000000,99/20000⟩
  | 26 => ⟨67/50000,347/250000⟩
  | 27 => ⟨269/1000000,71/250000⟩
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

end SKRatio.Certificate.Data.J3K4

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K5

def expression : Expr := integrandExpr (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 5

end SKRatio.Certificate.Data.J3K5

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K6

def expression : Expr := integrandExpr (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 6

end SKRatio.Certificate.Data.J3K6

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_LogPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def standardSample (β : ℝ) (n : ℕ) (z : Edge n → ℝ) : Disorder n :=
  fun e => sqrt (β^2/n)*z e

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_PlantedGOE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def augmented (β : ℝ) (g : (Fin n × Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => β * goe g i j + β^2/(n:ℝ)

def augmentedDisorder (β : ℝ) (g : (Fin n × Fin n) → ℝ) : Disorder n :=
  fun e => augmented β g e.1.1 e.1.2

def augmentedField (β : ℝ) (g : (Fin n × Fin n) → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, augmented β g i j

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_RowGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open Set Real
namespace SKRatio.Planted
open MatrixNet
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def otherEnd (i : Fin n) (e : Edge n) : Fin n :=
  if e.1.1=i then e.1.2 else e.1.1

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_AugmentedSquares
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def augmentedDiagonal (β : ℝ) (g : (Fin n × Fin n) → ℝ) : Fin n → ℝ :=
  fun i => augmented β g i i

def diagonalLaw (β : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  (standardArrayLaw (Fin n × Fin n)).map (augmentedDiagonal β)

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_CompactField
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus

instance instCompactSpaceElemRealFieldWeight : CompactSpace FieldWeight := inferInstanceAs (CompactSpace (Set.Icc (0:ℝ) 2))

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_FormAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def varianceKernel (p : FieldWeight × FieldWeight) : ℝ := compactV p.2
def meanVarianceKernel (p : FieldWeight × FieldWeight) : ℝ :=
  (1-(p.2:ℝ))*compactV p.2

def compactForm (J : Interaction n) (x : Fin n → FieldWeight) (p : Fin n → ℝ) : ℝ :=
  weightedForm J varianceKernel x p +
  2*weightedForm (fun i j => J i j^2) meanVarianceKernel x p +
  diagonalForm (fun i j => J i j^2) compactF x p +
  weightedForm (fun i j => J i j^2) compactK x p

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ReducedForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet Calculus Scalar
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def reducedForm (β : ℝ) (g : (Fin n × Fin n) → ℝ) (p : Fin n → ℝ) : ℝ :=
  let x := fun i => compactWeight (augmentedField β g i)
  weightedForm (augmented β g) varianceKernel x p +
    2*weightedForm (fun _ _ => β^2/(n:ℝ)) meanVarianceKernel x p +
    diagonalForm (fun _ _ => β^2/(n:ℝ)) compactF x p +
    weightedForm (fun _ _ => β^2/(n:ℝ)) compactK x p

end SKRatio.Planted

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinProjected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression Scalar
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def deterministicForm (β : ℝ) (H p : Fin n → ℝ) : ℝ :=
  rankForm H (fun i => v (H i)) p +
    2*β^2/(n:ℝ)*(∑ i, p i)*(∑ i, p i*m (H i)*v (H i)) +
    diagonalForm (fun _ _ => β^2/(n:ℝ)) compactF (fun i => compactWeight (H i)) p +
    weightedForm (fun _ _ => β^2/(n:ℝ)) compactK (fun i => compactWeight (H i)) p

end SKRatio.Planted

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarMonotone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def signMeanG (h : ℝ) : ℝ := (1-m h^2)*(7/4+m h^2)/((7/4)^2-m h^2)

def gSignFactor (h : ℝ) : ℝ := v h/((7/4)^2-m h^2)

end SKRatio.Scalar

end

end OAI
end


