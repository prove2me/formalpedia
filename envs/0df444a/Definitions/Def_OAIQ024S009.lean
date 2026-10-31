-- Prove2me | Definitions.Def_OAIQ024S009
-- name    : OAIQ024S009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:20:59.323157+00:00
-- url     : https://prove2.me/theorems/58cdd4d5-e640-44e6-a4ab-9db79b507a3b
-- title:
--   Definitions bundle OAIQ024S009 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 16 definitions and 4 theorems. The definitions and types are `OAI.SKRatio.Certificate.Data.J3K5.blocks`, `OAI.SKRatio.Certificate.Data.J3K6.blocks`, `OAI.SKRatio.Certificate.Data.J3K7.blocks`, `OAI.SKRatio.Certificate.Data.J3K7.expression`, `OAI.SKRatio.Certificate.Data.J4K0.expression`, `OAI.SKRatio.Certificate.Data.J4K1.expression`, `OAI.SKRatio.Certificate.Data.J4K12.expression`, `OAI.SKRatio.FiniteLaw.entropy`, `OAI.SKRatio.FiniteLaw.variance`, `OAI.SKRatio.MatrixNet.incidentEdges`, `OAI.SKRatio.Observation.Channel.density`, `OAI.SKRatio.Observation.Channel.mean`, `OAI.SKRatio.Observation.Channel.secondMoment`, `OAI.SKRatio.Observation.avg`, `OAI.SKRatio.Observation.tilt`, `OAI.SKRatio.Observation.tiltZ`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: [`SKRatio_Certificates_ScalarDataJ3K5`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ3K5.lean), [`SKRatio_Certificates_ScalarDataJ3K6`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ3K6.lean), [`SKRatio_Certificates_ScalarDataJ3K7`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ3K7.lean), [`SKRatio_Certificates_ScalarDataJ4K0`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K0.lean), [`SKRatio_Certificates_ScalarDataJ4K1`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K1.lean), [`SKRatio_Certificates_ScalarDataJ4K12`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K12.lean), [`SKRatio_Entropy_Entropy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Entropy/Entropy.lean), [`SKRatio_Entropy_GaussianChannel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Entropy/GaussianChannel.lean), [`SKRatio_FiniteChain_EntropicCovariance`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/FiniteChain/EntropicCovariance.lean), [`SKRatio_FiniteChain_Mean`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/FiniteChain/Mean.lean), [`SKRatio_Matrices_GaussianSquareMatrix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Matrices/GaussianSquareMatrix.lean).
--
--   **Imports.** It imports the published bundle `Def_SKRatio`; the bundles `OAIQ024S000` and `OAIQ024S001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ024S016`; the statements `OAI.SKRatio.Calculus.ratio_cutoff_of_static_inputs` and `OAI.SKRatio.Calculus.ratio_cutoff_of_uniform_gradient`; the proofs of `OAI.SKRatio.Calculus.ratio_cutoff_of_static_inputs` and `OAI.SKRatio.Calculus.ratio_cutoff_of_uniform_gradient`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S000
import Definitions.Def_OAIQ024S001

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
  | 12 => ⟨27/250000,7/62500⟩
  | 13 => ⟨513/1000000,523/1000000⟩
  | 14 => ⟨1731/1000000,873/500000⟩
  | 15 => ⟨969/250000,1949/500000⟩
  | 16 => ⟨5087/1000000,2569/500000⟩
  | 17 => ⟨2887/1000000,183/62500⟩
  | 18 => ⟨287/1000000,347/1000000⟩
  | 19 => ⟨2429/1000000,99/40000⟩
  | 20 => ⟨1061/250000,217/50000⟩
  | 21 => ⟨1471/1000000,811/500000⟩
  | 22 => ⟨173/1000000,199/500000⟩
  | 23 => ⟨423/250000,949/500000⟩
  | 24 => ⟨33/15625,1131/500000⟩
  | 25 => ⟨599/500000,127/100000⟩
  | 26 => ⟨403/1000000,109/250000⟩
  | 27 => ⟨91/1000000,51/500000⟩
  | 28 => ⟨7/500000,17/1000000⟩
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
  | 12 => ⟨37/1000000,1/25000⟩
  | 13 => ⟨81/250000,21/62500⟩
  | 14 => ⟨33/15625,2161/1000000⟩
  | 15 => ⟨9521/1000000,4817/500000⟩
  | 16 => ⟨26601/1000000,6681/250000⟩
  | 17 => ⟨1561/40000,39381/1000000⟩
  | 18 => ⟨2719/125000,10987/500000⟩
  | 19 => ⟨501/250000,469/200000⟩
  | 20 => ⟨15287/1000000,243/15625⟩
  | 21 => ⟨25297/1000000,25671/1000000⟩
  | 22 => ⟨14701/1000000,14957/1000000⟩
  | 23 => ⟨1011/250000,67/15625⟩
  | 24 => ⟨537/1000000,129/200000⟩
  | 25 => ⟨9/500000,49/1000000⟩
  | 26 => ⟨-3/1000000,1/250000⟩
  | 27 => ⟨-1/1000000,1/500000⟩
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

end SKRatio.Certificate.Data.J3K6

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K7

def expression : Expr := integrandExpr (19/40) (406349/500000) (66273/125000) (28579/250000) (135787/200000) 7
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
  | 10 => ⟨1/20000,27/500000⟩
  | 11 => ⟨209/500000,433/1000000⟩
  | 12 => ⟨2691/1000000,2761/1000000⟩
  | 13 => ⟨541/40000,13767/1000000⟩
  | 14 => ⟨52109/1000000,52697/1000000⟩
  | 15 => ⟨147861/1000000,18581/125000⟩
  | 16 => ⟨8941/31250,287393/1000000⟩
  | 17 => ⟨16551/50000,1667/5000⟩
  | 18 => ⟨21621/125000,21779/125000⟩
  | 19 => ⟨3217/200000,1821/100000⟩
  | 20 => ⟨10581/125000,85953/1000000⟩
  | 21 => ⟨20437/100000,206681/1000000⟩
  | 22 => ⟨96671/500000,9757/50000⟩
  | 23 => ⟨110183/1000000,111621/1000000⟩
  | 24 => ⟨44983/1000000,11531/250000⟩
  | 25 => ⟨7191/500000,3739/250000⟩
  | 26 => ⟨3721/1000000,1967/500000⟩
  | 27 => ⟨39/50000,21/25000⟩
  | 28 => ⟨13/100000,9/62500⟩
  | 29 => ⟨17/1000000,1/50000⟩
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

end SKRatio.Certificate.Data.J3K7

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K0

def expression : Expr := integrandExpr (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 0

end SKRatio.Certificate.Data.J4K0

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K1

def expression : Expr := integrandExpr (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 1

end SKRatio.Certificate.Data.J4K1

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K12

def expression : Expr := integrandExpr (1/2) (397973/500000) (524071/1000000) (119553/1000000) (702377/1000000) 12

end SKRatio.Certificate.Data.J4K12

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_Mean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio
namespace FiniteLaw
variable {α : Type*} [Fintype α]

def variance (p : α → ℝ) (f : α → ℝ) : ℝ :=
  ∑ x, p x * (f x - mean p f) ^ 2

end FiniteLaw
end SKRatio
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter ContinuousLinearMap
namespace SKRatio.FiniteLaw
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

def entropy (q f : α → ℝ) : ℝ :=
  mean q (fun x => f x * Real.log (f x)) - mean q f * Real.log (mean q f)

end SKRatio.FiniteLaw

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_EntropicCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter Real
namespace SKRatio.Observation
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α]

def avg (p : Prior α) (f : α → ℝ) : ℝ := FiniteLaw.mean p f

lemma avg_pos (p : Prior α) {f : α → ℝ} (hf : ∀ x, 0 < f x) : 0 < avg p f := by
  have h : 0 < ∑ x, p x := by rw [p.sum_one];norm_num
  obtain ⟨x,hx,hpx⟩ := (Finset.sum_pos_iff_of_nonneg (fun x _ => p.nonneg x)).mp h
  exact Finset.sum_pos' (fun y _ => mul_nonneg (p.nonneg y) (hf y).le)
    ⟨x,hx,mul_pos hpx (hf x)⟩

def tiltZ (p : Prior α) (v : α → ℝ) (s : ℝ) : ℝ := avg p (fun x => exp (s*v x))

lemma tiltZ_pos (p : Prior α) (v : α → ℝ) (s : ℝ) : 0 < tiltZ p v s :=
  avg_pos p (fun _ => exp_pos _)

def tilt (p : Prior α) (v : α → ℝ) (s : ℝ) : Prior α where
  mass x := p x*exp (s*v x)/tiltZ p v s
  nonneg x := div_nonneg (mul_nonneg (p.nonneg x) (exp_nonneg _)) (tiltZ_pos p v s).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (tiltZ_pos p v s).ne'

@[simp] lemma tilt_apply (p : Prior α) (v : α → ℝ) (s : ℝ) (x : α) :
    tilt p v s x = p x*exp (s*v x)/tiltZ p v s := rfl

end SKRatio.Observation

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_GaussianChannel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
namespace SKRatio.Observation.Channel
variable {α : Type*} [Fintype α] {d : ℕ}

variable (v : α → Fin d → ℝ)

def mean (p : Prior α) (i : Fin d) : ℝ := avg p (fun x => v x i)

def secondMoment (p : Prior α) : ℝ := avg p (normSq v)

def density (p : Prior α) (t : ℝ) (z : Fin d → ℝ) : ℝ :=
  ∑ x, p x*likelihood v t x z

lemma density_jensen (p : Prior α) (t : ℝ) (z : Fin d → ℝ) :
    exp (sqrt t*(∑ i, mean v p i*z i)-t*secondMoment v p/2) ≤ density v p t z := by
  have he : (∑ x, p x*(sqrt t*(∑ i, v x i*z i)-t*normSq v x/2)) =
      sqrt t*(∑ i, mean v p i*z i)-t*secondMoment v p/2 := by
    simp only [mul_sub,Finset.sum_sub_distrib,mean,secondMoment,avg,FiniteLaw.mean]
    congr 1
    · simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun x _ => by ring))
    · simp only [Finset.mul_sum,Finset.sum_div]
      exact Finset.sum_congr rfl (fun x _ => by ring)
  have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := p.mass)
    (p := fun x => sqrt t*(∑ i, v x i*z i)-t*normSq v x/2)
    (fun x _ => p.nonneg x) p.sum_one (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul,he,density,likelihood] using hj

end SKRatio.Observation.Channel

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianSquareMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.MatrixNet
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

def incidentEdges {n : ℕ} (i : Fin n) : Finset (Edge n) :=
  Finset.univ.filter (fun e => e.1.1 = i ∨ e.1.2 = i)

end SKRatio.MatrixNet

end
end

end OAI
end


