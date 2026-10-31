-- Prove2me | Definitions.Def_OAIQ024S002
-- name    : OAIQ024S002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:20:00.164016+00:00
-- url     : https://prove2.me/theorems/be5be90b-86b4-4275-ad36-f63c151f336a
-- title:
--   Definitions bundle OAIQ024S002 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 15 definitions and 3 theorems. The definitions and types are `OAI.SKRatio.Certificate.Data.J0K3.blocks`, `OAI.SKRatio.Certificate.Data.J0K4.blocks`, `OAI.SKRatio.Certificate.Data.J0K5.blocks`, `OAI.SKRatio.Certificate.Data.J0K6.blocks`, `OAI.SKRatio.Certificate.Data.J2K0.expression`, `OAI.SKRatio.Certificate.coefficientBox`, `OAI.SKRatio.Certificate.crossBox`, `OAI.SKRatio.Certificate.interpolationCheck`, `OAI.SKRatio.Certificate.lBox`, `OAI.SKRatio.Certificate.slackBox₀`, `OAI.SKRatio.Certificate.slackBox₁`, `OAI.SKRatio.Fields.conditionalExpectation`, `OAI.SKRatio.Fields.dirichlet`, `OAI.SKRatio.Fields.expectation`, `OAI.SKRatio.Fields.pairUpdate`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: [`SKRatio_Calculus_Expectation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Calculus/Expectation.lean), [`SKRatio_Calculus_PairUpdate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Calculus/PairUpdate.lean), [`SKRatio_Certificates_CertifiedInterpolation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/CertifiedInterpolation.lean), [`SKRatio_Certificates_ScalarDataJ0K3`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ0K3.lean), [`SKRatio_Certificates_ScalarDataJ0K4`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ0K4.lean), [`SKRatio_Certificates_ScalarDataJ0K5`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ0K5.lean), [`SKRatio_Certificates_ScalarDataJ0K6`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ0K6.lean), [`SKRatio_Certificates_ScalarDataJ2K0`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ2K0.lean).
--
--   **Imports.** It imports the published bundle `Def_SKRatio`; the bundles `OAIQ024S000` and `OAIQ024S001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ024S016`; the proof of `OAI.SKRatio.Planted.augmented_norm_rare`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S000
import Definitions.Def_OAIQ024S001

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_Expectation
attribute [-simp] _root_.OAI.SKRatio.Calculus.abs_signConjugate _root_.OAI.SKRatio.Calculus.abs_spin _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.halfDiff_const _root_.OAI.SKRatio.Calculus.halfDiff_replace _root_.OAI.SKRatio.Calculus.halfDiff_self _root_.OAI.SKRatio.Calculus.halfDiff_spin _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.plus_signProduct _root_.OAI.SKRatio.Calculus.replace_replace _root_.OAI.SKRatio.Calculus.replace_same _root_.OAI.SKRatio.Calculus.replace_self _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.semigroup_zero _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.signProduct_plus _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.spin_sq _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Independent.coupling_zero _root_.OAI.SKRatio.Independent.mass_zero _root_.OAI.SKRatio.Independent.siteKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix TwoSpin
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def expectation {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  ∑ x, mass g h x * f x

def conditionalExpectation {n : ℕ} (g : Disorder n) (h : Fin n → ℝ)
    (i : Fin n) (f : Spin n → ℝ) (x : Spin n) : ℝ :=
  (weight g h x * f x + weight g h (flip i x) * f (flip i x)) /
    (weight g h x + weight g h (flip i x))

def dirichlet {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  ∑ i, expectation g h (fun x => (f x - conditionalExpectation g h i f x) ^ 2)

@[simp] theorem expectation_const (g : Disorder n) (h : Fin n → ℝ) (c : ℝ) :
    expectation g h (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul]

end SKRatio.Fields
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_PairUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix TwoSpin
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def pairUpdate (i j : Fin n) (x : Spin n) (a b : Bool) : Spin n :=
  Function.update (Function.update x i a) j b

lemma conditionalExpectation_add (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f k : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i (f+k) x=conditionalExpectation g h i f x+conditionalExpectation g h i k x := by
  unfold conditionalExpectation
  simp only [Pi.add_apply]
  ring
lemma conditionalExpectation_smul (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (c : ℝ) (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i (c • f) x=c*conditionalExpectation g h i f x := by
  unfold conditionalExpectation
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

end SKRatio.Fields
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open Real MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate
open Scalar

def lBox (A : Box) : Box := Box.sub (Box.rat (64/100)) (Box.mul (Box.rat (19/100)) A)

def coefficientBox (X Y : Enclosures) : Box :=
  Box.sub (Box.sub (Box.divPos (Box.sq Y.av) (lBox Y.av)) Y.av)
    (Box.mul (Box.rat (3/2)) (Box.sq X.gv))

def slackBox₀ (j z : ℚ) (X Y : Enclosures) : Box :=
  Box.sub (Box.add (Box.add (lBox X.av) (Box.rat (18/1000)))
    (Box.mul (Box.rat (j^2)) (coefficientBox X Y))) (Box.mul (Box.rat (z^2)) Y.rv)

def slackBox₁ (j z : ℚ) (X Y : Enclosures) : Box :=
  Box.sub (Box.add (Box.sub (Box.rat (4644/10000)) (Box.mul (Box.rat (z/2)) Y.vs))
    (Box.mul (Box.rat (j^2)) X.mv))
    (Box.mul (Box.rat (z^2)) (Box.add (Box.mul (Box.rat (3/2)) (Box.sq Y.gs)) Y.rv))

def crossBox (j z t : ℚ) (X Y : Enclosures) : Box :=
  let aTerm := Box.mul (Box.sub X.av Y.av) (Box.rat z)
  let mTerm := Box.mul (Box.rat (2*(z^2-j^2))) Y.ms
  let vTerm := Box.mul (Box.sub (Box.divPos (Box.mul (Box.rat (z^2)) X.av) (lBox X.av))
    (Box.divPos (Box.mul (Box.rat (j^2)) Y.av) (lBox Y.av))) Y.vs
  let gTerm := Box.mul (Box.mul (Box.rat 3)
    (Box.sub (Box.mul (Box.rat (z^2)) X.gv) (Box.mul (Box.rat (j^2)) Y.gv))) Y.gs
  Box.mul ⟨0,t⟩ (Box.add (Box.add (Box.add (Box.add Y.fs aTerm) mTerm) vTerm) gTerm)

def interpolationCheck (j z t : ℚ) (X Y : Enclosures) : Bool := decide (
  0 < (lBox X.av).lo ∧ 0 < (lBox Y.av).lo ∧
  (lBox Y.av).hi ≤ 2*Y.av.lo ∧ 0 ≤ (coefficientBox X Y).lo ∧
  511/1000 ≤ (slackBox₀ j z X Y).lo ∧ 425/1000 ≤ (slackBox₁ j z X Y).lo ∧
  (crossBox j z t X Y).hi ≤ 925/1000)

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K3

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
  | 12 => ⟨1/500000,3/1000000⟩
  | 13 => ⟨11/500000,1/40000⟩
  | 14 => ⟨77/500000,81/500000⟩
  | 15 => ⟨371/500000,763/1000000⟩
  | 16 => ⟨1217/500000,2473/1000000⟩
  | 17 => ⟨5177/1000000,2617/500000⟩
  | 18 => ⟨3247/500000,1317/200000⟩
  | 19 => ⟨961/250000,1961/500000⟩
  | 20 => ⟨399/1000000,569/1000000⟩
  | 21 => ⟨321/200000,1847/1000000⟩
  | 22 => ⟨647/125000,1101/200000⟩
  | 23 => ⟨71/12500,3003/500000⟩
  | 24 => ⟨1687/500000,3567/1000000⟩
  | 25 => ⟨39/31250,83/62500⟩
  | 26 => ⟨307/1000000,333/1000000⟩
  | 27 => ⟨13/250000,59/1000000⟩
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

end SKRatio.Certificate.Data.J0K3

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K4

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
  | 10 => ⟨3/1000000,1/200000⟩
  | 11 => ⟨29/1000000,31/1000000⟩
  | 12 => ⟨1/6250,33/200000⟩
  | 13 => ⟨151/250000,613/1000000⟩
  | 14 => ⟨293/200000,739/500000⟩
  | 15 => ⟨1977/1000000,401/200000⟩
  | 16 => ⟨197/200000,101/100000⟩
  | 17 => ⟨257/1000000,3/10000⟩
  | 18 => ⟨3073/1000000,3101/1000000⟩
  | 19 => ⟨5351/1000000,1351/250000⟩
  | 20 => ⟨7/3125,571/250000⟩
  | 21 => ⟨551/1000000,319/500000⟩
  | 22 => ⟨4907/1000000,2497/500000⟩
  | 23 => ⟨2067/250000,8393/1000000⟩
  | 24 => ⟨1317/200000,833/125000⟩
  | 25 => ⟨79/25000,3209/1000000⟩
  | 26 => ⟨1011/1000000,1037/1000000⟩
  | 27 => ⟨57/250000,119/500000⟩
  | 28 => ⟨37/1000000,1/25000⟩
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

end SKRatio.Certificate.Data.J0K4

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K5

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
  | 11 => ⟨7/500000,1/62500⟩
  | 12 => ⟨91/1000000,19/200000⟩
  | 13 => ⟨103/250000,419/1000000⟩
  | 14 => ⟨33/25000,333/250000⟩
  | 15 => ⟨2877/1000000,723/250000⟩
  | 16 => ⟨491/125000,99/25000⟩
  | 17 => ⟨703/250000,2837/1000000⟩
  | 18 => ⟨113/200000,593/1000000⟩
  | 19 => ⟨3/6250,251/500000⟩
  | 20 => ⟨101/50000,41/20000⟩
  | 21 => ⟨1867/1000000,19/10000⟩
  | 22 => ⟨59/125000,261/500000⟩
  | 23 => ⟨27/1000000,73/1000000⟩
  | 24 => ⟨27/100000,19/62500⟩
  | 25 => ⟨19/62500,163/500000⟩
  | 26 => ⟨77/500000,41/250000⟩
  | 27 => ⟨23/500000,1/20000⟩
  | 28 => ⟨9/1000000,11/1000000⟩
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

end SKRatio.Certificate.Data.J0K5

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K6

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
  | 11 => ⟨1/200000,7/1000000⟩
  | 12 => ⟨3/50000,1/15625⟩
  | 13 => ⟨227/500000,467/1000000⟩
  | 14 => ⟨609/250000,1239/500000⟩
  | 15 => ⟨4463/500000,2249/250000⟩
  | 16 => ⟨5229/250000,20997/1000000⟩
  | 17 => ⟨14113/500000,28427/1000000⟩
  | 18 => ⟨3503/200000,17633/1000000⟩
  | 19 => ⟨2147/1000000,583/250000⟩
  | 20 => ⟨3491/500000,111/15625⟩
  | 21 => ⟨629/31250,10167/500000⟩
  | 22 => ⟨19501/1000000,19649/1000000⟩
  | 23 => ⟨9837/1000000,9943/1000000⟩
  | 24 => ⟨2963/1000000,381/125000⟩
  | 25 => ⟨567/1000000,601/1000000⟩
  | 26 => ⟨69/1000000,79/1000000⟩
  | 27 => ⟨1/200000,7/1000000⟩
  | 28 => ⟨0,1/1000000⟩
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

end SKRatio.Certificate.Data.J0K6

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

def expression : Expr := integrandExpr (89/200) (52021/62500) (13423/25000) (21477/200000) (81561/125000) 0

end SKRatio.Certificate.Data.J2K0

end

end OAI
end


