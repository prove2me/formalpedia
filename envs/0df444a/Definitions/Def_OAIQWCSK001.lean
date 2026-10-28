-- Prove2me | Definitions.Def_OAIQWCSK001
-- name    : OAIQWCSK001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T02:30:11.885232+00:00
-- url     : https://prove2.me/theorems/20d39741-319f-42d5-a301-4582538e6411
-- title:
--   Definitions bundle OAIQWCSK001 of the split of OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalSK.covariance_and_linear_tests` and `OAI.CriticalSK.critical_mixing_lower_bounds`, carved from OpenAI's openai/math development (OpenAI, *Critical slowing down in the Sherrington–Kirkpatrick model*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to this platform's Lean and Mathlib. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 27 definitions, 4 instances and 6 theorems. The definitions and types are `OAI.CriticalSK.Incident`, `OAI.CriticalSK.Nonincident`, `OAI.CriticalSK.alphaSite`, `OAI.CriticalSK.cavityClippedCount`, `OAI.CriticalSK.cavityNormalization`, `OAI.CriticalSK.cavityOverlap`, `OAI.CriticalSK.cavityOverlapCoord`, `OAI.CriticalSK.cavitySplit`, `OAI.CriticalSK.coshMixture`, `OAI.CriticalSK.deleteDisorder`, `OAI.CriticalSK.edgeOfOther`, `OAI.CriticalSK.flipSite`, `OAI.CriticalSK.flipSiteEquiv`, `OAI.CriticalSK.gaussianLinear`, `OAI.CriticalSK.gaussianScalarPi`, `OAI.CriticalSK.gibbsOverlap`, `OAI.CriticalSK.incidentCoeff`, `OAI.CriticalSK.incidentLaw`, `OAI.CriticalSK.incidentOtherEquiv`, `OAI.CriticalSK.localField`, `OAI.CriticalSK.naturalOverlapConstant`, `OAI.CriticalSK.nonincidentLaw`, `OAI.CriticalSK.otherEnd`, `OAI.CriticalSK.restrictCoeff`, `OAI.CriticalSK.rotatedCubeOverlap`, `OAI.CriticalSK.rotatedCubePair`, `OAI.CriticalSK.touches`.
--
--   **Sources.** They come from these modules of lean/OAI/MathematicalPhysics/CriticalSK, in whole or in part: [`Cavity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/Cavity.lean), [`CubeRestriction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/CubeRestriction.lean), [`GaussianMoments`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/GaussianMoments.lean), [`OrientationLimits`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/OrientationLimits.lean), [`Rayleigh`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/Rayleigh.lean), [`SpinModel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/SpinModel.lean).
--
--   **Imports.** It imports the published bundle `Def_CriticalSK`; the bundle `OAIQWCSK000` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.CriticalSK.cavity_overlap_tail_zero` and `OAI.CriticalSK.orientation_normalized_overlap_bound`; the proofs of `OAI.CriticalSK.cavity_overlap_tail_zero`, `OAI.CriticalSK.covariance_and_linear_tests`, `OAI.CriticalSK.covariance_upper_tight` and `OAI.CriticalSK.orientation_normalized_overlap_bound`.
-- source:
--   OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics/CriticalSK at commit adc7f12

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_OAIQWCSK000

section
-- module Solutions.OAIQW_CriticalSK.SpinModel
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise
open Set Metric MeasureTheory MeasureTheory.Measure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open scoped BigOperators InnerProductSpace
open Module
open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open scoped BigOperators
open Matrix Polynomial
open scoped BigOperators Topology
open Filter
namespace CriticalSK

section

open Set MeasureTheory

def gibbsOverlap {n : ℕ} (W : Disorder n) : ℝ :=
  ∑ x : Spin n, ∑ y : Spin n, gibbs W x*gibbs W y*(cubeOverlap x y)^2

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.Cavity
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

section

open Set Filter MeasureTheory

variable {n : ℕ}

def flipSite (i : Fin n) (x : Spin n) : Spin n := Function.update x i (!(x i))

@[simp] lemma flipSite_apply_self (i : Fin n) (x : Spin n) : flipSite i x i = !(x i) := by simp [flipSite]

@[simp] lemma flipSite_apply_ne (i : Fin n) (x : Spin n) {j : Fin n} (h : j ≠ i) : flipSite i x j = x j := by simp [flipSite,h]

@[simp] lemma flipSite_involutive (i : Fin n) (x : Spin n) : flipSite i (flipSite i x) = x := by
  funext j
  by_cases hj : j=i
  · subst j; simp
  · simp [hj]

def flipSiteEquiv (i : Fin n) : Spin n ≃ Spin n where
  toFun := flipSite i
  invFun := flipSite i
  left_inv := flipSite_involutive i
  right_inv := flipSite_involutive i

def incidentCoeff (i : Fin n) (x : Spin n) (e : Edge n) : ℝ :=
  if e.val.1=i then spinValue (x e.val.2) else if e.val.2=i then spinValue (x e.val.1) else 0

def localField (W : Disorder n) (i : Fin n) (x : Spin n) : ℝ :=
  ∑ e : Edge n, W e*incidentCoeff i x e

def deleteDisorder (W : Disorder n) (i : Fin n) : Disorder n :=
  fun e => if e.val.1=i ∨ e.val.2=i then 0 else W e

def cavityNormalization (W : Disorder n) (i : Fin n) : ℝ :=
  mean (deleteDisorder W i) (fun x => Real.cosh (localField W i x))

def alphaSite (W : Disorder n) (i : Fin n) : ℝ := mean W (fun x => (Real.cosh (localField W i x))⁻¹^2)

end

section

open Set Filter MeasureTheory

variable {n : ℕ} (W : Disorder n)

def cavityOverlapCoord (i : Fin n) (x y : Spin n) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, spinValue (x j)*spinValue (y j))/(n:ℝ)

def cavityOverlap (i : Fin n) : ℝ :=
  mean (deleteDisorder W i) (fun x => mean (deleteDisorder W i) (fun y => cavityOverlapCoord i x y^2))

end

open Set Filter MeasureTheory ProbabilityTheory

variable {n : ℕ}

def touches (i : Fin n) (e : Edge n) : Prop := e.val.1=i ∨ e.val.2=i

instance instDecidablePredEdgeTouches (i : Fin n) : DecidablePred (touches i) := fun _ => Classical.propDecidable _

abbrev Incident (i : Fin n) := {e : Edge n // touches i e}

abbrev Nonincident (i : Fin n) := {e : Edge n // ¬touches i e}

def edgeOfOther (i j : Fin n) (h : j ≠ i) : Edge n :=
  if hij : i < j then ⟨(i,j),hij⟩ else ⟨(j,i),lt_of_le_of_ne (le_of_not_gt hij) h⟩

lemma edgeOfOther_touches (i j : Fin n) (h : j ≠ i) : touches i (edgeOfOther i j h) := by
  unfold edgeOfOther touches
  split_ifs <;> simp

def otherEnd (i : Fin n) (e : Incident i) : Fin n :=
  if e.val.val.1=i then e.val.val.2 else e.val.val.1

lemma otherEnd_ne (i : Fin n) (e : Incident i) : otherEnd i e ≠ i := by
  unfold otherEnd
  have hlt := e.val.property
  split_ifs <;> grind

def incidentOtherEquiv (i : Fin n) : Incident i ≃ {j : Fin n // j ≠ i} where
  toFun e := ⟨otherEnd i e,otherEnd_ne i e⟩
  invFun j := ⟨edgeOfOther i j.val j.property,edgeOfOther_touches i j.val j.property⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    have he := e.property
    have hlt := e.val.property
    dsimp only [touches] at he
    dsimp only [otherEnd,edgeOfOther]
    split_ifs <;> ext <;> grind
  right_inv j := by
    apply Subtype.ext
    dsimp only [otherEnd,edgeOfOther]
    split_ifs <;> grind

def cavitySplit (i : Fin n) : Disorder n ≃ᵐ ((Incident i → ℝ) × (Nonincident i → ℝ)) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Edge n => ℝ) (touches i)

def incidentLaw (i : Fin n) : Measure (Incident i → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 (n:ℝ≥0)⁻¹

def nonincidentLaw (i : Fin n) : Measure (Nonincident i → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 (n:ℝ≥0)⁻¹

instance instIsProbabilityMeasureForallIncidentRealIncidentLaw (i : Fin n) : IsProbabilityMeasure (incidentLaw i) := by unfold incidentLaw; infer_instance

instance instIsProbabilityMeasureForallNonincidentRealNonincidentLaw (i : Fin n) : IsProbabilityMeasure (nonincidentLaw i) := by unfold nonincidentLaw; infer_instance

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.GaussianMoments
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

section

open Set Filter MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

def gaussianScalarPi (v : ℝ≥0) : Measure (ι → ℝ) := Measure.pi fun _ => gaussianReal 0 v

instance instIsProbabilityMeasureForallRealGaussianScalarPi (v : ℝ≥0) : IsProbabilityMeasure (gaussianScalarPi (ι := ι) v) := by unfold gaussianScalarPi; infer_instance

def gaussianLinear (a : ι → ℝ) (z : ι → ℝ) : ℝ := ∑ i, a i*z i

end

open Set Filter MeasureTheory ProbabilityTheory

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def coshMixture (p : κ → ℝ) (a : κ → ι → ℝ) (z : ι → ℝ) : ℝ :=
  ∑ x, p x*Real.cosh (gaussianLinear (a x) z)

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.CubeRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter

open scoped Topology

open MeasureTheory Filter Set Real

open scoped ENNReal NNReal BigOperators

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set
namespace CriticalSK

section

def rotatedCubePair {n : ℕ} (lam : Fin n → ℝ) (g : ℝ → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : ℝ :=
  (Fintype.card (Spin n) : ℝ)⁻¹^2 * ∑ x : Spin n, ∑ y : Spin n,
    g (cubeOverlap x y)*Real.exp ((diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+
      diagonalEnergy lam (orthogonalIsometry U (cubeVector y)))/2)

end

def rotatedCubeOverlap {n : ℕ} (lam : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : ℝ :=
  rotatedCubePair lam (fun q => q^2) U/rotatedCubePartition lam 1 U^2

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.OrientationLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

open Finset Real

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real Filter

open scoped Topology

namespace CriticalSK


open Set MeasureTheory Filter

def naturalOverlapConstant (L : ℝ) : ℝ :=
  32*(16*Real.exp (6*(L*Real.sqrt L)))^2/Real.sqrt L

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.Rayleigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

section

open Set Filter MeasureTheory ProbabilityTheory

variable {n : ℕ}

@[simp] lemma abs_spinValue (b : Bool) : |spinValue b| = 1 := by cases b <;> norm_num [spinValue]

noncomputable def cavityClippedCount (W : Disorder n) (r : ℝ) : ℝ :=
  ∑ i : Fin n, if Real.exp 1+1 < cavityNormalization W i ∧ cavityOverlap W i ≤ r then 1 else 0

end

section

open Set Filter MeasureTheory

variable {n : ℕ} (W : Disorder n)

def restrictCoeff (A : Finset (Fin n)) (a : Fin n → ℝ) : Fin n → ℝ := fun i => if i ∈ A then a i else 0

end

open Set Filter MeasureTheory

end CriticalSK

end

end OAI
end


