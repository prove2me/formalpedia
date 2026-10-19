-- Prove2me | Definitions.Def_OAIQWCSK000
-- name    : OAIQWCSK000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T21:35:58.740349+00:00
-- url     : https://prove2.me/theorems/f2ecec65-25e2-474e-a616-e28550a62185
-- title:
--   OpenAI critical SK slow-mixing split: definitions bundle
-- statement:
--   This is the definitions bundle for the split of OpenAI's proof of `OAI.CriticalSK.realized_equilibrium_initial_states`. That theorem is about zero-field Gaussian Sherrington–Kirkpatrick heat-bath dynamics at the critical inverse temperature $\beta = 1$. Fix initial states drawn from the Gibbs measure. For times $o(n^{2/3})$, or for $o(n^{5/3})$ single-site update attempts, the Gibbs mass of the initial states that are still farther than $1/4$ from equilibrium tends to one in probability over the disorder.
--
--   The bundle holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/MathematicalPhysics/CriticalSK` (OpenAI, *Critical slowing down in the Sherrington–Kirkpatrick model*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are:
--   - the Gaussian orthogonal ensemble and its tridiagonal model;
--   - the spectral rigidity event `spectralGood`;
--   - Haar measure on the orthogonal group;
--   - spherical and rotated-cube partition functions with their saddle-point quantities;
--   - the Gibbs small-ball mass `linearSmallBall` and the obstruction event `smallBallObstruction`;
--   - the explicit constants of the proof.
--
--   The bundle also holds the lemmas that these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them.
--
--   The definitions of the published statement are not repeated. These are the disorder, the Gibbs measure, the heat-bath dynamics and the good-mass functions. The bundle imports them from the published bundle `Def_CriticalSK`. It imports no other bundle.
--
--   Modules: `BlockEnergy`, `CubeOverlap`, `CubeRestriction`, `DisorderTransfer`, `EdgeAsymptotics`, `GaussianConcentration`, `GaussianMatrices`, `GaussianMoments`, `Gibbs`, `GOESpectrum`, `HeatBath`, `MinMax`, `OrientationBounds`, `OrientationLimits`, `OverlapMoments`, `PartitionBounds`, `PathEnergy`, `PathSpectra`, `Powers`, `Resolvent`, `SaddleLimit`, `SmallBall`, `SphereGeometry`, `SphereSaddle`, `SpinModel`, `TriNoise`.
-- source:
--   OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics/CriticalSK at commit adc7f12

import Mathlib
import Definitions.Def_CriticalSK

section
-- module Solutions.OAIQW_CriticalSK.Compat
namespace OAI.CriticalSK
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434


end OAI.CriticalSK
end

section
-- module Solutions.OAIQW_CriticalSK.GaussianMoments
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

def chiSquare (m : ℕ) (x : Fin m → ℝ) : ℝ := ∑ i, x i ^ 2

def standardGaussianProduct (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

open Set Filter MeasureTheory ProbabilityTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.GaussianConcentration
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

section

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

def chi (m : ℕ) (x : Fin m → ℝ) : ℝ := Real.sqrt (chiSquare m x)

def chiRowDim (n i : ℕ) : ℕ := max 1 (n - i)

abbrev ChiRows (n : ℕ) := (i : ℕ) → (Fin (chiRowDim n i) → ℝ)

def chiRowLaw (n : ℕ) : Measure (ChiRows n) :=
  Measure.infinitePi (fun i => standardGaussianProduct (chiRowDim n i))

instance instIsProbabilityMeasureChiRowsChiRowLaw (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

def centeredChiRow (n i : ℕ) (ω : ChiRows n) : ℝ :=
  chi (chiRowDim n i) (ω i) - ∫ y, chi (chiRowDim n i) y ∂standardGaussianProduct (chiRowDim n i)

def scaledChiRow (n i : ℕ) (ω : ChiRows n) : ℝ :=
  (Real.sqrt (n + 1))⁻¹ * centeredChiRow n i ω

def diagonalMarginal (n _i : ℕ) : Measure ℝ :=
  gaussianReal 0 ⟨2 / (n + 1), by positivity⟩

instance instIsProbabilityMeasureRealDiagonalMarginal (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

def diagonalLaw (n : ℕ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (diagonalMarginal n)

instance instIsProbabilityMeasureForallNatRealDiagonalLaw (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def blockThreshold (c : ℝ≥0) (m j r : ℕ) (h : ℝ) : ℝ :=
  Real.sqrt (2 * (m + 1) * (c : ℝ) * (h ^ 2 + (j + r : ℕ) * Real.log 16))

def blockShell (j : ℕ) : ℕ → Finset ℕ
  | 0 => Finset.range (2 * 8 ^ j)
  | r + 1 => Finset.Ico (2 ^ (r + 1) * 8 ^ j) (2 ^ (r + 2) * 8 ^ j)

def multiscaleBad (X : ℕ → Ω → ℝ) (c : ℝ≥0) (d : ℕ → ℕ)
    (J N : ℕ) (h : ℝ) : Set Ω :=
  ⋃ j ∈ Finset.range J, ⋃ r ∈ Finset.range (N + 1), ⋃ b ∈ blockShell j r,
    {ω | ∃ k ≤ d j, blockThreshold c (d j) j r h ≤
      |∑ i ∈ Finset.range (k + 1), X (b * (d j + 1) + i) ω|}

end

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_1 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_1 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_1 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_1 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_2 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_2 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_2 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_2 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_3 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_3 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_3 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_3 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_4 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_4 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_4 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_4 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_5 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_5 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_5 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_5 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_6 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_6 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_6 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_6 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_7 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_7 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_7 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_7 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_8 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_8 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_8 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_8 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_9 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_9 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_9 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_9 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_10 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_10 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_10 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_10 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_11 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_11 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_11 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_11 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_12 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_12 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_12 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_12 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_13 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_13 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_13 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_13 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_14 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_14 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_14 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_14 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_15 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_15 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_15 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_15 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_16 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_16 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_16 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_16 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_17 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_17 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_17 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_17 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_18 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_18 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_18 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_18 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_19 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_19 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_19 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_19 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_20 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_20 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_20 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_20 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_21 (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance instIsProbabilityMeasureChiRowsChiRowLaw_21 (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance instIsProbabilityMeasureRealDiagonalMarginal_21 (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance instIsProbabilityMeasureForallNatRealDiagonalLaw_21 (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.PathEnergy
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

namespace CriticalSK

def edgeCoeff (n i : ℕ) : ℝ := Real.sqrt (1 - (i + 1 : ℝ) / (n + 1))

def pathEnergy (n : ℕ) (u : ℕ → ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range (n + 1), u i ^ 2 -
    2 * ∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i + 1)

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.BlockEnergy
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

namespace CriticalSK

def blockIndices (d l : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (B ×ˢ Finset.range l).image (fun p => p.1 * d + p.2)

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.SpinModel
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

variable {n : ℕ} (W : Disorder n)

@[simp] lemma spinValue_sq (b : Bool) : spinValue b ^ 2 = 1 := by
  cases b <;> norm_num [spinValue]

end

section

def cubeVector {n : ℕ} (x : Spin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => spinValue (x i))

def cubeOverlap {n : ℕ} (x y : Spin n) : ℝ := inner ℝ (cubeVector x) (cubeVector y) / n

instance instDecidableSameExcept_1 {n : ℕ} (i : Fin n) (x y : Spin n) : Decidable (sameExcept i x y) :=
  Classical.propDecidable _

instance instDecidableSameExcept_2 {n : ℕ} (i : Fin n) (x y : Spin n) : Decidable (sameExcept i x y) :=
  Classical.propDecidable _

open Set MeasureTheory

end

instance instDecidableSameExcept_3 {n : ℕ} (i : Fin n) (x y : Spin n) : Decidable (sameExcept i x y) :=
  Classical.propDecidable _

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.SphereGeometry
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
namespace CriticalSK


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orthogonal_entry_bound (U : Matrix.orthogonalGroup ι ℝ) (i j : ι) :
    |(U : Matrix ι ι ℝ) i j| ≤ 1 := by
  have h : (∑ k : ι, ((U : Matrix ι ι ℝ) k j)^2) = 1 := by
    have he := congrArg (fun A : Matrix ι ι ℝ => A j j) (Unitary.star_mul_self_of_mem U.property)
    simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply_eq,
      ← sq] using he
  have hl : ((U : Matrix ι ι ℝ) i j)^2 ≤ 1 := by
    rw [← h]
    exact Finset.single_le_sum (f := fun k => ((U : Matrix ι ι ℝ) k j)^2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [sq_abs ((U : Matrix ι ι ℝ) i j), abs_nonneg ((U : Matrix ι ι ℝ) i j)]

instance orthogonalGroup_compactSpace : CompactSpace (Matrix.orthogonalGroup ι ℝ) := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_unitary (R := Matrix ι ι ℝ))
  apply Metric.isBounded_iff_subset_closedBall (0 : Matrix ι ι ℝ) |>.mpr
  refine ⟨1, ?_⟩
  intro A hA
  rw [mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro j
  exact orthogonal_entry_bound ⟨A,hA⟩ i j

instance orthogonalGroup_measurableSpace : MeasurableSpace (Matrix.orthogonalGroup ι ℝ) :=
  borel _

instance orthogonalGroup_borelSpace : BorelSpace (Matrix.orthogonalGroup ι ℝ) := ⟨rfl⟩

def orthogonalHaar (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Measure (Matrix.orthogonalGroup ι ℝ) :=
  Measure.haarMeasure ⟨⟨univ, isCompact_univ⟩, by simpa only [interior_univ] using Set.univ_nonempty⟩

instance orthogonalHaar_probability : IsProbabilityMeasure (orthogonalHaar ι) := by
  constructor
  exact Measure.haarMeasure_self

instance orthogonalHaar_leftInvariant : IsMulLeftInvariant (orthogonalHaar ι) := by
  unfold orthogonalHaar
  infer_instance

instance orthogonalHaar_haar : IsHaarMeasure (orthogonalHaar ι) := by
  unfold orthogonalHaar
  infer_instance

instance orthogonalHaar_rightInvariant : IsMulRightInvariant (orthogonalHaar ι) := by
  constructor
  intro g
  let ν := (orthogonalHaar ι).map (· * g)
  have hν : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (continuous_mul_right g).measurable.aemeasurable
  have he := isMulInvariant_eq_smul_of_compactSpace ν (orthogonalHaar ι)
  have hf := congrArg (fun μ : Measure (Matrix.orthogonalGroup ι ℝ) => μ univ) he
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hf
  have hf' : haarScalarFactor ν (orthogonalHaar ι) = 1 := by exact_mod_cast hf.symm
  rw [hf', one_smul] at he
  exact he

lemma euclideanMatrix_mul_apply (A B : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    (A*B).toEuclideanLin x = A.toEuclideanLin (B.toEuclideanLin x) := by
  exact congrArg (fun L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι => L x)
    (Matrix.toLpLin_mul 2 2 2 A B)

lemma euclideanMatrix_one_apply (x : EuclideanSpace ℝ ι) :
    (1 : Matrix ι ι ℝ).toEuclideanLin x = x := by
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply]

lemma orthogonal_inner_map (U : Matrix.orthogonalGroup ι ℝ) (x y : EuclideanSpace ℝ ι) :
    inner ℝ ((U : Matrix ι ι ℝ).toEuclideanLin x) ((U : Matrix ι ι ℝ).toEuclideanLin y) =
      inner ℝ x y := by
  rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    ← euclideanMatrix_mul_apply]
  rw [← Matrix.star_eq_conjTranspose, Unitary.star_mul_self_of_mem U.property,
    euclideanMatrix_one_apply]

def orthogonalIsometry (U : Matrix.orthogonalGroup ι ℝ) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι where
  toLinearMap := (U : Matrix ι ι ℝ).toEuclideanLin
  invFun := (star (U : Matrix ι ι ℝ)).toEuclideanLin
  left_inv x := by
    change (star (U : Matrix ι ι ℝ)).toEuclideanLin ((U : Matrix ι ι ℝ).toEuclideanLin x) = x
    rw [← euclideanMatrix_mul_apply, Unitary.star_mul_self_of_mem U.property,
      euclideanMatrix_one_apply]
  right_inv x := by
    change (U : Matrix ι ι ℝ).toEuclideanLin ((star (U : Matrix ι ι ℝ)).toEuclideanLin x) = x
    rw [← euclideanMatrix_mul_apply, Unitary.mul_star_self_of_mem U.property,
      euclideanMatrix_one_apply]
  norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr (orthogonal_inner_map U)

def matrixOfIsometry (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) : Matrix.orthogonalGroup ι ℝ :=
  ⟨U.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis (EuclideanSpace.basisFun ι ℝ).toBasis,
    U.toMatrix_mem_unitaryGroup _ _⟩

end


section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sphereMap (U : E ≃ₗᵢ[ℝ] E) (u : sphere (0:E) 1) : sphere (0:E) 1 :=
  ⟨U u.val, mem_sphere_zero_iff_norm.mpr (by rw [U.norm_map]; exact mem_sphere_zero_iff_norm.mp u.property)⟩

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev unitSphere (ι : Type*) [Fintype ι] := Metric.sphere (0 : EuclideanSpace ℝ ι) 1

def orthogonalSphere (U : Matrix.orthogonalGroup ι ℝ) (u : unitSphere ι) : unitSphere ι :=
  sphereMap (orthogonalIsometry U) u

variable [Nonempty ι]

def sphereArea : ℝ := (volume : Measure (EuclideanSpace ℝ ι)).toSphere.real Set.univ

def sphereAverage (f : unitSphere ι → ℝ) : ℝ :=
  (∫ u, f u ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) / sphereArea (ι := ι)

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def sphereUniform : Measure (unitSphere ι) :=
  ((volume : Measure (EuclideanSpace ℝ ι)).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ ι)).toSphere

instance sphereUniform_probability : IsProbabilityMeasure (sphereUniform (ι := ι)) := by
  constructor
  rw [sphereUniform, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (measure_univ_pos.mpr (Measure.toSphere_ne_zero _)).ne'
    (measure_ne_top _ _)

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagonalEnergy (lam : ι → ℝ) (x : EuclideanSpace ℝ ι) : ℝ := ∑ i, lam i * x i ^ 2

def pairIntegrand (lam : ι → ℝ) (x y : EuclideanSpace ℝ ι) (q : ℝ)
    (U : Matrix.orthogonalGroup ι ℝ) : ℝ :=
  Real.exp (((1+q)*diagonalEnergy lam (orthogonalIsometry U x) +
    (1-q)*diagonalEnergy lam (orthogonalIsometry U y))/2)

def pairMoment (lam : ι → ℝ) (x y : EuclideanSpace ℝ ι) (q : ℝ) : ℝ :=
  ∫ U, pairIntegrand lam x y q U ∂orthogonalHaar ι

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def spherePartition (lam : ι → ℝ) (a r : ℝ) : ℝ :=
  sphereAverage (fun u => Real.exp (a / 2 * diagonalEnergy lam (r • u.val)))

end


section

def rotatedCubePartition {n : ℕ} (lam : Fin n → ℝ) (a : ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : ℝ :=
  (Fintype.card (Spin n) : ℝ)⁻¹ * ∑ x : Spin n,
    Real.exp (a/2 * diagonalEnergy lam (orthogonalIsometry U (cubeVector x)))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def overlapPlus (u v : EuclideanSpace ℝ ι) (q : ℝ) : EuclideanSpace ℝ ι :=
  Real.sqrt ((1+q)/2) • u + Real.sqrt ((1-q)/2) • v

def overlapMinus (u v : EuclideanSpace ℝ ι) (q : ℝ) : EuclideanSpace ℝ ι :=
  Real.sqrt ((1+q)/2) • u - Real.sqrt ((1-q)/2) • v

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable [Nonempty ι]

def spherePairEnergy (lam : ι → ℝ) (r : ℝ) (p : unitSphere ι × unitSphere ι) : ℝ :=
  Real.exp ((diagonalEnergy lam (r • p.1.val) + diagonalEnergy lam (r • p.2.val))/2)

def sphereOverlapLaw (ι : Type*) [Fintype ι] : Measure ℝ :=
  ((sphereUniform (ι := ι)).prod sphereUniform).map
    (fun p : unitSphere ι × unitSphere ι => inner ℝ p.1.val p.2.val)

end

section

def spinProduct {n : ℕ} (x y : Spin n) : Spin n := fun i => x i == y i

lemma spinProduct_involution {n : ℕ} (x : Spin n) : Function.Involutive (spinProduct x) := by
  intro y
  funext i
  change (x i == (x i == y i)) = y i
  cases x i <;> cases y i <;> rfl

def spinProductEquiv {n : ℕ} (x : Spin n) : Spin n ≃ Spin n :=
  (spinProduct_involution x).toPerm

def signMean {n : ℕ} (x : Spin n) : ℝ := (∑ i, spinValue (x i)) / n

def spinFinsetEquiv (n : ℕ) : Spin n ≃ Finset (Fin n) where
  toFun x := Finset.univ.filter fun i => x i = true
  invFun s := fun i => decide (i ∈ s)
  left_inv x := by
    funext i
    simp
  right_inv s := by
    ext i
    simp

section

def radialGaussian (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal (r^(n-1) * Real.exp (-r^2))

end

end

def sphereRatio (t : ℝ) : ℝ := t / Real.sqrt (1+t^2)

def sphereRatioInv (q : ℝ) : ℝ := q / Real.sqrt (1-q^2)

def sphereOverlapShape (n : ℕ) (q : ℝ) : ℝ := (Real.sqrt (1-q^2))^(n-3)

def cylinderKernel (f : ℝ → ℝ≥0∞) (s r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(s^2+r^2))) * f (s / Real.sqrt (s^2+r^2))

def euclidSplit (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) : ℝ × EuclideanSpace ℝ (Fin n) :=
  (x 0, WithLp.toLp 2 (fun i => x i.succ))

def overlapShapeMeasure (n : ℕ) : Measure ℝ :=
  (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity (fun q => ENNReal.ofReal (sphereOverlapShape n q))

def normalizedOverlapShape (n : ℕ) : Measure ℝ :=
  ((overlapShapeMeasure n) Set.univ)⁻¹ • overlapShapeMeasure n

def firstUnit (n : ℕ) : unitSphere (Fin (n+1)) :=
  ⟨EuclideanSpace.single 0 1, mem_sphere_zero_iff_norm.mpr (by simp)⟩

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.CubeOverlap
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
namespace CriticalSK

def latticeOverlap (n j : ℕ) : ℝ := -1 + 2 * j / n

def cubeOverlapMass (n j : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n * n.choose j

def binaryEntropyRate (q : ℝ) : ℝ :=
  ((1+q)*Real.log (1+q)+(1-q)*Real.log (1-q))/2

def stirlingLogError (n : ℕ) : ℝ := Real.log (Stirling.stirlingSeq n) - Real.log Real.pi/2

def scaledOverlapShape (n : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt (1-x^2/(n+6)))^(n+3)

def sphereOverlapDensity (n : ℕ) (q : ℝ) : ℝ :=
  sphereOverlapShape n q / (∫ r : ℝ, sphereOverlapShape n r)

def outwardBinLeft (δ q : ℝ) : ℝ := if q < 0 then q-δ else if 0 < q then q else -δ/2

def outwardBin (δ q : ℝ) : Set ℝ := Ioc (outwardBinLeft δ q) (outwardBinLeft δ q+δ)

def overlapCentralCutoff (n : ℕ) : ℝ := (n:ℝ)^(-(7/24:ℝ))

open MeasureTheory Set

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.SphereSaddle
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
namespace CriticalSK



section

variable {ι : Type*} [Fintype ι]

def gaussianPiPDF (v : ι → ℝ≥0) (x : ι → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 (v i) (x i)

def diagonalGaussian (v : ι → ℝ≥0) : Measure (EuclideanSpace ℝ ι) :=
  (Measure.pi (fun i => gaussianReal 0 (v i))).map (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)

instance diagonalGaussian_probability (v : ι → ℝ≥0) : IsProbabilityMeasure (diagonalGaussian v) := by
  unfold diagonalGaussian
  exact Measure.isProbabilityMeasure_map (by fun_prop)

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

def normShell (a b : ℝ) : Set E := {x | a < ‖x‖ ∧ ‖x‖ ≤ b}

def radialDensity (μ : Measure E) (f : E → ℝ) (r : ℝ) : ℝ :=
  r ^ (Module.finrank ℝ E - 1) * ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere

def squareNormShell (s δ : ℝ) : Set E := {x | s < ‖x‖^2 ∧ ‖x‖^2 ≤ s+δ}

end

section

def splitPair (n : ℕ) (x : Fin (n+2) → ℝ) : (ℝ × ℝ) × (Fin n → ℝ) :=
  ((x 0, x 1), fun i => x i.succ.succ)

section

def squareDisk (s : ℝ) : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ s}

def squareAnnulus (s δ : ℝ) : Set (ℝ × ℝ) :=
  {p | s < p.1 ^ 2 + p.2 ^ 2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ s + δ}

def gaussianPairPrefactor (a b : ℝ≥0) : ℝ :=
  (Real.sqrt (2 * Real.pi * a) * Real.sqrt (2 * Real.pi * b))⁻¹

variable {Ω : Type*} [MeasurableSpace Ω]

def sumSquareShell (Z : Ω → ℝ) (s δ : ℝ) : Set ((ℝ × ℝ) × Ω) :=
  {p | s < p.1.1^2 + p.1.2^2 + Z p.2 ∧ p.1.1^2 + p.1.2^2 + Z p.2 ≤ s+δ}

end

section

variable {ι : Type*} [Fintype ι]

def piSquareSum (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

end

section

open Set Filter

variable {n : ℕ}

def diagonalSquareDensity {ι : Type*} [Fintype ι] (v : ι → ℝ≥0) (s : ℝ) : ℝ :=
  radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) (Real.sqrt s) /
    (2 * Real.sqrt s)

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def radialEval (p : sphere (0 : E) 1 × Ioi (0 : ℝ)) : E := p.2.val • p.1.val

def radialCone (A : Set (sphere (0 : E) 1)) : Set E := radialEval '' (A ×ˢ Set.univ)

def radialDensityOn (μ : Measure E) (f : E → ℝ) (A : Set (sphere (0 : E) 1)) (r : ℝ) : ℝ :=
  r ^ (Module.finrank ℝ E - 1) * ∫ u in A, f (r • u.val) ∂μ.toSphere

end

open Set Filter

variable {n : ℕ}

def diagonalSquareDensityOn {ι : Type*} [Fintype ι] (v : ι → ℝ≥0)
    (A : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) (s : ℝ) : ℝ :=
  radialDensityOn volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) A (Real.sqrt s) /
    (2*Real.sqrt s)

end

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def gaussianPiPrefactor (v : ι → ℝ≥0) : ℝ := ∏ i, (Real.sqrt (2 * Real.pi * v i))⁻¹

end

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def sphereTilted (lam : ι → ℝ) (a r : ℝ) : Measure (unitSphere ι) :=
  (ENNReal.ofReal (∫ u : unitSphere ι, Real.exp (a / 2 * diagonalEnergy lam (r • u.val))
    ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere))⁻¹ •
  (volume : Measure (EuclideanSpace ℝ ι)).toSphere.withDensity
    (fun u => ENNReal.ofReal (Real.exp (a / 2 * diagonalEnergy lam (r • u.val))))

end

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
def gaussianSquareCoordinateDensity (v : ι → ℝ≥0) (i : ι) (s : ℝ) : ℝ :=
  radialDensity volume (fun x : EuclideanSpace ℝ ι => x i^2 * gaussianPiPDF v x) (Real.sqrt s) /
    (2*Real.sqrt s)

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.OverlapMoments
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
namespace CriticalSK

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateReflection (i : ι) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j =>
    if j=i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

end

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

def rotatedCubeRestricted {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : ℝ :=
  (Fintype.card (Spin n):ℝ)⁻¹ * ∑ x : Spin n,
    if |(orthogonalIsometry U (cubeVector x)) i| ≤ b then
      Real.exp (a/2*diagonalEnergy lam (orthogonalIsometry U (cubeVector x))) else 0

def rotatedCubeSmallBall {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : ℝ :=
  rotatedCubeRestricted lam 1 b i U/rotatedCubePartition lam 1 U

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.GaussianMatrices
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
namespace CriticalSK


section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def alignIsometry (e v : E) : E ≃ₗᵢ[ℝ] E :=
  Submodule.reflection (ℝ ∙ (v - ‖v‖ • e))ᗮ

variable {ι : Type*} [Fintype ι]

abbrev GaussianMatrix (ι : Type*) [Fintype ι] :=
  PiLp 2 (fun _ : ι => EuclideanSpace ℝ ι)

def transposeGaussianMatrix : GaussianMatrix ι ≃ₗᵢ[ℝ] GaussianMatrix ι where
  toFun A := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A j i))
  invFun A := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A j i))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' A := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_comm

@[simp] lemma transposeGaussianMatrix_apply (A : GaussianMatrix ι) (i j : ι) :
    transposeGaussianMatrix A i j = A j i := rfl

def rowIsometry (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    GaussianMatrix ι ≃ₗᵢ[ℝ] GaussianMatrix ι :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ι => U)

@[simp] lemma rowIsometry_apply (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) (i : ι) : rowIsometry U A i = U (A i) := rfl

def conjugateGaussianMatrix (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    GaussianMatrix ι ≃ₗᵢ[ℝ] GaussianMatrix ι :=
  (rowIsometry U).trans (transposeGaussianMatrix.trans
    ((rowIsometry U).trans transposeGaussianMatrix))

def symmetrizeGaussianMatrix (s : ℝ) (A : GaussianMatrix ι) : GaussianMatrix ι :=
  s • (A + transposeGaussianMatrix A)

def goeLaw (ι : Type*) [Fintype ι] (s : ℝ) : Measure (GaussianMatrix ι) :=
  (stdGaussian (GaussianMatrix ι)).map (symmetrizeGaussianMatrix s)

noncomputable def matrixUnit (i j : ι) : GaussianMatrix ι := by
  classical
  exact PiLp.single 2 i (EuclideanSpace.single j 1)

@[simp] lemma matrixUnit_inner (i j : ι) (A : GaussianMatrix ι) :
    inner ℝ (matrixUnit i j) A = A i j := by
  classical
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single i]
  · simp [matrixUnit, EuclideanSpace.inner_single_left]
  · intro k _ hki
    simp [matrixUnit, hki]
  · simp

@[simp] lemma matrixUnit_apply [DecidableEq ι] (i j k l : ι) :
    matrixUnit i j k l = if k = i ∧ l = j then 1 else 0 := by
  classical
  simp [matrixUnit]
  split_ifs <;> simp_all

def goeEntryVector (s : ℝ) (i j : ι) : GaussianMatrix ι :=
  s • (matrixUnit i j + matrixUnit j i)

variable [LinearOrder ι]

abbrev UpperEntry (ι : Type*) [LinearOrder ι] := {p : ι × ι // p.1 ≤ p.2}

end

section

open scoped NNReal

section Upper

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def upperRead (A : GaussianMatrix ι) : UpperEntry ι → ℝ := fun p => A p.1.1 p.1.2

def upperWrite (a : UpperEntry ι → ℝ) : GaussianMatrix ι :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j =>
    if h : i ≤ j then a ⟨(i, j), h⟩ else a ⟨(j, i), (le_of_not_ge h)⟩))

end Upper

def upperSplit (n : ℕ) : Unit ⊕ (Fin n ⊕ UpperEntry (Fin n)) ≃ UpperEntry (Fin (n + 1)) :=
  Equiv.ofBijective
    (fun x => match x with
      | Sum.inl _ => ⟨(0, 0), le_rfl⟩
      | Sum.inr (Sum.inl i) => ⟨(0, i.succ), Fin.zero_le _⟩
      | Sum.inr (Sum.inr p) => ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_le_succ_iff.mpr p.2⟩)
    ⟨by
      intro x y h
      have hz (i : Fin n) : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
      rcases x with u | (i | p) <;> rcases y with v | (j | q)
      all_goals simp_all [Subtype.ext_iff, Prod.ext_iff]
    , by
      rintro ⟨⟨i, j⟩, hij⟩
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact ⟨Sum.inl (), rfl⟩
        | succ j => exact ⟨Sum.inr (Sum.inl j), rfl⟩
      | succ i =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j => exact ⟨Sum.inr (Sum.inr ⟨(i, j), Fin.succ_le_succ_iff.mp hij⟩), rfl⟩⟩

@[simp] lemma upperSplit_diag (n : ℕ) : upperSplit n (Sum.inl ()) = ⟨(0, 0), le_rfl⟩ := rfl

@[simp] lemma upperSplit_column (n : ℕ) (i : Fin n) :
    upperSplit n (Sum.inr (Sum.inl i)) = ⟨(0, i.succ), Fin.zero_le _⟩ := rfl

@[simp] lemma upperSplit_tail (n : ℕ) (p : UpperEntry (Fin n)) :
    upperSplit n (Sum.inr (Sum.inr p)) =
      ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_le_succ_iff.mpr p.2⟩ := rfl

def goeUpperMarginal {ι : Type*} [LinearOrder ι] (s : ℝ) (p : UpperEntry ι) : Measure ℝ :=
  gaussianReal 0 (if p.1.1 = p.1.2 then (4 * s^2).toNNReal else (2 * s^2).toNNReal)

instance goeUpperMarginal_probability {ι : Type*} [LinearOrder ι] (s : ℝ) (p : UpperEntry ι) :
    IsProbabilityMeasure (goeUpperMarginal s p) := by
  unfold goeUpperMarginal
  infer_instance

def splitUpper (n : ℕ) (a : UpperEntry (Fin (n + 1)) → ℝ) :
    ℝ × ((Fin n → ℝ) × (UpperEntry (Fin n) → ℝ)) :=
  (a ⟨(0, 0), le_rfl⟩, ((fun i => a ⟨(0, i.succ), Fin.zero_le _⟩),
    fun p => a ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_le_succ_iff.mpr p.2⟩))

open scoped BigOperators

def extendTailIsometry {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun x := WithLp.toLp 2 (Fin.cases (x 0) (U (WithLp.toLp 2 (fun i => x i.succ))))
  invFun x := WithLp.toLp 2 (Fin.cases (x 0) (U.symm (WithLp.toLp 2 (fun i => x i.succ))))
  left_inv x := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => change U.symm (U (WithLp.toLp 2 (fun j => x j.succ))) i = x i.succ; simp
  right_inv x := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => change U (U.symm (WithLp.toLp 2 (fun j => x j.succ))) i = x i.succ; simp
  map_add' x y := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change U ((WithLp.toLp 2 (fun j => x j.succ)) + (WithLp.toLp 2 (fun j => y j.succ))) i = _
      simp
  map_smul' c x := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change U (c • WithLp.toLp 2 (fun j => x j.succ)) i = _
      simp
  norm_map' x := by
    change ‖(WithLp.toLp 2 (Fin.cases (x 0) (U (WithLp.toLp 2 (fun i => x i.succ)))) : EuclideanSpace ℝ (Fin (n + 1)))‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have h := congrArg (fun r : ℝ => r^2) (U.norm_map (WithLp.toLp 2 (fun j => x j.succ)))
    simp only [PiLp.norm_sq_eq_of_L2] at h ⊢
    simpa only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, PiLp.toLp_apply] using
      congrArg (fun t : ℝ => ‖x 0‖ ^ 2 + t) h

@[simp] lemma extendTailIsometry_zero {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin (n + 1))) : extendTailIsometry U x 0 = x 0 := rfl

@[simp] lemma extendTailIsometry_succ {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    extendTailIsometry U x i.succ = U (WithLp.toLp 2 (fun j => x j.succ)) i := rfl

@[simp] lemma extendTailIsometry_basis_zero {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    extendTailIsometry U (EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0) =
      EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0 := by
  ext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [extendTailIsometry_succ, EuclideanSpace.basisFun_apply]
    have h : (WithLp.toLp 2 fun j : Fin n => (EuclideanSpace.single 0 (1 : ℝ)) j.succ) = 0 := by
      ext j; simp
    rw [h, map_zero]
    simp

def borderMatrix {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) : GaussianMatrix (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.cases (WithLp.toLp 2 (Fin.cases a v))
    (fun i => WithLp.toLp 2 (Fin.cases (v i) (B i))))

@[simp] lemma borderMatrix_zero_zero {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) : borderMatrix a v B 0 0 = a := rfl

@[simp] lemma borderMatrix_zero_succ {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) (i : Fin n) : borderMatrix a v B 0 i.succ = v i := rfl

@[simp] lemma borderMatrix_succ_zero {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) (i : Fin n) : borderMatrix a v B i.succ 0 = v i := rfl

@[simp] lemma borderMatrix_succ_succ {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) (i j : Fin n) : borderMatrix a v B i.succ j.succ = B i j := rfl

def matrixTail {n : ℕ} (A : GaussianMatrix (Fin (n + 1))) : GaussianMatrix (Fin n) :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A i.succ j.succ))

def goeBlocks {n : ℕ} (A : GaussianMatrix (Fin (n + 1))) :
    ℝ × ((Fin n → ℝ) × GaussianMatrix (Fin n)) :=
  (A 0 0, (fun i => A 0 i.succ, matrixTail A))

end

section

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def orthoMatrix (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  fun i j => U (EuclideanSpace.basisFun ι ℝ j) i

def matrixOfGaussian (A : GaussianMatrix ι) : Matrix ι ι ℝ := fun i j => A i j

end

open scoped BigOperators

def firstAxis (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => if i.val = 0 then 1 else 0)

def firstColumn {n : ℕ} (A : GaussianMatrix (Fin (n+1))) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => A 0 i.succ)

def reducedTail {n : ℕ} (A : GaussianMatrix (Fin (n+1))) : GaussianMatrix (Fin n) :=
  conjugateGaussianMatrix (alignIsometry (firstAxis n) (firstColumn A)) (matrixTail A)

def triReduce : (n : ℕ) → GaussianMatrix (Fin n) → GaussianMatrix (Fin n)
  | 0, A => A
  | n+1, A => borderMatrix (A 0 0) (‖firstColumn A‖ • firstAxis n) (triReduce n (reducedTail A))

def triIsometry : (n : ℕ) → GaussianMatrix (Fin n) →
    (EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
  | 0, _ => LinearIsometryEquiv.refl _ _
  | n+1, A => (extendTailIsometry (alignIsometry (firstAxis n) (firstColumn A))).trans
      (extendTailIsometry (triIsometry n (reducedTail A)))

def columnNormLaw (n : ℕ) (s : ℝ) : Measure ℝ :=
  (Measure.pi fun _ : Fin n => gaussianReal 0 (2*s^2).toNNReal).map
    (fun v : Fin n → ℝ => ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖)

def assembleTri (n : ℕ) (p : ℝ × (ℝ × GaussianMatrix (Fin n))) : GaussianMatrix (Fin (n+1)) :=
  borderMatrix p.1 (p.2.1 • firstAxis n) p.2.2

def triMatrixLaw : (n : ℕ) → ℝ → Measure (GaussianMatrix (Fin n))
  | 0, s => goeLaw (Fin 0) s
  | n+1, s => ((gaussianReal 0 (4*s^2).toNNReal).prod
      ((columnNormLaw n s).prod (triMatrixLaw n s))).map (assembleTri n)

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.MinMax
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

namespace CriticalSK

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def basisSpan {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (s : Finset (Fin n)) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun i : s => b i))

def basisQuadratic {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) (x : E) : ℝ :=
  ∑ i, a i * (b.repr x i) ^ 2

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.PathSpectra
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
namespace CriticalSK

def edgeTent (m b i : ℕ) : ℝ := (min (min (i - b) m) (4 * m - (i - b)) : ℕ)

def tentCombination {r : ℕ} (m : ℕ) (c : Fin r → ℝ) (i : ℕ) : ℝ :=
  ∑ k, c k * edgeTent m (4*m*k.val) i

def tentMap (m n r : ℕ) : (Fin r → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n+1)) where
  toFun c := WithLp.toLp 2 (fun i => tentCombination m c i.val)
  map_add' c d := by
    ext i
    simp only [tentCombination, Pi.add_apply, PiLp.add_apply,
      add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    ext i
    simp only [tentCombination, Pi.smul_apply, smul_eq_mul,
      PiLp.smul_apply, RingHom.id_apply, mul_assoc, Finset.mul_sum]

def scaledHermite (a : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | k + 1 => X * scaledHermite a k - C a * derivative (scaledHermite a k)

@[simp] lemma scaledHermite_zero (a : ℝ) : scaledHermite a 0 = 1 := rfl

def jacobi (a : ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ := fun i j =>
  if i.val + 1 = j.val then Real.sqrt (a * ((k : ℝ) - 1 - i.val))
  else if j.val + 1 = i.val then Real.sqrt (a * ((k : ℝ) - 1 - j.val)) else 0

lemma jacobi_symmetric (a : ℝ) (k : ℕ) : (jacobi a k).IsSymm := by
  ext i j
  dsimp [jacobi, Matrix.transpose]
  split_ifs with h₁ h₂ h₃ <;> first | rfl | omega

lemma jacobi_hermitian (a : ℝ) (n : ℕ) : (jacobi a n).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (jacobi_symmetric a n)

section

def semicircleResolvent (s : ℝ) : ℝ := (2 + s - Real.sqrt (s * (4 + s))) / 2

def empiricalResolvent {ι : Type*} [Fintype ι] (e : ι → ℝ) (s : ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, (s + e i)⁻¹

def empiricalResolventSquare {ι : Type*} [Fintype ι] (e : ι → ℝ) (s : ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, (s + e i)⁻¹ ^ 2

end

open Matrix Polynomial Filter

noncomputable def jacobiGaps (n : ℕ) (i : Fin n) : ℝ :=
  2 - (jacobi_hermitian (n : ℝ)⁻¹ n).eigenvalues i

def pathOperator (n : ℕ) : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin (n+1)) := Matrix.toLpLin 2 2 (jacobi ((n+1 : ℝ)⁻¹) (n+1))

lemma pathOperator_symmetric (n : ℕ) : (pathOperator n).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (jacobi_hermitian _ _)

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.Powers
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

namespace CriticalSK

def edgeError (A B C s e : ℝ) : ℝ := A * (e + s) ^ (3 / 8 : ℝ) + B + C * e

open Set MeasureTheory Filter

open Set Filter MeasureTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.TriNoise
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

section

def scaleLength (J j : ℕ) : ℕ := 2 ^ (J - j)

def scaleRoot (J j : ℕ) : ℝ := (2 : ℝ)^j / (2 : ℝ)^J

def scaleEnergy (J j : ℕ) : ℝ := scaleRoot J j ^ 2

end

def entryVariance (n : ℕ) : ℝ≥0 := ⟨2 * (48 * Real.exp 1 + 4) / (n + 1), by positivity⟩

abbrev TriSample (n : ℕ) := (ℕ → ℝ) × ChiRows n

def triLaw (n : ℕ) : Measure (TriSample n) := (diagonalLaw n).prod (chiRowLaw n)

instance instIsProbabilityMeasureTriSampleTriLaw (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

def entryBad {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (h : ℝ) : Set Ω :=
  multiscaleBad X (entryVariance n) (fun j => scaleLength (Nat.clog 8 (n + 1)) j - 1)
    (Nat.clog 8 (n + 1) + 2) (n + 1) h

def triBad (n : ℕ) (h : ℝ) : Set (TriSample n) :=
  Prod.fst ⁻¹' entryBad n (fun i (ω : ℕ → ℝ) => ω i) h ∪
    Prod.snd ⁻¹' entryBad n (scaledChiRow n) h

def triForm (n : ℕ) (ω : TriSample n) (u : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range (n + 1), ω.1 i * u i ^ 2) +
    2 * ∑ i ∈ Finset.range n,
      (chi (chiRowDim n i) (ω.2 i) / Real.sqrt (n + 1 : ℝ)) * u i * u (i + 1)

def formError (n : ℕ) (h s e : ℝ) : ℝ :=
  41472 * Real.sqrt (32 * (entryVariance n : ℝ)) * (h + 1) *
    ((2 : ℝ)^(Nat.clog 8 (n + 1))) ^ (1 / 4 : ℝ) * (e + s) ^ (3 / 8 : ℝ) +
    8 / (n + 1) + 16 / Real.sqrt (n + 1 : ℝ) * e

instance instIsProbabilityMeasureTriSampleTriLaw_1 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_2 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_3 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_4 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_5 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_6 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_7 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_8 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_9 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_10 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_11 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_12 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_13 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_14 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_15 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_16 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_17 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_18 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_19 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_20 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance instIsProbabilityMeasureTriSampleTriLaw_21 (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.Resolvent
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

namespace CriticalSK


def triSampleMatrix (n : ℕ) (ω : TriSample n) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => (if i=j then ω.1 i.val else 0)+
    (if i.val+1=j.val then chi (chiRowDim n i.val) (ω.2 i.val)/Real.sqrt (n+1:ℝ) else 0)+
    (if j.val+1=i.val then chi (chiRowDim n j.val) (ω.2 j.val)/Real.sqrt (n+1:ℝ) else 0)

lemma triSampleMatrix_hermitian (n : ℕ) (ω : TriSample n) : (triSampleMatrix n ω).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,triSampleMatrix]
  by_cases h : i=j
  · subst j; ring
  · simp only [ite_eq_right h,ite_eq_right (Ne.symm h),zero_add,add_comm]

def triSampleOperator (n : ℕ) (ω : TriSample n) : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin (n+1)) := Matrix.toLpLin 2 2 (triSampleMatrix n ω)

lemma triSampleOperator_symmetric (n : ℕ) (ω : TriSample n) : (triSampleOperator n ω).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (triSampleMatrix_hermitian n ω)

def extendPath (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) (i : ℕ) : ℝ :=
  if hi : i<n+1 then x ⟨i,hi⟩ else 0

open MeasureTheory Set



open MeasureTheory Set


def formA (n : ℕ) (h : ℝ) : ℝ :=
  41472 * Real.sqrt (32 * (entryVariance n : ℝ)) * (h + 1) *
    ((2 : ℝ)^(Nat.clog 8 (n + 1))) ^ (1 / 4 : ℝ)

def formB (n : ℕ) : ℝ := 8 / (n+1)

def formC (n : ℕ) : ℝ := 16 / Real.sqrt (n+1:ℝ)

def orderedJacobiGaps (n : ℕ) (i : Fin (n+1)) : ℝ :=
  2-(pathOperator_symmetric n).eigenvalues (by simp) i

def sampleEigenvalues (n : ℕ) (ω : TriSample n) : Fin (n+1) → ℝ :=
  (triSampleOperator_symmetric n ω).eigenvalues (by simp)

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.GOESpectrum
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
namespace CriticalSK

open scoped InnerProductSpace

def gaussianMatrixCLM {n : ℕ} (A : GaussianMatrix (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toLpLin 2 2 (fun i j => A i j)).toContinuousLinearMap

def gaussianMatrixToCLM (n : ℕ) : GaussianMatrix (Fin n) →ₗ[ℝ]
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) where
  toFun := gaussianMatrixCLM
  map_add' A B := by
    ext x i
    change (∑ j, (A i j+B i j)*x j) = (∑ j, A i j*x j)+(∑ j, B i j*x j)
    simp only [add_mul,Finset.sum_add_distrib]
  map_smul' r A := by
    ext x i
    change (∑ j, (r*A i j)*x j) = r*(∑ j, A i j*x j)
    simp only [mul_assoc,Finset.mul_sum]

lemma gaussianMatrixCLM_symmetric {n : ℕ} (A : GaussianMatrix (Fin n))
    (hA : ∀ i j, A i j = A j i) : (gaussianMatrixCLM A).toLinearMap.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  ext i j
  exact hA j i

lemma symmetrize_half_entry {n : ℕ} (A : GaussianMatrix (Fin n)) (i j : Fin n) :
    symmetrizeGaussianMatrix (1/2:ℝ) A i j = (A i j + A j i)/2 := by
  change (1/2:ℝ)*(A i j+A j i) = _
  ring

lemma symmetrize_half_symmetric {n : ℕ} (A : GaussianMatrix (Fin n)) :
    ∀ i j, symmetrizeGaussianMatrix (1/2:ℝ) A i j = symmetrizeGaussianMatrix (1/2:ℝ) A j i := by
  intro i j
  rw [symmetrize_half_entry,symmetrize_half_entry,add_comm]

def matrixOrderedEigenvalues {n : ℕ} (A : GaussianMatrix (Fin n)) : Fin n → ℝ :=
  (gaussianMatrixCLM_symmetric _ (symmetrize_half_symmetric A)).eigenvalues (by simp : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)

def triEntriesLaw (n : ℕ) (s : ℝ) : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi fun i => (gaussianReal 0 (4*s^2).toNNReal).prod (columnNormLaw (n-i.val-1) s)

def triEntriesMatrix : (n : ℕ) → (Fin n → ℝ × ℝ) → GaussianMatrix (Fin n)
  | 0, _ => 0
  | n+1, p => assembleTri n ((p 0).1, (p 0).2, triEntriesMatrix n (fun i => p i.succ))

def goeScale (n : ℕ) : ℝ := (Real.sqrt (2*(n+1:ℝ)))⁻¹

def finiteChiEntry (n i : ℕ) (x : Fin (chiRowDim n i) → ℝ) : ℝ :=
  if i<n then chi (chiRowDim n i) x/Real.sqrt (n+1:ℝ) else 0

def sampleEntries (n : ℕ) (ω : TriSample n) (i : Fin (n+1)) : ℝ × ℝ :=
  (ω.1 i.val, finiteChiEntry n i.val (ω.2 i.val))

def spectralGood (n : ℕ) (h s : ℝ) : Set (Fin (n+1) → ℝ) :=
  {lam | ∀ i, |lam i-(2-orderedJacobiGaps n i)| ≤
    edgeError (formA n h) (formB n) (formC n) s (orderedJacobiGaps n i)}

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.Gibbs
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

namespace CriticalSK

section FiniteGibbs

variable {n : ℕ} (W : Disorder n)

lemma partition_pos : 0 < partition W := by
  unfold partition
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

lemma gibbs_pos (x : Spin n) : 0 < gibbs W x :=
  div_pos (Real.exp_pos _) (partition_pos W)

lemma gibbs_nonneg (x : Spin n) : 0 ≤ gibbs W x := (gibbs_pos W x).le

def spinFlip (x : Spin n) : Spin n := fun i => !(x i)

def spinFlipEquiv : Equiv.Perm (Spin n) := Equiv.piCongrRight (fun _ => Equiv.boolNot)

@[simp] lemma spinFlipEquiv_apply (x : Spin n) : spinFlipEquiv x = spinFlip x := rfl

@[simp] lemma spinFlip_spinFlip (x : Spin n) : spinFlip (spinFlip x) = x := by
  funext i
  simp [spinFlip]

@[simp] lemma spinValue_not (b : Bool) : spinValue (!b) = -spinValue b := by
  cases b <;> norm_num [spinValue]

@[simp] lemma hamiltonian_spinFlip (x : Spin n) :
    hamiltonian W (spinFlip x) = hamiltonian W x := by
  unfold hamiltonian
  apply Finset.sum_congr rfl
  intro e _
  simp [spinFlip]

@[simp] lemma gibbs_spinFlip (x : Spin n) : gibbs W (spinFlip x) = gibbs W x := by
  simp [gibbs]

@[simp] lemma linearObservable_spinFlip (a : Fin n → ℝ) (x : Spin n) :
    linearObservable a (spinFlip x) = -linearObservable a x := by
  simp [linearObservable, spinFlip, Finset.sum_neg_distrib]

lemma sameExcept_symm {i : Fin n} {x y : Spin n} (h : sameExcept i x y) :
    sameExcept i y x := by
  intro j hj
  exact (h j hj).symm

lemma sameExcept_trans {i : Fin n} {x y z : Spin n}
    (hxy : sameExcept i x y) (hyz : sameExcept i y z) : sameExcept i x z := by
  intro j hj
  exact (hyz j hj).trans (hxy j hj)

lemma sameExcept_classes {i : Fin n} {x y : Spin n} (h : sameExcept i x y)
    (z : Spin n) : sameExcept i x z ↔ sameExcept i y z :=
  ⟨sameExcept_trans (sameExcept_symm h), sameExcept_trans h⟩

def fiberMass (i : Fin n) (x : Spin n) : ℝ :=
  ∑ z : Spin n, if sameExcept i x z then gibbs W z else 0

lemma fiberMass_eq {i : Fin n} {x y : Spin n} (h : sameExcept i x y) :
    fiberMass W i x = fiberMass W i y := by
  unfold fiberMass
  apply Finset.sum_congr rfl
  intro z _
  simp only [sameExcept_classes h z]

lemma siteKernel_reversible (i : Fin n) (x y : Spin n) :
    gibbs W x * siteKernel W i x y = gibbs W y * siteKernel W i y x := by
  by_cases h : sameExcept i x y
  · have h' := sameExcept_symm h
    change gibbs W x * (if sameExcept i x y then gibbs W y / fiberMass W i x else 0) =
      gibbs W y * (if sameExcept i y x then gibbs W x / fiberMass W i y else 0)
    simp only [h, h', ite_true, fiberMass_eq W h]
    ring
  · have h' : ¬sameExcept i y x := fun hh => h (sameExcept_symm hh)
    simp [siteKernel, h, h']

end FiniteGibbs

variable {n : ℕ} (W : Disorder n)

def siteAverage (i : Fin n) (f : Spin n → ℝ) : Spin n → ℝ :=
  (siteKernel W i).mulVec f

def linearRest (a : Fin n → ℝ) (i : Fin n) (x : Spin n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, a j * spinValue (x j)

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.DisorderTransfer
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

def matrixDisorder {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Disorder n := fun e => A e.val.1 e.val.2

def matrixEnergy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) : ℝ :=
  (1/2:ℝ)*∑ i, ∑ j, A i j*spinValue (x i)*spinValue (x j)

def linearSmallBall {n : ℕ} (W : Disorder n) (a : Fin n → ℝ) (b : ℝ) : ℝ :=
  ∑ x, if |linearObservable a x| ≤ b then gibbs W x else 0

def smallBallObstruction (n : ℕ) (b δ : ℝ) : Set (Disorder n) :=
  {W | ∀ a : EuclideanSpace ℝ (Fin n), ‖a‖ = 1 → δ ≤ linearSmallBall W a b}

def rotatedDirection {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  (orthogonalIsometry U).symm (EuclideanSpace.basisFun (Fin n) ℝ i)

def haarConjugate {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) (A : GaussianMatrix (Fin n)) : GaussianMatrix (Fin n) :=
  conjugateGaussianMatrix (orthogonalIsometry U).symm A

open scoped NNReal

def gaussianDisorder {n : ℕ} (A : GaussianMatrix (Fin n)) : Disorder n :=
  matrixDisorder (matrixOfGaussian A)

end

open Set MeasureTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.EdgeAsymptotics
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

namespace CriticalSK


open scoped Topology

def edgeLength (n : ℕ) : ℕ := 2^(Nat.clog 8 (n+1))

def naturalEdgeScale (n : ℕ) (L : ℝ) : ℝ := L/(edgeLength n : ℝ)^2

def formConstant : ℝ := 41472*Real.sqrt (512*(48*Real.exp 1+4))

def traceCost (n : ℕ) (h s : ℝ) : ℝ :=
  416*formA n h*s^(-5/8:ℝ)+8*formB n/s+2*formC n/Real.sqrt s+
    2/((n+1:ℝ)*s*Real.sqrt s)

open scoped Topology

def edgeFixedCost (h L : ℝ) : ℝ :=
  416*formConstant*(h+1)*L^(-5/8:ℝ)+16/(L*Real.sqrt L)

def fixedEdgeVariance {ι : Type*} (lam : ι → ℝ) (s : ℝ) (i : ι) : NNReal :=
  ⟨max 0 ((2+s-lam i)⁻¹),le_max_left _ _⟩

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.HeatBath
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

namespace CriticalSK

open scoped InnerProductSpace

section GibbsEuclidean

variable {n : ℕ} (W : Disorder n)

lemma gibbs_sqrt_pos (x : Spin n) : 0 < Real.sqrt (gibbs W x) :=
  Real.sqrt_pos.mpr (gibbs_pos W x)

def gibbsEuclideanEquiv : (Spin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Spin n) where
  toFun f := WithLp.toLp 2 (fun x => Real.sqrt (gibbs W x) * f x)
  invFun v := fun x => v x / Real.sqrt (gibbs W x)
  left_inv f := by
    funext x
    simp [ne_of_gt (gibbs_sqrt_pos W x)]
  right_inv v := by
    ext x
    change Real.sqrt (gibbs W x) * (v x / Real.sqrt (gibbs W x)) = v x
    field_simp [ne_of_gt (gibbs_sqrt_pos W x)]
  map_add' f g := by ext x; simp [mul_add]
  map_smul' c f := by ext x; simp [mul_left_comm]

@[simp] lemma gibbsEuclideanEquiv_apply (f : Spin n → ℝ) (x : Spin n) :
    gibbsEuclideanEquiv W f x = Real.sqrt (gibbs W x) * f x := rfl

@[simp] lemma gibbsEuclideanEquiv_symm_apply (v : EuclideanSpace ℝ (Spin n)) (x : Spin n) :
    (gibbsEuclideanEquiv W).symm v x = v x / Real.sqrt (gibbs W x) := rfl

def kernelConjugate (K : Matrix (Spin n) (Spin n) ℝ) : Matrix (Spin n) (Spin n) ℝ :=
  fun x y => Real.sqrt (gibbs W x) * K x y / Real.sqrt (gibbs W y)

lemma kernelConjugate_isHermitian (K : Matrix (Spin n) (Spin n) ℝ)
    (hK : ∀ x y, gibbs W x * K x y = gibbs W y * K y x) :
    (kernelConjugate W K).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, star_trivial, kernelConjugate]
  apply (div_eq_div_iff (ne_of_gt (gibbs_sqrt_pos W x))
    (ne_of_gt (gibbs_sqrt_pos W y))).mpr
  have h := hK x y
  rw [← Real.sq_sqrt (gibbs_nonneg W x), ← Real.sq_sqrt (gibbs_nonneg W y)] at h
  nlinarith only [h]

lemma discreteKernel_reversible (x y : Spin n) :
    gibbs W x * discreteKernel W x y = gibbs W y * discreteKernel W y x := by
  simp only [discreteKernel, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  change gibbs W x * ((n : ℝ)⁻¹ * ∑ i, siteKernel W i x y) =
    gibbs W y * ((n : ℝ)⁻¹ * ∑ i, siteKernel W i y x)
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    gibbs W x * ((n : ℝ)⁻¹ * siteKernel W i x y) =
      (n : ℝ)⁻¹ * (gibbs W x * siteKernel W i x y) := by ring
    _ = (n : ℝ)⁻¹ * (gibbs W y * siteKernel W i y x) := by
      rw [siteKernel_reversible W i x y]
    _ = gibbs W y * ((n : ℝ)⁻¹ * siteKernel W i y x) := by ring

end GibbsEuclidean

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.PartitionBounds
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

namespace CriticalSK

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def spectralTop (lam : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty lam

lemma le_spectralTop (lam : ι → ℝ) (i : ι) : lam i ≤ spectralTop lam :=
  Finset.le_sup' lam (Finset.mem_univ i)

lemma spectralTop_attained (lam : ι → ℝ) : ∃ i, lam i = spectralTop lam := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty lam
  exact ⟨i,hi.symm⟩

def spectralStieltjes (lam : ι → ℝ) (r : ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, (r-lam i)⁻¹

def spectralStieltjesSlope (lam : ι → ℝ) (r : ℝ) : ℝ :=
  -(Fintype.card ι : ℝ)⁻¹ * ∑ i, ((r-lam i)⁻¹)^2

lemma cardinal_pos_real : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos

lemma spectralStieltjes_hasStrictDerivAt (lam : ι → ℝ) {r : ℝ} (hr : spectralTop lam < r) :
    HasStrictDerivAt (spectralStieltjes lam) (spectralStieltjesSlope lam r) r := by
  have h (i : ι) := (hasStrictDerivAt_inv (ne_of_gt (show 0 < r-lam i by linarith [le_spectralTop lam i]))).comp r ((hasStrictDerivAt_id r).sub_const (lam i))
  have hd := (HasStrictDerivAt.sum (u := Finset.univ) (fun i _ => h i)).const_mul (Fintype.card ι : ℝ)⁻¹
  convert! hd using 1
  · funext x; simp [spectralStieltjes, Finset.sum_apply]
  · unfold spectralStieltjesSlope
    simp only [mul_one,inv_pow,Finset.sum_neg_distrib,neg_mul,mul_neg]

lemma spectralStieltjes_continuous (lam : ι → ℝ) : ContinuousOn (spectralStieltjes lam) (Ioi (spectralTop lam)) :=
  fun _ hr => (spectralStieltjes_hasStrictDerivAt lam hr).hasDerivAt.continuousAt.continuousWithinAt

lemma spectralStieltjes_exists (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ r, spectralTop lam < r ∧ spectralStieltjes lam r = a := by
  let N : ℝ := Fintype.card ι
  have hN : 0 < N := cardinal_pos_real
  have hN1 : 1 ≤ N := by
    change (1:ℝ) ≤ Fintype.card ι
    exact_mod_cast (Fintype.card_pos (α := ι))
  let l := spectralTop lam + (N*a)⁻¹
  let u := spectralTop lam + a⁻¹
  have hl : spectralTop lam < l := by
    exact lt_add_of_pos_right _ (inv_pos.mpr (mul_pos hN ha))
  have hlu : l ≤ u := by
    dsimp [l,u]
    gcongr
    nlinarith
  have hlow : a ≤ spectralStieltjes lam l := by
    obtain ⟨i,hi⟩ := spectralTop_attained lam
    have hp (j : ι) : 0 ≤ (l-lam j)⁻¹ := by exact (inv_pos.mpr (by linarith [le_spectralTop lam j])).le
    have hsum := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
    have hmul := mul_le_mul_of_nonneg_left hsum (inv_pos.mpr hN).le
    have heq : N⁻¹ * (l-lam i)⁻¹ = a := by
      rw [hi]
      dsimp [l]
      rw [add_sub_cancel_left, inv_inv]
      field_simp
    rw [heq] at hmul
    exact hmul
  have hupp : spectralStieltjes lam u ≤ a := by
    have hh (i : ι) : (u-lam i)⁻¹ ≤ a := by
      have hle : a⁻¹ ≤ u-lam i := by dsimp [u]; linarith [le_spectralTop lam i]
      have hh := inv_anti₀ (inv_pos.mpr ha) hle
      simpa only [inv_inv] using hh
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hh i)
    have ht := mul_le_mul_of_nonneg_left hs (inv_pos.mpr hN).le
    change N⁻¹ * ∑ i, (u-lam i)⁻¹ ≤ a
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc, show (Fintype.card ι : ℝ) = N from rfl, inv_mul_cancel₀ hN.ne',one_mul] using ht
  have hc := (spectralStieltjes_continuous lam).mono (show Icc l u ⊆ Ioi (spectralTop lam) from fun _ hx => hl.trans_le hx.1)
  obtain ⟨r,hr,heq⟩ := intermediate_value_Icc' hlu hc ⟨hupp,hlow⟩
  exact ⟨r,hl.trans_le hr.1,heq⟩

def saddleRadius (lam : ι → ℝ) (a : ℝ) : ℝ :=
  if h : 0 < a then (spectralStieltjes_exists lam h).choose else 0

def saddleObjective (lam : ι → ℝ) (a z : ℝ) : ℝ :=
  (z-1)/2 - (2*(Fintype.card ι : ℝ))⁻¹ * ∑ i, Real.log (z-a*lam i)

def sphericalVariational (lam : ι → ℝ) (a : ℝ) : ℝ :=
  sInf (saddleObjective lam a '' Set.Ioi (a*spectralTop lam))

def saddleZ (lam : ι → ℝ) (a : ℝ) : ℝ :=
  if a = 0 then 1 else a*saddleRadius lam a

end

section

open Set

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def saddleVariance (lam : ι → ℝ) (a : ℝ) (i : ι) : ℝ≥0 :=
  Real.toNNReal ((saddleZ lam a-a*lam i)⁻¹)

end

def fixedBulkDeficit {n : ℕ} (lam : Fin (n+2) → ℝ) (s : ℝ) : ℝ :=
  (n+2)-(∑ i : Fin n, (fixedEdgeVariance lam s i.succ.succ:ℝ))

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.SaddleLimit
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

namespace CriticalSK

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def saddlePairDeficit (lam : ι → ℝ) (q : ℝ) : ℝ :=
  sphericalVariational lam (1+q)+sphericalVariational lam (1-q)-2*sphericalVariational lam 1

def saddlePairSlope (lam : ι → ℝ) (u : ℝ) : ℝ :=
  (saddleRadius lam (1+u)-(1+u)⁻¹)/2-(saddleRadius lam (1-u)-(1-u)⁻¹)/2

end

section

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]

def saddleSubcriticalError {κ : Type*} [Fintype κ] [Nonempty κ] (lam : κ → ℝ) : ℝ :=
  ∫ a in (0:ℝ)..1, |deriv (sphericalVariational lam) a-a/2|

end

open Set Filter

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.OrientationBounds
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



section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def correlatedVector (u v : EuclideanSpace ℝ ι) (t : ℝ) : EuclideanSpace ℝ ι :=
  t • u + Real.sqrt (1-t^2) • v

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable [Nonempty ι]

def sphereWeightedPair (lam : ι → ℝ) (r q : ℝ) (p : unitSphere ι × unitSphere ι) : ℝ :=
  Real.exp (((1+q)*diagonalEnergy lam (r • p.1.val)+(1-q)*diagonalEnergy lam (r • p.2.val))/2)

end

open Set MeasureTheory Filter

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


def naturalPartitionConstant (n : ℕ) (L : ℝ) : ℝ :=
  (naturalEdgeScale n L/4)*Real.exp (-6*(L*Real.sqrt L))

def naturalPartitionBase (L : ℝ) : ℝ := (L/32)*Real.exp (-6*(L*Real.sqrt L))

def naturalOrientationTail (n : ℕ) (L : ℝ) : ℝ :=
  (n+2:ℝ)*((26*Real.exp 1*(n+1)/naturalPartitionConstant n L)^2*
    Real.exp (-(n+1:ℝ)/24*overlapCentralCutoff (n+1)^3))

open Set MeasureTheory Filter

structure OrientationInputs {n : ℕ} [Nonempty (Fin n)]
    (lam : Fin n → ℝ) (K s : ℝ) : Prop where
  bounded : ∀ i, |lam i| ≤ 3
  Kpos : 0 < K
  partitionLower : K*Real.exp ((n:ℝ)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt n)
  scaleNonneg : 0 ≤ s
  topUpper : spectralTop lam < 2+s
  topLower : 2-s ≤ spectralTop lam
  trace : spectralStieltjes lam (2+s) ≤ 1
  traceUniform : ∀ t ∈ Icc s 1, |spectralStieltjes lam (2+t)-semicircleResolvent t| ≤ (1/100)*Real.sqrt t
  cutoff : 216*s ≤ overlapCentralCutoff n^2
  saddle : saddleSubcriticalError lam+s/2 ≤ 1/1536

def naturalOverlapRate (n : ℕ) (L : ℝ) : ℝ :=
  (16*Real.exp (6*(L*Real.sqrt L)))^2*16/((n+1)*Real.sqrt (naturalEdgeScale n L))

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.SmallBall
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

section

open Set MeasureTheory Filter

def naturalSmallBallConstant (L : ℝ) : ℝ := 4*Real.sqrt L*Real.exp (6*(L*Real.sqrt L))

end

open Set MeasureTheory Filter

instance disorderLaw_probability (n : ℕ) : IsProbabilityMeasure (disorderLaw n) := by
  unfold disorderLaw
  infer_instance

end CriticalSK

end

end OAI
end


