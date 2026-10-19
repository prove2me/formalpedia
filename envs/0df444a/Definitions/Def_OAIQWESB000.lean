-- Prove2me | Definitions.Def_OAIQWESB000
-- name    : OAIQWESB000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:19:52.151601+00:00
-- url     : https://prove2.me/theorems/8f73328e-2a2e-4264-bd43-36527e2bd573
-- title:
--   OpenAI Euclidean Steinitz–Bergström split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of the Euclidean Steinitz–Bergström theorem (`OAI.EuclideanSteinitzBergstrom.main`). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/Steinitz` (OpenAI, *The Euclidean Steinitz–Bergström theorem*, OpenAI Math Release, September 24, 2026, result family 097, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are the filter steps and their runs (`Step`, `Step.Good`, `run`, `Fresh`), the Gaussian autoregressive chains (`GaussianAR.row`, `GaussianAR.evaluation`), the $L^2$ heat operators (`HeatL2.spectralOp`, `HeatL2.heat`, `HeatL2.mask`, `HeatL2.compressedHeat`, `HeatL2.Diagonal.Bound`, `GaussianKernel.symbol`), the shifted sections (`ShiftedSections.Good`, `ShiftedSections.sectionNorm`), the application body (`EuclideanSteinitz.Filter.applicationDomain`) and the absolute constants of the proof (`GaussianAR.slabRadius`, `stateRadius`, `stateRate`, `bodyRate`, `bodyScale`, `universalConstant`). It also contains the lemmas those definitions use in their bodies (for example the bounds needed to build the multiplication and Fourier-multiplier operators on $L^2$), and three uses of `Measure.isProbabilityMeasure_map` where this Mathlib needs the measurability fact that newer Mathlib finds by instance search.
--
--   The definitions of the published statement (`Vector`, `SignedPrefixBound`, `OrderingPrefixBound`) are not repeated: the bundle imports them from the published bundle `Def_SteinitzBergstrom`. It imports no other bundle.
--
--   Modules: `Adaptive.lean`, `Chaining.lean`, `Coefficients.lean`, `Correlation.lean`, `Energy.lean`, `Filter.lean`, `FilteredBody.lean`, `FilterMoments.lean`, `Gain.lean`, `GaussianKernel.lean`, `GaussianProcess.lean`, `GaussianTail.lean`, `HeatEnergy.lean`, `HeatL2.lean`, `LiftedRearrangement.lean`, `Main.lean`, `MatrixEnergy.lean`, `PathLaws.lean`, `Predictor.lean`, `Prekopa.lean`, `Rearrangement.lean`, `Scales.lean`, `SectionEnergy.lean`, `SigningData.lean`, `Spectral.lean`, `Survival.lean`, `Transference.lean`.
--
--   The theorems of the development that the definitions do not need are proved in the seven solutions of this split. Five prove the published classical statements: Royen's Gaussian correlation inequality in three forms (`OAI.EuclideanSteinitz.GaussianCorrelation.stdGaussian_closed_convex_correlation`, `linear_image_closed_convex_correlation`, `linear_image_finite_correlation`, stated with Mathlib's definitions only), Chobanyan's transference (`OAI.EuclideanSteinitzBergstrom.signing_implies_ordering`) and the signs-with-adaptive-shifts proposition (`OAI.ShiftedSections.adaptive_linear_equations`). One proves the intermediate statement `OAI.EuclideanSteinitz.Filter.applicationDomain_survival`, and the last proves `OAI.EuclideanSteinitzBergstrom.main` from them. The Prékopa–Leindler inequality is not proved again here: the solutions import the published statement `ConvexOptimization.prekopa_leindler`.
-- source:
--   OpenAI, The Euclidean Steinitz–Bergström theorem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 097; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Steinitz at commit adc7f12

import Mathlib
import Definitions.Def_SteinitzBergstrom

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
end OAICompat434
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.MatrixEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar potentials and spectral endpoint inequalities. -/

namespace EuclideanSteinitz.MatrixEnergy

open Matrix
open scoped MatrixOrder

noncomputable def exponent : ℝ := 3 / 2

noncomputable def cutoff (x : ℝ) : ℝ :=
  if x ≤ 1 / 2 then 0 else if x < 1 then 2 * x - 1 else
    if x ≤ 2 then 1 else if x < 4 then 2 - x / 2 else 0

noncomputable def weight (x : ℝ) : ℝ := min (x ^ exponent) x⁻¹

noncomputable def potential (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, weight u / u

noncomputable def gainPotential (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, u ^ (exponent - 1) / (1 + u) ^ exponent

noncomputable def sizeWeight (x : ℝ) : ℝ := min (x ^ (exponent - 1)) x⁻¹

noncomputable def scalarRemainder (x y : ℝ) : ℝ :=
  potential x - potential y + (y / x - 1) * (weight x + weight y) / 2

section Scalar

noncomputable def rootWeight (u : ℝ) : ℝ :=
  if u ≤ 1 then u ^ 3 else (u ^ 2)⁻¹

end Scalar

end EuclideanSteinitz.MatrixEnergy

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real spectral calculus and noncommuting matrix inequalities. -/

namespace EuclideanSteinitz.Spectral
open Matrix
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def overlapBasis {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : unitaryGroup ι ℝ :=
  star hA.eigenvectorUnitary * hB.eigenvectorUnitary

end EuclideanSteinitz.Spectral

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Gain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contraction and gain potentials for positive semidefinite matrices. -/

namespace EuclideanSteinitz.Gain
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def inverseSqrt (M : Matrix ι ι ℝ) : Matrix ι ι ℝ := (CFC.sqrt M)⁻¹

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz.GainScalar
open MatrixEnergy

noncomputable def rate (x : ℝ) : ℝ :=
  Real.sqrt x / ((1 + x) * Real.sqrt (1 + x))

noncomputable def extendedRate (x : ℝ) : ℝ := rate (max 0 x)

noncomputable def primitive (x : ℝ) : ℝ := ∫ u in (0 : ℝ)..x, extendedRate u

end EuclideanSteinitz.GainScalar

namespace EuclideanSteinitz.Gain
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def relativeMoment (S V : Matrix ι ι ℝ) : ℝ :=
  (cfc (fun x : ℝ => x ^ exponent) (inverseSqrt S * V * inverseSqrt S)).trace

noncomputable def gainValue (D : Matrix ι ι ℝ) : ℝ := (cfc gainPotential D).trace

noncomputable def gainConstant : ℝ := exponent * 2 ^ exponent

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz.Gain
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure Move (ι : Type*) where
  contract : Matrix ι ι ℝ
  gain : Matrix ι ι ℝ

noncomputable def Move.old (p : Move ι) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  p.contract * M * p.contract.transpose

noncomputable def Move.next (p : Move ι) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ := p.old M + p.gain

def Move.Admissible (p : Move ι) : Prop :=
  p.contract * p.contract.transpose ≤ 1 ∧ p.gain.PosSemidef

noncomputable def follow (Z V : Matrix ι ι ℝ) : List (Move ι) → Matrix ι ι ℝ × Matrix ι ι ℝ
  | [] => (Z, V)
  | p :: ps => follow (p.old Z) (p.next V) ps

noncomputable def gainCost (D : Matrix ι ι ℝ) : List (Move ι) → ℝ
  | [] => 0
  | p :: ps => gainValue (p.next D) - gainValue (p.old D) + gainCost (p.next D) ps

end EuclideanSteinitz.Gain

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filtered coefficients and their quadratic energy bounds. -/

namespace EuclideanSteinitz.PotentialScalar
open MatrixEnergy

noncomputable def rate (x : ℝ) : ℝ := min (Real.sqrt x) ((max 1 x)⁻¹ ^ 2)
noncomputable def primitive (x : ℝ) : ℝ := ∫ u in (0 : ℝ)..x, rate u

end EuclideanSteinitz.PotentialScalar

namespace EuclideanSteinitz.Endpoint
open Matrix MatrixEnergy Spectral
open scoped MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def transportBasis {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (C : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * C * hB.eigenvectorUnitary

end EuclideanSteinitz.Endpoint

namespace EuclideanSteinitz.Coefficient
open Matrix MatrixEnergy Spectral Endpoint
open scoped MatrixOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def lift (R : Matrix ι κ ℝ) (A : Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  R.transpose * A * R

noncomputable def weightedSq (D : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) : ℝ :=
  (D * W * D.transpose).trace

end EuclideanSteinitz.Coefficient

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Telescoping matrix energy and trace budgets. -/

namespace EuclideanSteinitz.Energy
open Matrix MatrixEnergy Gain Spectral
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def pTrace (A : Matrix ι ι ℝ) : ℝ := (cfc potential A).trace
noncomputable def hTrace (A : Matrix ι ι ℝ) : ℝ := pTrace A + gainValue A

noncomputable def stepCost (p : Move ι) (D : Matrix ι ι ℝ) : ℝ :=
  hTrace D - hTrace (p.old D) + hTrace (p.next D) - hTrace (p.old D)

noncomputable def cost (D : Matrix ι ι ℝ) : List (Move ι) → ℝ
  | [] => 0
  | p :: ps => stepCost p D + cost (p.next D) ps

noncomputable def finish (D : Matrix ι ι ℝ) : List (Move ι) → Matrix ι ι ℝ
  | [] => D
  | p :: ps => finish (p.next D) ps

noncomputable def incrementConstant : ℝ :=
  230400 * (1 + 16 * gainConstant ^ (1 / exponent))

end EuclideanSteinitz.Energy

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Filter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric contraction updates and filtered matrix states. -/

namespace EuclideanSteinitz.Filter
open Matrix MatrixEnergy Gain Energy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

structure Step (ι κ : Type*) where
  C : Matrix ι ι ℝ
  b : ι → ℝ
  j : κ

noncomputable def insert (b : ι → ℝ) (j : κ) : Matrix ι κ ℝ :=
  fun i k => if k = j then b i else 0

noncomputable def Step.apply (p : Step ι κ) (R : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  p.C * R + insert p.b p.j

noncomputable def Step.move (p : Step ι κ) (q : κ → ℝ) : Move ι :=
  ⟨p.C, q p.j • vecMulVec p.b p.b⟩

def Step.Good (p : Step ι κ) : Prop :=
  IsUnit p.C ∧ p.C * p.C.transpose + vecMulVec p.b p.b = 1

noncomputable def run (R : Matrix ι κ ℝ) : List (Step ι κ) → Matrix ι κ ℝ
  | [] => R
  | p :: ps => run (p.apply R) ps

noncomputable def product : List (Step ι κ) → Matrix ι ι ℝ
  | [] => 1
  | p :: ps => product ps * p.C

noncomputable def state (q : κ → ℝ) (R : Matrix ι κ ℝ) : Matrix ι ι ℝ :=
  R * diagonal q * R.transpose

def Fresh (R : Matrix ι κ ℝ) (ps : List (Step ι κ)) : Prop :=
  ∀ p ∈ ps, ∀ i, R i p.j = 0

omit [Fintype ι] [DecidableEq ι] in
lemma insert_mul_transpose (b : ι → ℝ) (j : κ) :
    insert b j * (insert b j).transpose = vecMulVec b b := by
  ext i k
  simp [Matrix.mul_apply, insert, Matrix.transpose_apply, vecMulVec_apply]

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
lemma rankOne_psd (b : ι → ℝ) : (vecMulVec b b).PosSemidef := by
  have h := Matrix.PosSemidef.one.mul_mul_conjTranspose_same (insert (κ := Unit) b ())
  simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_one, insert_mul_transpose] using h

omit [Fintype κ] [DecidableEq κ] in
lemma Step.contract {p : Step ι κ} (hp : p.Good) : p.C * p.C.transpose ≤ 1 := by
  rw [← hp.2]
  exact le_add_of_nonneg_right (rankOne_psd p.b).nonneg

lemma state_posDef {R : Matrix ι κ ℝ} (hR : R * R.transpose = 1)
    {q : κ → ℝ} (hq : ∀ j, 0 < q j) : (state q R).PosDef := by
  have hi : Function.Injective R.vecMul := by
    intro x y hxy
    have hh := congrArg (fun v => R.transpose.vecMul v) hxy
    simpa only [Matrix.vecMul_vecMul, hR, Matrix.vecMul_one] using hh
  simpa only [state, conjTranspose_eq_transpose_of_trivial] using
    (Matrix.PosDef.diagonal hq).mul_mul_conjTranspose_same hi

omit [Fintype ι] [DecidableEq ι] in
noncomputable def newSet (ps : List (Step ι κ)) : Finset κ := (ps.map Step.j).toFinset

noncomputable def oldMask (J : Finset κ) : Matrix κ κ ℝ := diagonal (fun j => if j ∈ J then 0 else 1)
noncomputable def oldQ (J : Finset κ) (q : κ → ℝ) : Matrix κ κ ℝ :=
  diagonal (fun j => if j ∈ J then 0 else q j)
noncomputable def newQ (J : Finset κ) (q : κ → ℝ) : Matrix κ κ ℝ :=
  diagonal (fun j => if j ∈ J then q j else 0)

end EuclideanSteinitz.Filter

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Scales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform dyadic scale-energy estimates. -/

namespace EuclideanSteinitz.ScaleMatrix
open Matrix MatrixEnergy Gain Energy Spectral
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def primitiveTrace (A : Matrix ι ι ℝ) : ℝ :=
  (cfc PotentialScalar.primitive A).trace + (cfc GainScalar.primitive A).trace

noncomputable def rateMatrix (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  cfc PotentialScalar.rate A + cfc GainScalar.extendedRate A

noncomputable def scaleTrace (S : Finset ℤ) (A : Matrix ι ι ℝ) : ℝ :=
  ∑ n ∈ S, (2 : ℝ) ^ n * primitiveTrace (((2 : ℝ) ^ n)⁻¹ • A)

noncomputable def scaleRate (S : Finset ℤ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  ∑ n ∈ S, rateMatrix (((2 : ℝ) ^ n)⁻¹ • A)

end EuclideanSteinitz.ScaleMatrix

namespace EuclideanSteinitz.ScaleEnergy
open Matrix MatrixEnergy Gain Energy ScaleMatrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def rescale (c : ℝ) (p : Move ι) : Move ι := ⟨p.contract, c • p.gain⟩

noncomputable def aggregateCost (S : Finset ℤ) (A : Matrix ι ι ℝ) : List (Move ι) → ℝ
  | [] => 0
  | p :: ps => scaleTrace S A - scaleTrace S (p.old A) + scaleTrace S (p.next A) -
      scaleTrace S (p.old A) + aggregateCost S (p.next A) ps

noncomputable def variation (A : Matrix ι ι ℝ) : List (Move ι) → ℝ
  | [] => 0
  | p :: ps => A.trace - (p.old A).trace + (p.next A).trace -
      (p.old A).trace + variation (p.next A) ps

noncomputable def gainSum (ps : List (Move ι)) : ℝ := (ps.map (fun p => p.gain.trace)).sum

end EuclideanSteinitz.ScaleEnergy

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.GaussianTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar and matrix Gaussian tail estimates. -/

section

open Matrix MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
namespace GaussianTail
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

noncomputable def matrixMap (B : Matrix κ ι ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  (Matrix.toEuclideanLin B).toContinuousLinearMap

noncomputable def squareMass (B : Matrix κ ι ℝ) : ℝ := ∑ i,∑ j,B i j^2

end GaussianTail

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.FilterMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filtered moments, prefix bounds, and rank-one contractions. -/

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def vectorMass (b : ι → ℝ) : ℝ := ∑ i,b i^2
noncomputable def eta (b : ι → ℝ) : ℝ := 1/(1+Real.sqrt (1-vectorMass b))
noncomputable def symmetricContraction (b : ι → ℝ) : Matrix ι ι ℝ := 1-eta b • vecMulVec b b
noncomputable def symmetricStep (b : ι → ℝ) (j : κ) : Step ι κ := ⟨symmetricContraction b,b,j⟩

end EuclideanSteinitz.Filter

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Predictor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Predictor-column energy and exact feedback cancellation. -/

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def rawRow (R : Matrix ι κ ℝ) (b : ι → ℝ) : κ → ℝ :=
  fun j => eta b*(b ⬝ᵥ (fun i => R i j))
noncomputable def predictorRows (R : Matrix ι κ ℝ) : List (Step ι κ) → List (κ → ℝ)
  | [] => []
  | p::ps => rawRow R p.b :: predictorRows (p.apply R) ps

omit [Fintype κ] [DecidableEq ι] in
lemma predictorRows_length (R : Matrix ι κ ℝ) (L : List (Step ι κ)) :
    (predictorRows R L).length=L.length := by
  induction L generalizing R with
  | nil => rfl
  | cons p ps ih => simp only [predictorRows,List.length_cons,ih]

end EuclideanSteinitz.Filter

end

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def rowMap (m : κ → ℝ) : EuclideanSpace ℝ κ →L[ℝ] ℝ := innerSL ℝ (WithLp.toLp 2 m)

noncomputable def noiseRow {ν : Type*} (m : ι⊕ν → ℝ) : ι⊕ν → ℝ :=
  Sum.elim (fun _ => 0) (fun j => m (Sum.inr j))

end EuclideanSteinitz.Filter

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.GaussianProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stationary Gaussian autoregressive rows and covariance identities. -/

section

open Matrix
open scoped BigOperators
namespace GaussianAR

noncomputable def row (r : ℝ) : ℕ → ℕ → ℝ
  | 0,k => if k=0 then 1 else 0
  | t+1,k => r*row r t k + if k=t+1 then Real.sqrt (1-r^2) else 0

lemma row_support (r : ℝ) {t k : ℕ} (h : t<k) : row r t k=0 := by
  induction t with
  | zero => simp [row,show k≠0 by omega]
  | succ t ih => simp [row,ih (by omega),show k≠t+1 by omega]

lemma row_diag (r : ℝ) (t : ℕ) : row r (t+1) (t+1) = Real.sqrt (1-r^2) := by
  simp [row,row_support r (Nat.lt_succ_self t)]

end GaussianAR

end

section

open Matrix
open scoped BigOperators RealInnerProductSpace
namespace GaussianAR
open GaussianTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def evaluation (r : ι → ℝ) (n : ℕ) (t : Fin (n+1)) : Matrix ι (Fin (n+1)×ι) ℝ :=
  fun i k => if i=k.2 then row (r i) t.val k.1.val else 0

end GaussianAR

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Chaining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian chaining, finite nets, and uniform process bounds. -/

section

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal BigOperators
namespace GaussianChaining

noncomputable def radius (A : ℝ) (j l : ℕ) : ℝ :=
  100*(A+1)*(2:ℝ)^j*(l+1)*(1/2:ℝ)^l
noncomputable def variance (A : ℝ) (j l : ℕ) : ℝ :=
  A*((2:ℝ)^j)^2*((1/2:ℝ)^l)^4

def exponent (j l : ℕ) : ℕ := j+25*(l+1)+4

end GaussianChaining

end

section

open Filter
open scoped Topology BigOperators
namespace GridNets

noncomputable def cell (l : ℕ) (a : ℝ) : ℕ := ⌊(64:ℝ)^l*a⌋₊

def InSquare (p : ℝ × ℝ) : Prop := 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

noncomputable def cellPair (l : ℕ) (p : ℝ × ℝ) : ℕ × ℕ := (cell l p.1,cell l p.2)

def grid (l : ℕ) : Finset (ℕ × ℕ) := Finset.range (64^l+1) ×ˢ Finset.range (64^l+1)

variable {I : Type*} [Fintype I] [Nonempty I]

noncomputable def point (p : I → ℝ × ℝ) (l : ℕ) (c : ℕ × ℕ) : I :=
  if h : ∃ i, cellPair l (p i) = c then h.choose else Classical.arbitrary I

noncomputable def rep (p : I → ℝ × ℝ) (l : ℕ) (i : I) : I := point p l (cellPair l (p i))

end GridNets

end

section

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal BigOperators Topology
namespace GaussianTail
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

@[simp] lemma matrixMap_add (B C : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) :
    matrixMap (B+C) x = matrixMap B x+matrixMap C x := by
  apply WithLp.ofLp_injective
  exact Matrix.add_mulVec _ _ _
@[simp] lemma matrixMap_sub (B C : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) :
    matrixMap (B-C) x = matrixMap B x-matrixMap C x := by
  apply WithLp.ofLp_injective
  exact Matrix.sub_mulVec _ _ _
@[simp] lemma matrixMap_zero (x : EuclideanSpace ℝ ι) : matrixMap (0 : Matrix κ ι ℝ) x = 0 := by
  apply WithLp.ofLp_injective
  exact Matrix.zero_mulVec _

end GaussianTail

namespace GaussianChaining
open GaussianTail GridNets

variable {ι κ I : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype I] [Nonempty I]

noncomputable def netEnd (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (l : ℕ) (i : I) : Matrix κ ι ℝ :=
  B (rep p l i)

noncomputable def netEdge (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) : ℕ → I → Matrix κ ι ℝ
  | 0,i => netEnd B p 0 i
  | l+1,i => netEnd B p (l+1) i-netEnd B p l i

noncomputable def edgeSet (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (l : ℕ) : Finset (Matrix κ ι ℝ) :=
  Finset.univ.image (netEdge B p l)

end GaussianChaining

end

section

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal NNReal BigOperators Topology
namespace GaussianChaining
open GaussianTail GridNets
variable {ι κ I : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype I]

noncomputable def sizeClass (k : ℝ) : ℕ :=
  if hk : 1/4 ≤ k then (exists_nat_pow_near (by linarith : (1:ℝ) ≤ 4*k) (by norm_num : (1:ℝ)<4)).choose else 0

end GaussianChaining

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Correlation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian correlation and symmetric convex events. -/

section

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix Gain
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def blockCov (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (D : Matrix κ κ ℝ) (t : ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := fromBlocks A (t • B) (t • B.transpose) D

def interpolate (p : ι → Bool) (R : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  fun i j => if p i = p j then R i j else t * R i j

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def laplaceKernel (z x : ι → ℝ) : ℝ := Real.exp (-∑ i, z i * x i)

noncomputable def squareLaw (R : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  (multivariateGaussian 0 R).map (fun x : EuclideanSpace ℝ ι => fun i => x i ^ 2 / 2)

instance squareLaw_isProbabilityMeasure (R : Matrix ι ι ℝ) :
    IsProbabilityMeasure (squareLaw R) :=
  by
  unfold squareLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

noncomputable def sumLaw (μ ν : Measure (ι → ℝ)) : Measure (ι → ℝ) :=
  (μ.prod ν).map (fun x => x.1 + x.2)

instance sumLaw_isProbabilityMeasure (μ ν : Measure (ι → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (sumLaw μ ν) :=
  by
  unfold sumLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

noncomputable def tripleSquareLaw (R : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  sumLaw (squareLaw R) (sumLaw (squareLaw R) (squareLaw R))

instance tripleSquareLaw_isProbabilityMeasure (R : Matrix ι ι ℝ) :
    IsProbabilityMeasure (tripleSquareLaw R) := inferInstanceAs
      (IsProbabilityMeasure (sumLaw (squareLaw R) (sumLaw (squareLaw R) (squareLaw R))))

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev PolynomialIndex (p : ι → ℝ[X]) := ∀ i, Fin ((p i).natDegree + 1)

def polynomialWeight (p : ι → ℝ[X]) (k : PolynomialIndex p) : ℝ :=
  ∏ i, (p i).coeff (k i)

def exponentVector {p : ι → ℝ[X]} (k : PolynomialIndex p) : ι → ℝ := fun i => (k i : ℝ)

def mixedMultiplier {p : ι → ℝ[X]} (k : PolynomialIndex p) (S : Finset ι) : ℝ :=
  ∏ i ∈ S, (k i : ℝ)

noncomputable def mixedPolynomial (p : ι → ℝ[X]) (S : Finset ι) (x : ι → ℝ) : ℝ :=
  ∏ i, if i ∈ S then Real.exp (-x i) * (p i).derivative.eval (Real.exp (-x i))
    else (p i).eval (Real.exp (-x i))

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def royenCoefficient (p : ι → Bool) (R : Matrix ι ι ℝ)
    (S : Finset ι) (t : ℝ) : ℝ :=
  -(deriv (fun u => ((interpolate p R u).submatrix
    (Subtype.val : S → ι) Subtype.val).det) t) / 2

noncomputable def polynomialExpectation (p : ι → ℝ[X]) (R : Matrix ι ι ℝ) : ℝ :=
  ∑ k : PolynomialIndex p, polynomialWeight p k *
    (Real.sqrt (diagonal (exponentVector k) * R + 1).det)⁻¹

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Polynomial _root_.Filter
open scoped unitInterval Topology

noncomputable def bernsteinP (n : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (a k) * bernsteinPolynomial ℝ n k

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory Polynomial _root_.Filter
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def continuousProduct (f : ι → C(ℝ, ℝ)) (x : ι → ℝ) : ℝ :=
  ∏ i, f i (Real.exp (-x i))

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory _root_.Filter
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def upperCutoff (n : ℕ) (a : ℝ) : C(ℝ, ℝ) :=
  ⟨fun y => min 1 (max 0 (1 + ((n : ℝ) + 1) * (y - a))), by fun_prop⟩

noncomputable def exponentialBox (a : ι → ℝ) : Set (ι → ℝ) :=
  {x | ∀ i, a i ≤ Real.exp (-x i)}

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory _root_.Filter
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def coordinatePi (f : κ → ι) : EuclideanSpace ℝ ι →L[ℝ] (κ → ℝ) :=
  ContinuousLinearMap.pi (fun i => EuclideanSpace.proj (f i))

noncomputable def coordinateCLM (f : κ → ι) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℝ)).symm.toContinuousLinearMap.comp
    (coordinatePi f)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] lemma coordinateCLM_apply (f : κ → ι) (x : EuclideanSpace ℝ ι) (i : κ) :
    coordinateCLM f x i = x (f i) := rfl

noncomputable def quadraticBox (t : ι → ℝ) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, x i ^ 2 / 2 ≤ t i}

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory _root_.Filter
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def innerCoordinates (u : ι → E) : E →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => innerSL ℝ (u i)))

omit [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma innerCoordinates_apply (u : ι → E) (x : E) (i : ι) :
    innerCoordinates u x i = ⟪u i, x⟫ := rfl

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory _root_.Filter InnerProductSpace
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def partialSlabs (u : ℕ → E) (r : ℕ → ℝ) (n : ℕ) : Set E :=
  {x | ∀ i, i < n → |⟪u i, x⟫| ≤ r i}

end EuclideanSteinitz.GaussianCorrelation

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Survival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian path survival with slab and state constraints. -/

section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
namespace GaussianEvents
variable {E F I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def constraints (A : I → E →L[ℝ] F) (R : I → ℝ) : Set E :=
  {x | ∀ i,‖A i x‖ ≤ R i}

end GaussianEvents

end

section

open Matrix MeasureTheory ProbabilityTheory
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
open MatrixEnergy Spectral Coefficient Gain Energy GaussianTail GaussianAR
variable {ι κ T : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Fintype T]

noncomputable def epochFactor : ℝ := 1+16*gainConstant
noncomputable def momentConstant : ℝ := incrementConstant+20
noncomputable def survivalRadius : ℝ := 800*(640*momentConstant+2)

end EuclideanSteinitz.Filter

end

section

open Matrix MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace GaussianAR
open GaussianTail EuclideanSteinitz.Coefficient EuclideanSteinitz.Filter
variable {ι κ J : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]  [Fintype J]
noncomputable def slabRadius : ℝ := 800*(640+2)

end GaussianAR

end

section

open Matrix GaussianTail MeasureTheory ProbabilityTheory
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
open MatrixEnergy Spectral Coefficient ScaleMatrix ScaleEnergy Energy GaussianAR
variable {ι κ T : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Fintype T]

noncomputable def stateRadius : ℝ := 4*survivalRadius
noncomputable def stateRate : ℝ := 84*epochFactor+2

end EuclideanSteinitz.Filter

end

section

open Matrix
open scoped BigOperators
namespace GaussianAR
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def pathMatrix (r : ι → ℝ) (n : ℕ) : Matrix (Fin (n+1)×ι) (Fin (n+1)×ι) ℝ :=
  fun i j => evaluation r n i.1 i.2 j

lemma pathMatrix_det (r : ι → ℝ) (n : ℕ) :
    (pathMatrix r n).det = (∏ i,Real.sqrt (1-(r i)^2))^n := by
  have htri : (pathMatrix r n).transpose.BlockTriangular (fun p => p.1) := by
    intro a b hab
    change (if b.2=a.2 then row (r b.2) b.1.val a.1.val else 0)=0
    split_ifs
    · exact row_support _ hab
    · rfl
  rw [← Matrix.det_transpose,htri.det_fintype]
  have hb (t : Fin (n+1)) : ((pathMatrix r n).transpose.toSquareBlock (fun p => p.1) t).det =
      ∏ i, row (r i) t.val t.val := by
    let e : ι ≃ {p : Fin (n+1)×ι // p.1=t} :=
      { toFun := fun i => ⟨(t,i),rfl⟩
        invFun := fun p => p.val.2
        left_inv := fun _ => rfl
        right_inv := fun p => by ext <;> simp [p.property] }
    rw [← Matrix.det_reindex_self e.symm]
    have he : Matrix.reindex e.symm e.symm
        ((pathMatrix r n).transpose.toSquareBlock (fun p => p.1) t) =
        diagonal (fun i => row (r i) t.val t.val) := by
      ext i j
      simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.toSquareBlock_def,
        Matrix.transpose_apply,pathMatrix,e,evaluation,Matrix.diagonal_apply]
      split_ifs with h <;> simp_all [eq_comm]
    rw [he,Matrix.det_diagonal]
  simp_rw [hb]
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero,row,ite_true,Fin.val_succ,row_diag,Finset.prod_const_one,one_mul]
  simp

lemma pathMatrix_det_pos (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ) :
    0 < (pathMatrix r n).det := by
  rw [pathMatrix_det]
  apply pow_pos
  exact Finset.prod_pos fun i _ => Real.sqrt_pos.mpr (by nlinarith [hr i,hr1 i])

lemma pathMatrix_lin_det (r : ι → ℝ) (n : ℕ) :
    (Matrix.toEuclideanLin (pathMatrix r n)).det=(pathMatrix r n).det := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin]

noncomputable def pathEquiv (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ) :
    EuclideanSpace ℝ (Fin (n+1)×ι) ≃L[ℝ] EuclideanSpace ℝ (Fin (n+1)×ι) :=
  (LinearMap.equivOfIsUnitDet (show IsUnit (Matrix.toEuclideanLin (pathMatrix r n)).det from by
    rw [pathMatrix_lin_det]
    exact isUnit_iff_ne_zero.mpr (pathMatrix_det_pos r hr hr1 n).ne')).toContinuousLinearEquiv

end GaussianAR

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.GaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal Gaussian kernels and their densities. -/

section

open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal
namespace GaussianKernel

variable {ι : Type*} [Fintype ι]

noncomputable def diagonalLaw (v : ι → ℝ≥0) : Measure (EuclideanSpace ℝ ι) :=
  (Measure.pi (fun i => gaussianReal 0 (v i))).map (toLp 2)

instance instIsProbabilityMeasureEuclideanSpaceRealDiagonalLaw (v : ι → ℝ≥0) : IsProbabilityMeasure (diagonalLaw v) :=
  by
  unfold diagonalLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

noncomputable def density (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∏ i, gaussianPDFReal 0 (v i) (x i)

lemma density_nonneg (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) : 0 ≤ density v x := by
  exact Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 (v i) (x i)

lemma density_continuous (v : ι → ℝ≥0) : Continuous (density v) := by
  unfold density gaussianPDFReal
  fun_prop

lemma density_le_zero (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) : density v x ≤ density v 0 := by
  unfold density
  apply Finset.prod_le_prod₀
  · intro i _
    exact gaussianPDFReal_nonneg _ _ _
  · intro i _
    simp only [gaussianPDFReal, sub_zero, PiLp.zero_apply, neg_zero, zero_pow (by decide : 2 ≠ 0),
      zero_div, Real.exp_zero, mul_one]
    apply mul_le_of_le_one_right (by positivity)
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

section Scale
variable [DecidableEq ι]

noncomputable def scaleMap (v : ι → ℝ≥0) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (fun i => Real.sqrt (v i : ℝ)))

end Scale

end GaussianKernel
open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.HeatL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Heat operators, weak coordinate derivatives, and Dirichlet energy. -/

section

open MeasureTheory FourierTransform Filter ComplexConjugate
open scoped Topology ComplexInnerProductSpace

namespace HeatL2

section Multiplier
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma memLp_mul_bounded (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : Lp ℂ 2 μ) :
    MemLp (fun x => m x * f x) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := C) (hm.mul (Lp.aestronglyMeasurable f))
  filter_upwards [hb] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

noncomputable def mulLp (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (memLp_mul_bounded m hm hb f).toLp _

lemma mulLp_coe (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : Lp ℂ 2 μ) :
    (mulLp m hm hb f : X → ℂ) =ᵐ[μ] fun x => m x * f x := MemLp.coeFn_toLp _

noncomputable def mulLinear (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := mulLp m hm hb
  map_add' f g := by
    apply Lp.ext
    filter_upwards [mulLp_coe m hm hb (f+g), mulLp_coe m hm hb f,
      mulLp_coe m hm hb g, Lp.coeFn_add f g, Lp.coeFn_add (mulLp m hm hb f) (mulLp m hm hb g)] with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply] at h₄ h₅
    rw [h₁, h₄, h₅, h₂, h₃, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [mulLp_coe m hm hb (c • f), mulLp_coe m hm hb f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (mulLp m hm hb f)] with x h₁ h₂ h₃ h₄
    simp only [Pi.smul_apply, smul_eq_mul] at h₃ h₄
    simp only [RingHom.id_apply]
    rw [h₁, h₃, h₄, h₂]
    ring

lemma mulLp_norm_le (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : Lp ℂ 2 μ) :
    ‖mulLp m hm hb f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulLp_coe m hm hb f, hb] with x hx hbx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hbx (norm_nonneg _)

noncomputable def mulOp (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (mulLinear m hm hb).mkContinuous C (mulLp_norm_le m hm hb)

lemma mulOp_coe (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : Lp ℂ 2 μ) :
    (mulOp m hm hb f : X → ℂ) =ᵐ[μ] fun x => m x * f x := mulLp_coe m hm hb f

lemma norm_sq_integral (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  have he := L2.inner_def (𝕜 := ℂ) f f
  simp only [inner_self_eq_norm_sq_to_K] at he
  change (‖f‖ : ℂ)^2 = ∫ x, (‖f x‖ : ℂ)^2 ∂μ at he
  simp only [← Complex.ofReal_pow, integral_complex_ofReal] at he
  exact Complex.ofReal_injective he

end Multiplier
end HeatL2

namespace HeatL2
section Translation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def translate (a : E) : Lp ℂ 2 (volume : Measure E) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x + a) (measurePreserving_add_right volume a)

lemma translate_coe (a : E) (f : Lp ℂ 2 (volume : Measure E)) :
    (translate a f : E → ℂ) =ᵐ[volume] fun x => f (x+a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume a)

noncomputable def phase (a ξ : E) : ℂ := Real.fourierChar (inner ℝ a ξ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma phase_continuous (a : E) : Continuous (phase a) :=
  (continuous_subtype_val.comp Real.continuous_fourierChar).comp (continuous_const.inner continuous_id)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma phase_norm (a ξ : E) : ‖phase a ξ‖ = 1 := Circle.norm_coe _

noncomputable def phaseOp (a : E) : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  mulOp (phase a) (phase_continuous a).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => (phase_norm a ξ).le)

lemma phaseOp_coe (a : E) (f : Lp ℂ 2 (volume : Measure E)) :
    (phaseOp a f : E → ℂ) =ᵐ[volume] fun ξ => phase a ξ * (f : E → ℂ) ξ :=
  mulOp_coe _ _ _ _

lemma translate_schwartz (a : E) (f : SchwartzMap E ℂ) :
    translate a (f.toLp 2) = (SchwartzMap.compSubConstCLM ℂ (-a) f).toLp 2 := by
  apply Lp.ext
  filter_upwards [translate_coe a (f.toLp 2),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp (f.coeFn_toLp 2),
    (SchwartzMap.compSubConstCLM ℂ (-a) f).coeFn_toLp 2] with x h₁ h₂ h₃
  simpa only [h₁, h₃, Function.comp_apply, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add] using h₂

lemma schwartz_fourier_translate (a : E) (f : SchwartzMap E ℂ) :
    ∀ ξ, (𝓕 (SchwartzMap.compSubConstCLM ℂ (-a) f)) ξ = phase a ξ * (𝓕 f) ξ := by
  intro ξ
  have he := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ E) (f : E → ℂ) a) ξ
  change (∫ x, Real.fourierChar (-inner ℝ x ξ) • f (x+a)) = _ at he
  change (∫ x, Real.fourierChar (-inner ℝ x ξ) • f (x - -a)) =
    phase a ξ * (∫ x, Real.fourierChar (-inner ℝ x ξ) • f x)
  simpa only [sub_neg_eq_add, Circle.smul_def, smul_eq_mul, phase, innerₗ_apply_apply,
    VectorFourier.fourierIntegral] using he

lemma fourier_translate (a : E) (f : Lp ℂ 2 (volume : Measure E)) :
    𝓕 (translate a f) = phaseOp a (𝓕 f) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := E) (F := ℂ) (p := 2) (μ := (volume : Measure E)) ENNReal.ofNat_ne_top).induction_on
    (p := fun g => 𝓕 (translate a g) = phaseOp a (𝓕 g)) f ?_ ?_
  · exact isClosed_eq (continuous_fourier.comp (translate a).continuous)
      ((phaseOp a).continuous.comp continuous_fourier)
  · intro g
    change 𝓕 (translate a (g.toLp 2)) = phaseOp a (𝓕 (g.toLp 2))
    rw [translate_schwartz, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
    apply Lp.ext
    filter_upwards [(𝓕 (SchwartzMap.compSubConstCLM ℂ (-a) g)).coeFn_toLp 2,
      phaseOp_coe a ((𝓕 g).toLp 2),
      (𝓕 g).coeFn_toLp 2] with ξ h₁ h₂ h₃
    rw [h₁, h₂, h₃, schwartz_fourier_translate]

end Translation
end HeatL2

namespace HeatL2
section TranslationContinuous
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma translate_sub_translate_norm_sq (a b : E) (f : Lp ℂ 2 (volume : Measure E)) :
    ‖translate a f - translate b f‖^2 =
      ∫ ξ, ‖phase a ξ - phase b ξ‖^2 * ‖(𝓕 f) ξ‖^2 := by
  have hs : 𝓕 (translate a f - translate b f) = 𝓕 (translate a f) - 𝓕 (translate b f) :=
    (Lp.fourierTransformₗᵢ E ℂ).map_sub _ _
  rw [← Lp.norm_fourier_eq (translate a f - translate b f), hs, fourier_translate,
    fourier_translate, norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (phaseOp a (𝓕 f)) (phaseOp b (𝓕 f)),
    phaseOp_coe a (𝓕 f),
    phaseOp_coe b (𝓕 f)] with ξ h₁ h₂ h₃
  simp only [Pi.sub_apply] at h₁
  rw [h₁, h₂, h₃, ← sub_mul, norm_mul, mul_pow]

lemma translate_continuous (f : Lp ℂ 2 (volume : Measure E)) :
    Continuous (fun a : E => translate a f) := by
  rw [continuous_iff_continuousAt]
  intro b
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun a : E => ‖translate a f - translate b f‖^2) (𝓝 b) (𝓝 0) := by
    simp_rw [translate_sub_translate_norm_sq]
    have hi := tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure E)) (l := 𝓝 b)
      (F := fun a ξ => ‖phase a ξ - phase b ξ‖^2 * ‖(𝓕 f) ξ‖^2)
      (f := fun _ => (0 : ℝ)) (fun ξ => 4 * ‖(𝓕 f) ξ‖^2)
    apply (by simpa using hi : _)
    · exact Filter.Eventually.of_forall fun a =>
        (((phase_continuous a).sub (phase_continuous b)).norm.pow 2).aestronglyMeasurable.mul
          ((Lp.aestronglyMeasurable (𝓕 f)).norm.pow 2)
    · apply Filter.Eventually.of_forall
      intro a
      apply Filter.Eventually.of_forall
      intro ξ
      have hn : ‖phase a ξ - phase b ξ‖ ≤ 2 := by
        calc
          _ ≤ ‖phase a ξ‖ + ‖phase b ξ‖ := norm_sub_le _ _
          _ = 2 := by rw [phase_norm, phase_norm]; norm_num
      have hs : ‖phase a ξ - phase b ξ‖^2 ≤ 4 := by nlinarith [norm_nonneg (phase a ξ-phase b ξ)]
      simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm] using
        mul_le_mul_of_nonneg_right hs (sq_nonneg ‖(𝓕 f) ξ‖)
    · exact ((Lp.memLp (𝓕 f)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul 4
    · apply Filter.Eventually.of_forall
      intro ξ
      have hc : Continuous (fun a : E => phase a ξ) :=
        (continuous_subtype_val.comp Real.continuous_fourierChar).comp
          (continuous_id.inner continuous_const)
      have hc' : Continuous (fun a : E => ‖phase a ξ - phase b ξ‖^2 * ‖(𝓕 f) ξ‖^2) :=
        ((hc.sub continuous_const).norm.pow 2).mul continuous_const
      simpa using hc'.tendsto b
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs, abs_norm] using
    (Real.continuous_sqrt.tendsto 0).comp ht

end TranslationContinuous
end HeatL2

namespace HeatL2
section Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def spectralOp (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    (hb : ∀ x, |m x| ≤ 1) : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (Lp.fourierTransformₗᵢ E ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (mulOp (fun x => (m x : ℂ)) (Complex.continuous_ofReal.comp_aestronglyMeasurable hm)
      (Filter.Eventually.of_forall fun x => by simpa using hb x)) ∘L
    (Lp.fourierTransformₗᵢ E ℂ).toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def heat (w : E → ℝ) (hw : AEStronglyMeasurable w volume)
    (hn : ∀ x, 0 ≤ w x) : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  spectralOp (fun x => Real.exp (-w x)) (Real.continuous_exp.comp_aestronglyMeasurable hw.neg)
    (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hn x)))

noncomputable def energy (w : E → ℝ) (f : Lp ℂ 2 (volume : Measure E)) : ℝ :=
  ∫ x, (1-Real.exp (-w x)) * ‖(𝓕 f) x‖^2

end Spectral
end HeatL2
namespace HeatL2
noncomputable def loss (x : ℝ) : ℝ := 1 - Real.exp (-x)

end HeatL2

namespace HeatL2
section Mask
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

omit [MeasurableSpace X] in
lemma indicator_one_norm_le (D : Set X) (x : X) : ‖D.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
  classical
  by_cases hx : x ∈ D <;> simp [hx]

noncomputable def mask (D : Set X) (hD : MeasurableSet D) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  mulOp (D.indicator (fun _ => (1 : ℂ)))
    (aestronglyMeasurable_const.indicator hD)
    (Filter.Eventually.of_forall (indicator_one_norm_le D))

noncomputable def supported (D : Set X) : Set (Lp ℂ 2 μ) :=
  {f | ∀ᵐ x ∂μ, x ∉ D → f x = 0}

end Mask

section Compressed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def compressedHeat (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  mask D hD ∘L heat w hw hn ∘L mask D hD

end Compressed
end HeatL2

namespace HeatL2
section Average
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

lemma integrable_translate (A : F →L[ℝ] E) (ν : Measure F) [IsFiniteMeasure ν]
    (f : Lp ℂ 2 (volume : Measure E)) : Integrable (fun z => translate (A z) f) ν := by
  apply Integrable.mono' (integrable_const ‖f‖)
    ((translate_continuous f).comp A.continuous).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => (translate (A z)).norm_map f |>.le

omit [FiniteDimensional ℝ F] [BorelSpace F] in
lemma average_norm_le (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν]
    (f : Lp ℂ 2 (volume : Measure E)) : ‖∫ z, translate (A z) f ∂ν‖ ≤ ‖f‖ := by
  simpa using norm_integral_le_of_norm_le_const
    (Filter.Eventually.of_forall fun z => (translate (A z)).norm_map f |>.le :
      ∀ᵐ z ∂ν, ‖translate (A z) f‖ ≤ ‖f‖)

noncomputable def averageLinear (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν] :
    Lp ℂ 2 (volume : Measure E) →ₗ[ℂ] Lp ℂ 2 (volume : Measure E) where
  toFun f := ∫ z, translate (A z) f ∂ν
  map_add' f g := by
    simp only [map_add]
    exact integral_add (integrable_translate A ν f) (integrable_translate A ν g)
  map_smul' c f := by simp only [map_smul, integral_smul, RingHom.id_apply]

noncomputable def average (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν] :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (averageLinear A ν).mkContinuous 1 (fun f => by change ‖∫ z, translate (A z) f ∂ν‖ ≤ 1 * ‖f‖; simpa using average_norm_le A ν f)

noncomputable def gaussianSymbol (A : F →L[ℝ] E) (ξ : E) : ℝ :=
  ‖(2*Real.pi) • A.adjoint ξ‖^2 / 2

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma gaussianSymbol_nonneg (A : F →L[ℝ] E) (ξ : E) : 0 ≤ gaussianSymbol A ξ := by
  unfold gaussianSymbol
  positivity

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma gaussianSymbol_continuous (A : F →L[ℝ] E) : Continuous (gaussianSymbol A) := by
  unfold gaussianSymbol
  fun_prop

end Average
end HeatL2

namespace HeatL2
section Energy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def directionalSymbol (e : E) (ξ : E) : ℝ := (2*Real.pi*inner ℝ e ξ)^2

end Energy
end HeatL2

open MeasureTheory FourierTransform Filter ComplexConjugate
open scoped Topology ComplexInnerProductSpace

namespace HeatL2

lemma sqrt_mix_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (t*a^2+u*b^2) ≤ Real.sqrt t*a+Real.sqrt u*b := by
  have hr : 0 ≤ Real.sqrt t*a+Real.sqrt u*b := by positivity
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hr, ?_⟩
  have h₁ := Real.sq_sqrt ht
  have h₂ := Real.sq_sqrt hu
  nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg t) ha) (mul_nonneg (Real.sqrt_nonneg u) hb)]

section Mixture
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

noncomputable def mixFun (t : ℝ) (f g : Lp ℂ 2 μ) (x : X) : ℂ :=
  (Real.sqrt (t*‖f x‖^2+(1-t)*‖g x‖^2) : ℝ)

lemma mixFun_memLp (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) (f g : Lp ℂ 2 μ) :
    MemLp (mixFun t f g) 2 μ := by
  have hu := sub_nonneg.mpr ht'
  have hmeas : AEStronglyMeasurable (mixFun t f g) μ := by
    unfold mixFun
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      (Real.continuous_sqrt.comp_aestronglyMeasurable
      ((((Lp.memLp f).aestronglyMeasurable.norm.pow 2).const_mul t).add
      (((Lp.memLp g).aestronglyMeasurable.norm.pow 2).const_mul (1-t))))
  apply MemLp.of_le ((Lp.memLp f).norm.const_mul (Real.sqrt t) |>.add
    ((Lp.memLp g).norm.const_mul (Real.sqrt (1-t)))) hmeas
  exact Filter.Eventually.of_forall fun x => by
    rw [mixFun, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    change _ ≤ ‖Real.sqrt t * ‖f x‖ + Real.sqrt (1-t) * ‖g x‖‖
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact sqrt_mix_bound t (1-t) ht hu _ _ (norm_nonneg _) (norm_nonneg _)

noncomputable def mixture (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) (f g : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (mixFun_memLp t ht ht' f g).toLp (mixFun t f g)

end Mixture

end HeatL2

open MeasureTheory FourierTransform Filter ComplexConjugate
open scoped Topology ComplexInnerProductSpace

open MeasureTheory Filter ComplexConjugate
open scoped ComplexInnerProductSpace ENNReal

namespace HeatL2
section Absolute
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma abs_memLp (f : Lp ℂ 2 μ) : MemLp (fun x => (‖f x‖ : ℂ)) 2 μ := by
  apply MemLp.of_le (Lp.memLp f)
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.memLp f).aestronglyMeasurable.norm)
  exact Filter.Eventually.of_forall fun x => by simp

noncomputable def absolute (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (abs_memLp f).toLp (fun x => (‖f x‖ : ℂ))

lemma absolute_coe (f : Lp ℂ 2 μ) : (absolute f : X → ℂ) =ᵐ[μ] fun x => (‖f x‖ : ℂ) :=
  MemLp.coeFn_toLp _

lemma absolute_norm (f : Lp ℂ 2 μ) : ‖absolute f‖ = ‖f‖ := by
  have he : ∀ᵐ x ∂μ, ‖absolute f x‖ = ‖f x‖ := by
    filter_upwards [absolute_coe f] with x hx
    simp [hx]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (he.mono fun _ h => h.ge))

variable [IsFiniteMeasure μ]

noncomputable def oneLp : Lp ℂ 2 μ := Lp.const 2 μ 1

lemma oneLp_coe : ((oneLp : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun _ => 1 := Lp.coeFn_const 2 μ 1

lemma integral_norm_le (f : Lp ℂ 2 μ) : (∫ x, ‖f x‖ ∂μ) ≤ ‖(oneLp : Lp ℂ 2 μ)‖ * ‖f‖ := by
  have he : ⟪(oneLp : Lp ℂ 2 μ), absolute f⟫ = (∫ x, ‖f x‖ ∂μ : ℝ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [oneLp_coe (μ := μ), absolute_coe f] with x h₁ h₂
    simp only [h₁, h₂, RCLike.inner_apply, map_one, mul_one]
  calc
    _ = (⟪(oneLp : Lp ℂ 2 μ), absolute f⟫).re := by rw [he]; rfl
    _ ≤ ‖⟪(oneLp : Lp ℂ 2 μ), absolute f⟫‖ := Complex.re_le_norm _
    _ ≤ ‖(oneLp : Lp ℂ 2 μ)‖ * ‖absolute f‖ := norm_inner_le_norm _ _
    _ = _ := by rw [absolute_norm]

end Absolute

structure BoundedKernel (X : Type*) [MeasurableSpace X] where
  value : X × X → ℝ
  measurable : Measurable value
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  nonneg : ∀ p, 0 ≤ value p
  le_bound : ∀ p, value p ≤ bound

section Kernel
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable (k : BoundedKernel X)

noncomputable def kernelFun (f : Lp ℂ 2 μ) (x : X) : ℂ :=
  ∫ y, (k.value (x,y) : ℂ) * f y ∂μ

lemma kernel_section_integrable (f : Lp ℂ 2 μ) (x : X) :
    Integrable (fun y => (k.value (x,y) : ℂ) * f y) μ := by
  apply Integrable.mono' (((Lp.memLp f).integrable (by norm_num : (1:ℝ≥0∞)≤2)).norm.const_mul k.bound)
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable
      (k.measurable.comp measurable_prodMk_left).aestronglyMeasurable).mul (Lp.memLp f).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun y => by
    change ‖(k.value (x,y) : ℂ) * f y‖ ≤ k.bound * ‖f y‖
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (k.nonneg _)]
    exact mul_le_mul_of_nonneg_right (k.le_bound _) (norm_nonneg _)

lemma kernelFun_bound (f : Lp ℂ 2 μ) (x : X) :
    ‖kernelFun k f x‖ ≤ k.bound * ∫ y, ‖f y‖ ∂μ := by
  unfold kernelFun
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono (kernel_section_integrable k f x).norm
    (((Lp.memLp f).integrable (by norm_num : (1:ℝ≥0∞)≤2)).norm.const_mul k.bound)
  intro y
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (k.nonneg _)]
  exact mul_le_mul_of_nonneg_right (k.le_bound _) (norm_nonneg _)

lemma kernelFun_norm_bound (f : Lp ℂ 2 μ) (x : X) :
    ‖kernelFun k f x‖ ≤ k.bound * ‖(oneLp : Lp ℂ 2 μ)‖ * ‖f‖ := by
  exact (kernelFun_bound k f x).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (integral_norm_le f) k.bound_nonneg)

lemma kernelFun_memLp (f : Lp ℂ 2 μ) : MemLp (kernelFun k f) 2 μ := by
  have hm : AEStronglyMeasurable (fun p : X × X => (k.value p : ℂ) * f p.2) (μ.prod μ) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable k.measurable.aestronglyMeasurable).mul
      (Lp.memLp f).aestronglyMeasurable.comp_snd
  apply MemLp.of_bound hm.integral_prod_right' (k.bound * ‖(oneLp : Lp ℂ 2 μ)‖ * ‖f‖)
  exact Filter.Eventually.of_forall (kernelFun_norm_bound k f)

noncomputable def kernelLp (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (kernelFun_memLp k f).toLp (kernelFun k f)

lemma kernelLp_coe (f : Lp ℂ 2 μ) : (kernelLp k f : X → ℂ) =ᵐ[μ] kernelFun k f :=
  MemLp.coeFn_toLp _

lemma kernelLp_add (f g : Lp ℂ 2 μ) : kernelLp k (f+g) = kernelLp k f+kernelLp k g := by
  apply Lp.ext
  filter_upwards [kernelLp_coe k (f+g), kernelLp_coe k f, kernelLp_coe k g,
    Lp.coeFn_add (kernelLp k f) (kernelLp k g)] with x h₁ h₂ h₃ h₄
  simp only [Pi.add_apply] at h₄
  rw [h₁, h₄, h₂, h₃]
  unfold kernelFun
  rw [← integral_add (kernel_section_integrable k f x) (kernel_section_integrable k g x)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g] with y hy
  simp only [hy, Pi.add_apply, mul_add]

lemma kernelLp_smul (c : ℂ) (f : Lp ℂ 2 μ) : kernelLp k (c • f) = c • kernelLp k f := by
  apply Lp.ext
  filter_upwards [kernelLp_coe k (c • f), kernelLp_coe k f, Lp.coeFn_smul c (kernelLp k f)] with x h₁ h₂ h₃
  simp only [Pi.smul_apply, smul_eq_mul] at h₃
  rw [h₁, h₃, h₂]
  unfold kernelFun
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with y hy
  simp only [hy, Pi.smul_apply, smul_eq_mul]
  ring

lemma kernelLp_norm_le (f : Lp ℂ 2 μ) :
    ‖kernelLp k f‖ ≤ (k.bound * ‖(oneLp : Lp ℂ 2 μ)‖^2) * ‖f‖ := by
  have h : ‖kernelLp k f‖ ≤ (k.bound * ‖(oneLp : Lp ℂ 2 μ)‖ * ‖f‖) * ‖(oneLp : Lp ℂ 2 μ)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [kernelLp_coe k f, oneLp_coe (μ := μ)] with x h₁ h₂
    rw [h₁, h₂, norm_one, mul_one]
    exact kernelFun_norm_bound k f x
  nlinarith [h]

noncomputable def kernelLinear : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := kernelLp k
  map_add' := kernelLp_add k
  map_smul' c f := by simpa only [RingHom.id_apply] using kernelLp_smul k c f

noncomputable def kernelOp : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (kernelLinear k).mkContinuous (k.bound * ‖(oneLp : Lp ℂ 2 μ)‖^2) (kernelLp_norm_le k)

noncomputable def pathMass (n : ℕ) : ℝ :=
  (⟪(oneLp : Lp ℂ 2 μ), (kernelOp k ^ n) oneLp⟫).re

end Kernel
end HeatL2

open MeasureTheory Filter
open scoped ENNReal ComplexInnerProductSpace

open MeasureTheory Filter
open scoped ComplexInnerProductSpace ENNReal
namespace HeatL2
section Restrict
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (D : Set X) (hD : MeasurableSet D)
noncomputable def extendLp (f : Lp ℂ 2 (μ.restrict D)) : Lp ℂ 2 μ :=
  ((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).toLp (D.indicator f)
noncomputable def restrictLp (f : Lp ℂ 2 μ) : Lp ℂ 2 (μ.restrict D) :=
  ((Lp.memLp f).restrict D).toLp f
end Restrict
end HeatL2

open MeasureTheory FourierTransform Filter Set
open scoped ComplexInnerProductSpace

open MeasureTheory ComplexConjugate
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2

section Density
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def densityKernel (p : E → ℝ) (hp : Measurable p) (hpn : ∀ x, 0 ≤ p x)
    (hpb : ∀ x, p x ≤ p 0) : BoundedKernel E where
  value xy := p (xy.2-xy.1)
  measurable := hp.comp (measurable_snd.sub measurable_fst)
  nonneg _ := hpn _
  bound := p 0
  bound_nonneg := hpn _
  le_bound _ := hpb _

end Density
end HeatL2

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.PathLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian heat kernels and autoregressive path laws. -/

section

open MeasureTheory ProbabilityTheory WithLp
open scoped NNReal ENNReal RealInnerProductSpace
namespace GaussianKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def symbol (v : ι → ℝ≥0) (ξ : EuclideanSpace ℝ ι) : ℝ :=
  (∑ i, (v i : ℝ)*(2*Real.pi*ξ i)^2)/2

omit [DecidableEq ι] in
lemma symbol_continuous (v : ι → ℝ≥0) : Continuous (symbol v) := by
  unfold symbol
  fun_prop

omit [DecidableEq ι] in
lemma symbol_nonneg (v : ι → ℝ≥0) (ξ : EuclideanSpace ℝ ι) : 0 ≤ symbol v ξ := by
  unfold symbol
  positivity

noncomputable def kernel (v : ι → ℝ≥0) : HeatL2.BoundedKernel (EuclideanSpace ℝ ι) :=
  HeatL2.densityKernel (density v) (density_continuous v).measurable (density_nonneg v) (density_le_zero v)

end GaussianKernel

open MeasureTheory ProbabilityTheory Set WithLp
open scoped NNReal ENNReal

end

section

open MeasureTheory Set Filter
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2

section Chain
variable {X : Type*} [MeasurableSpace X] (k : BoundedKernel X)
noncomputable def tailWeight : (n : ℕ) → X → (Fin n → X) → ℝ
  | 0, _, _ => 1
  | n+1, x, p => k.value (x,p 0) * tailWeight n (p 0) (fun i => p i.succ)

noncomputable def walk (μ : Measure X) (n : ℕ) (x : X) : ℝ :=
  ∫ p, tailWeight k n x p ∂Measure.pi (fun _ : Fin n => μ)

noncomputable def chainWeight (n : ℕ) (p : Fin (n+1) → X) : ℝ :=
  tailWeight k n (p 0) (fun i => p i.succ)

end Chain
end HeatL2

open MeasureTheory Set

end

section

open MeasureTheory WithLp Set
namespace GaussianAR

noncomputable def unpack (T I : Type*) [Fintype T] [Fintype I] :
    EuclideanSpace ℝ (T×I) ≃ᵐ (T → EuclideanSpace ℝ I) :=
  (MeasurableEquiv.toLp 2 (T×I → ℝ)).symm.trans ((MeasurableEquiv.curry T I ℝ).trans
    (MeasurableEquiv.piCongrRight (fun _ : T => (MeasurableEquiv.toLp 2 (I → ℝ)))))

end GaussianAR

end

section

open Matrix MeasureTheory ProbabilityTheory WithLp
open scoped RealInnerProductSpace ENNReal NNReal BigOperators
namespace GaussianAR
open GaussianKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def transition (r : ι → ℝ) (x y : EuclideanSpace ℝ ι) : ℝ :=
  ∏ i,(Real.sqrt (1-(r i)^2))⁻¹*gaussianPDFReal 0 1 ((y i-r i*x i)/Real.sqrt (1-(r i)^2))

end GaussianAR

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.HeatEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Survival-energy estimates and simultaneous diagonal separation. -/

section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexInnerProductSpace
namespace HeatL2
namespace Diagonal
variable {ι : Type*} [Fintype ι]

noncomputable def coordSymbol (i : ι) (ξ : EuclideanSpace ℝ ι) : ℝ := (2*Real.pi*ξ i)^2

def Bound (D : Set (EuclideanSpace ℝ ι)) (hD : MeasurableSet D) (c : ℝ) : Prop :=
  ∀ v : ι → ℝ≥0, Real.exp (-(c/2) * ∑ i, (v i:ℝ)) ≤
    ‖compressedHeat D hD (GaussianKernel.symbol v)
      (GaussianKernel.symbol_continuous v).aestronglyMeasurable (GaussianKernel.symbol_nonneg v)‖

end Diagonal
end HeatL2

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Prekopa
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prékopa inequalities and Gaussian log-concavity. -/

section

open MeasureTheory Set Filter
open scoped Topology

namespace Prekopa
open MeasureTheory Set Filter
open scoped Topology

noncomputable def gauss {n : ℕ} (c : ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.exp (-c * ∑ i, (x i)^2)

structure Nice {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop where
  continuous : Continuous f
  positive : ∀ x, 0 < f x
  bound : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x, f x ≤ C * gauss c x

end Prekopa

namespace Prekopa
open MeasureTheory Set Filter Metric
open scoped Topology

noncomputable def approx {n : ℕ} (c : ℝ) (k : ℕ) (A : Set (Fin n → ℝ))
    (x : Fin n → ℝ) : ℝ := gauss c x * Real.exp (-(k : ℝ) * infDist x A)

end Prekopa

open MeasureTheory Set ProbabilityTheory
open MeasureTheory Set ProbabilityTheory

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Rearrangement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical Steiner rearrangement and shifted section geometry. -/

section

open Set MeasureTheory
open scoped Pointwise
namespace ShiftedSections
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sectionDomain (K : Set E) (e : E) (ell s : ℝ) : Set E :=
  {y | ∃ c : ℝ, |c|+s < ell ∧ y+(c-s) • e ∈ K ∧ y+(c+s) • e ∈ K}

lemma section_open {K : Set E} (hK : IsOpen K) (e : E) (ell s : ℝ) :
    IsOpen (sectionDomain K e ell s) := by
  have he : sectionDomain K e ell s =
      ⋃ c : ℝ, ⋃ (_ : |c|+s<ell),
        ((fun y : E => y+(c-s) • e) ⁻¹' K) ∩ ((fun y : E => y+(c+s) • e) ⁻¹' K) := by
    ext y
    simp only [sectionDomain, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
    aesop
  rw [he]
  apply isOpen_iUnion
  intro c
  apply isOpen_iUnion
  intro _
  exact (hK.preimage (by fun_prop)).inter (hK.preimage (by fun_prop))

end ShiftedSections

end

section

open MeasureTheory Set Filter
open scoped ENNReal
namespace VerticalRearrangement

section Layer
variable {X U V : Type*} [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace V]
  {μ : Measure X} {ν : Measure U} {ρ : Measure V} [SFinite μ] [SFinite ν] [SFinite ρ]

noncomputable def layer (S : U → Set X) (ν : Measure U) (x : X) : ℝ≥0∞ :=
  ∫⁻ u, (S u).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ν

end Layer

noncomputable def centered (a : ℝ≥0∞) : Set ℝ :=
  {s | |s| < a.toReal / 2}

noncomputable def heightMeasure : Measure ℝ :=
  volume.withDensity (fun s : ℝ => ENNReal.ofReal |s|)

instance instSFiniteRealHeightMeasure : SFinite heightMeasure := by
  unfold heightMeasure
  infer_instance

section Rearranged
variable {X U V : Type*} [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace V]
  {μ : Measure X} {ν : Measure U} {ρ : Measure V} [SFinite μ] [SFinite ν] [SFinite ρ]

noncomputable def rearranged (S : U → Set X) (μ : Measure X) (ν : Measure U) : ℝ → ℝ≥0∞ :=
  layer (fun u => centered (μ (S u))) ν

end Rearranged

section FunctionLayers
variable {X : Type*} [MeasurableSpace X]
noncomputable def superlevel (f : X → ℝ) (u : ℝ) : Set X := {x | 0 < u ∧ u < f x}

end FunctionLayers
end VerticalRearrangement

open MeasureTheory Set Filter
open scoped ENNReal

end

section

open MeasureTheory Set Filter
open scoped ENNReal
namespace VerticalRearrangement
section Fibers
variable {X : Type*} [MeasurableSpace X]

noncomputable def fiberStar (F : X × ℝ → ℝ) (p : X × ℝ) : ℝ≥0∞ :=
  rearranged (superlevel (fun s => F (p.1,s))) volume volume p.2

end Fibers
end VerticalRearrangement

end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace ShiftedSections
variable {ι : Type*} [Fintype ι]

noncomputable def sectionNorm (K : Set (EuclideanSpace ℝ ι)) (hK : IsOpen K)
    (e : EuclideanSpace ℝ ι) (ell s : ℝ) (v : ι → ℝ≥0) : ℝ :=
  ‖HeatL2.compressedHeat (sectionDomain K e ell s) (section_open hK e ell s).measurableSet
    (GaussianKernel.symbol v) (GaussianKernel.symbol_continuous v).aestronglyMeasurable
    (GaussianKernel.symbol_nonneg v)‖

noncomputable def sectionRate (K : Set (EuclideanSpace ℝ ι)) (hK : IsOpen K)
    (e : EuclideanSpace ℝ ι) (ell : ℝ) (v : ι → ℝ≥0) (s : ℝ) : ℝ :=
  -Real.log (sectionNorm K hK e ell s v)

def activeHeights (K : Set (EuclideanSpace ℝ ι)) (e : EuclideanSpace ℝ ι) (ell : ℝ) : Set ℝ :=
  {s | 0 ≤ s ∧ (sectionDomain K e ell s).Nonempty}

end ShiftedSections

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.SectionEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Heat and energy inequalities for affine sections. -/

section

open MeasureTheory Set Filter
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2
section RealFunctions
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

noncomputable def complexLp (f : X → ℝ) (hf : MemLp f 2 μ) : Lp ℂ 2 μ :=
  hf.ofReal.toLp (fun x => (f x:ℂ))

noncomputable def nonnegRepresentative (D : Set X) (_hD : MeasurableSet D) (f : Lp ℂ 2 μ) : X → ℝ :=
  D.indicator (fun x => ‖(Lp.aestronglyMeasurable f).mk f x‖)

end RealFunctions

section Spatial
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

noncomputable def realDistance (f : E → ℝ) (a : E) : ℝ := ∫ x,(f (x+a)-f x)^2

end Spatial
end HeatL2

end

section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
namespace HeatL2
section Slice
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

noncomputable def sliceEnergy (ν : Measure F) (A : F →L[ℝ] E) (G : E × ℝ → ℝ) (s : ℝ) : ℝ :=
  (1/2:ℝ) * ∫ z, realDistance (fun x => G (x,s)) (A z) ∂ν

end Slice
end HeatL2

end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace ShiftedSections
variable {ι : Type*} [Fintype ι]

noncomputable def sliceMass (G : EuclideanSpace ℝ ι × ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ x,G (x,s)^2

end ShiftedSections

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.LiftedRearrangement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lifted fiber rearrangement and overlap estimates. -/

section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
namespace VerticalRearrangement
section Lift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def shear (e : E) : E × ℝ ≃ₜ E × ℝ where
  toFun p := (p.1+p.2 • e,p.2)
  invFun p := (p.1-p.2 • e,p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def liftFunction (ell c : ℝ) (e : E) (f : E → ℝ) (p : E × ℝ) : ℝ :=
  (Ioo (-ell) ell).indicator (fun s => c*f (p.1+s • e)) p.2

end Lift
end VerticalRearrangement

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Adaptive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy-preserving sections and adaptive coordinate selection. -/

section

open MeasureTheory Set
namespace ShiftedSections
open HeatL2.Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Coeff := EuclideanSpace ℝ ι

structure Good (K : Set (Coeff (ι := ι))) : Prop where
  nonempty : K.Nonempty
  isOpen : IsOpen K
  bounded : Bornology.IsBounded K
  convex : Convex ℝ K
  symmetric : ∀ x ∈ K,-x ∈ K
  bound : Bound K isOpen.measurableSet (1/10000)

noncomputable def backward : {n : ℕ} → (Fin n → ι) → Set (Coeff (ι := ι)) → Set (Coeff (ι := ι))
  | 0,_,K => K
  | _+1,j,K => sectionDomain (backward (fun i => j i.succ) K) (EuclideanSpace.single (j 0) 1) (5/2) 1

noncomputable def walk : {n : ℕ} → (Fin n → ι) → (Fin n → Coeff (ι := ι) → ℝ) →
    (Fin n → ℝ) → Coeff (ι := ι) → Coeff (ι := ι)
  | 0,_,_,_,x => x
  | _+1,j,q,ε,x => walk (fun i => j i.succ) (fun i => q i.succ) (fun i => ε i.succ)
      (x+(q 0 x+ε 0) • EuclideanSpace.single (j 0) 1)

end ShiftedSections

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.FilteredBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filtered-body energy and the predictor slab budget. -/

section

open Matrix GaussianTail MeasureTheory ProbabilityTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Pointwise NNReal
namespace GaussianEvents
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype I]
noncomputable def openConstraints (A : I → E →L[ℝ] F) (R : I → ℝ) : Set E :=
  {x | ∀ i,‖A i x‖ < R i}
end GaussianEvents

namespace EuclideanSteinitz.Filter
open GaussianAR GaussianEvents Coefficient
variable {ι κ T J : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Fintype T] [Fintype J] [Nonempty ι] [Nonempty κ]

noncomputable def bodyRate : ℝ := 2*stateRate+1
noncomputable def applicationDomain (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) : Set (EuclideanSpace ℝ κ) :=
  openConstraints (fun t => matrixMap (Rt t)) (fun _ => 2*stateRadius*Real.sqrt (Fintype.card ι)) ∩
  Metric.ball 0 (2*stateRadius*Real.sqrt (Fintype.card κ)) ∩
  openConstraints (fun j => matrixMap (H j)) (fun _ => 2*slabRadius)

noncomputable def bodyScale : ℝ := 1000*(2*bodyRate+1)

end EuclideanSteinitz.Filter

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.SigningData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized predictors and backward-forward shifted walks. -/

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
variable {ι ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

noncomputable def initialMatrix (ι ν : Type*) [DecidableEq ι] : Matrix ι (ι⊕ν) ℝ := Matrix.fromCols 1 0

noncomputable def familySteps {n : ℕ} (b : Fin n → ι → ℝ) : List (Step ι (ι⊕Fin n)) :=
  List.ofFn (fun i => symmetricStep (b i) (Sum.inr i))
noncomputable def familyPredictor {n : ℕ} (b : Fin n → ι → ℝ) (i : Fin n) : ι⊕Fin n → ℝ :=
  noiseRow ((predictorRows (initialMatrix ι (Fin n)) (familySteps b))[i.val]'
    (by rw [predictorRows_length]; simpa only [familySteps,List.length_ofFn] using i.isLt))

noncomputable def signingScale : ℝ := 1/(8*bodyScale*GaussianAR.slabRadius)

noncomputable def normalizedPredictor {n : ℕ} (b : Fin n → ι → ℝ) (i : Fin n) : Matrix Unit (ι⊕Fin n) ℝ :=
  fun _ k => familyPredictor b i k / signingScale

end EuclideanSteinitz.Filter

end

section

open MeasureTheory Set
namespace ShiftedSections
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def clip (u : ℝ) : ℝ := max (-(1/4)) (min u (1/4))

end ShiftedSections

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Transference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive-forward and negative-reverse permutation transference. -/

section

namespace EuclideanSteinitzBergstrom

noncomputable def walkPrefix {d N : ℕ} (v : Fin N → Vector d) (k : ℕ) : Vector d :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), v i

section Lists

variable {α E : Type*}

def signedOrder (p : α → Bool) (l : List α) : List α :=
  l.filter p ++ (l.filter fun a => !p a).reverse

end Lists

end EuclideanSteinitzBergstrom

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Euclidean Steinitz–Bergström theorem with one absolute constant. -/

section

open Matrix GaussianTail MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Pointwise

namespace EuclideanSteinitzBergstrom
open EuclideanSteinitz.Filter GaussianAR

noncomputable def universalConstant : ℝ := 2*bodyScale*stateRadius/signingScale

end EuclideanSteinitzBergstrom

end

end OAI
end


