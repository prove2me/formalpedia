-- Prove2me | Definitions.Def_OAIQWFE001
-- name    : OAIQWFE001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T01:05:44.52251+00:00
-- url     : https://prove2.me/theorems/4d2a60dd-15b5-41cf-963d-709805a48cc3
-- title:
--   OpenAI finite-entropy separation split: definitions bundle 2 (Hermite tensors, total second moment, auxiliary functions)
-- statement:
--   The second definitions bundle of the split of OpenAI's proof of `OAI.FiniteEntropySeparation.main`. It holds a few of OpenAI's definitions from `lean/OAI/Analysis/FreeEntropy` (OpenAI, *A finite-entropy separation of microstates and nonmicrostates free entropy*, OpenAI Math Release, September 25, 2026, result family 298, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a: the tensor Hermite polynomials `tensorHermite` and their weights `tensorWeight`, `optionTuple`, `reciprocalDifference`, `logarithmicPrimitive` and the total second moment `totalSecond`, with the lemmas they use. It imports the published bundle `Def_FiniteEntropySeparation` and no other bundle.
--
--   Modules: `GaussianHermite`, `TensorHermite`, `TensorGradient`, `OrthogonalExpansion`, `MatrixOperator`, `MatrixPolynomialNorm`, `MicrostatesSelection`, `MatrixBilinear`, `MatrixSpectralMoments`, `SpectralTestFunctions`, `SignalSeries`, `TotalSecond`, `EntropyIntegral`, `MatrixBlocks`.
-- source:
--   OpenAI, A finite-entropy separation of microstates and nonmicrostates free entropy, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 298; Apache License 2.0); definitions carved from lean/OAI/Analysis/FreeEntropy at commit adc7f12

import Mathlib
import Definitions.Def_FiniteEntropySeparation

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianHermite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Polynomial Finset
namespace FiniteEntropySeparation
 def realHermite (n : ℕ) : ℝ[X] := (Polynomial.hermite n).map (Int.castRingHom ℝ)
 @[simp] theorem realHermite_zero : realHermite 0 = 1 := by simp [realHermite]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorHermite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Polynomial Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]

def tensorHermite (a : ι → ℕ) (x : ι → ℝ) : ℝ := ∏ i, (realHermite (a i)).eval (x i)
def tensorWeight (a : ι → ℕ) : ℝ := ∏ i, (a i).factorial
@[simp] theorem tensorHermite_zero [DecidableEq ι] (x : ι → ℝ) : tensorHermite (fun _ => 0) x = 1 := by
  simp [tensorHermite]
 def tensorHermiteSpan : Submodule ℝ ((ι → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range (tensorHermite (ι := ι)))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Polynomial Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 def tensorGradient (a : ι → ℕ) (i : ι) (x : ι → ℝ) : ℝ :=
  ∏ j, (if j=i then (realHermite (a j)).derivative else realHermite (a j)).eval (x j)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.OrthogonalExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory Finset
namespace FiniteEntropySeparation
variable {κ : Type u1} {Ω : Type u2} [MeasurableSpace Ω]
 def linearExpand (g : κ → Ω → ℝ) (a : κ →₀ ℝ) : Ω → ℝ := a.sum (fun k r => r • g k)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 def matrixOperator {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixPolynomialNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem trace_conjTranspose_mul_re (D : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.trace (D.conjTranspose*D)).re = ∑j,∑k,Complex.normSq (D j k) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,Complex.mul_re,Complex.star_def,
    Complex.conj_re,Complex.conj_im,neg_mul,sub_neg_eq_add,Complex.normSq_apply]
  exact sum_comm
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MicrostatesSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology
namespace FiniteEntropySeparation
 def matrixVolumeEntropy {n d : ℕ} (s : Set (MatrixCoordinates n d)) : EReal :=
  ((((d:ℝ)^2)⁻¹:ℝ):EReal)*(volume s).log+(((n:ℝ)/2*Real.log d:ℝ):EReal)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate NNReal
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
 def matrixBilinear {d : ℕ} (v w : EuclideanSpace ℂ (Fin d)) (A : Matrix (Fin d) (Fin d) ℂ) : ℂ := inner ℂ v (matrixOperator A w)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixSpectralMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
open scoped ComplexConjugate
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def matrixUnivariateMoment (q : Polynomial ℝ) (a : MatrixCoordinates n d) (i : Fin n) : ℝ :=
    ∑k∈q.support,q.coeff k*(matrixMoment a (List.replicate k i)).re
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralTestFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset Filter
open scoped Topology ComplexConjugate
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def univariateMoment (m : List (Fin n) → ℂ) (q : Polynomial ℝ) (i : Fin n) : ℝ :=
    ∑k∈q.support,q.coeff k*(m (List.replicate k i)).re
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SignalSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset

section Product
variable {α A : Type} [DecidableEq α] [Monoid A]
def optionTuple (B : α → A) (Y : A) : Option α → A
  | none => Y
  | some i => B i
end Product

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TotalSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset Filter Set
open scoped Topology
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def totalSecond (m : List (Fin n) → ℂ) : ℝ := ∑i : Fin n,(m [i,i]).re
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EntropyIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set
namespace FiniteEntropySeparation

def reciprocalDifference (a s : ℝ) : ℝ := 1 / (1+s) - 1 / (a+s)
def logarithmicPrimitive (a s : ℝ) : ℝ := Real.log (1+s) - Real.log (a+s)

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
namespace FiniteEntropySeparation
 def matrixBlocks {d p : ℕ} : (Fin p → Matrix (Fin d) (Fin d) ℂ) →+* Matrix (Fin (d*p)) (Fin (d*p)) ℂ :=
  (Matrix.reindexRingEquiv ℂ finProdFinEquiv).toRingHom.comp (Matrix.blockDiagonalRingHom (Fin d) (Fin p) ℂ)
end FiniteEntropySeparation

end

end OAI
end


