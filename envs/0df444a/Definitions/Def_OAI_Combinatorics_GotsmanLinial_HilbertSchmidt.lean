-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
-- name    : OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:07:03.504655+00:00
-- url     : https://prove2.me/theorems/6d9c3c91-0207-49ee-9497-814b94cd60f7
-- title:
--   Squared Hilbert–Schmidt norm of a complex matrix
-- statement:
--   For finite index sets $\iota$ and $\kappa$ and a complex matrix $A = (A_{ij})_{i\in\iota,\, j\in\kappa}$, the squared Hilbert–Schmidt (Frobenius) norm is the explicit entry sum
--   $$
--   \|A\|_{HS}^2 = \sum_{i\in\iota}\sum_{j\in\kappa} |A_{ij}|^2 ,
--   $$
--   corresponding to the counting inner product on both index sets; no matrix norm structure is involved. Writing $A^*$ for the conjugate transpose, the file records:
--
--   1. $\|0\|_{HS}^2 = 0$ and $\|A^*\|_{HS}^2 = \|A\|_{HS}^2$.
--   2. Trace formulas: $|z|^2 = \bar z z$ for $z \in \mathbb{C}$; for every column $j$, $\sum_i |A_{ij}|^2 = (A^*A)_{jj}$; hence $\|A\|_{HS}^2 = \operatorname{tr}(A^* A)$ as complex numbers, and in particular $\|A\|_{HS}^2 = \operatorname{Re}\operatorname{tr}(A^*A)$.
--   3. For a diagonal matrix, $\|\operatorname{diag}(d)\|_{HS}^2 = \sum_i |d_i|^2$; for the identity matrix on $\iota$, $\|I\|_{HS}^2 = |\iota|$; and more generally every square matrix $U$ with $U^*U = I$ has $\|U\|_{HS}^2 = |\iota|$.
--
--   This quantity is the energy functional of the matrix proof of the Gotsman–Linial bound: total energy of the centred grading, commutator and anticommutator energies, and block decompositions are all measured with it.
--
--   **Formalization Note** The definition is `hsNormSq A`, a real number. Besides the facts above, the file contains the plumbing lemma `ofReal_fintype_sum` (the complex embedding commutes with finite sums), used to move between the real-valued norm and complex traces.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/HilbertSchmidt.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/HilbertSchmidt.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GotsmanLinial mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements

namespace OAI

open scoped BigOperators ComplexConjugate

namespace LeanBlast.GotsmanLinial

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The Hilbert--Schmidt norm squared for the counting inner product.
This explicit entry sum does not use any norm instance on matrices. -/
noncomputable def hsNormSq (A : Matrix ι κ ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

@[simp] theorem hsNormSq_zero : hsNormSq (0 : Matrix ι κ ℂ) = 0 := by
  simp [hsNormSq]

@[simp] theorem hsNormSq_conjTranspose (A : Matrix ι κ ℂ) :
    hsNormSq A.conjTranspose = hsNormSq A := by
  simp only [hsNormSq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

theorem ofReal_sq_norm (z : ℂ) : (↑(‖z‖ ^ 2) : ℂ) = star z * z := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, Complex.star_def]

 theorem ofReal_fintype_sum (f : ι → ℝ) :
    (↑(∑ i, f i) : ℂ) = ∑ i, (f i : ℂ) :=
  map_sum Complex.ofRealHom f Finset.univ

omit [Fintype κ] in
theorem ofReal_sum_sq_norm_column (A : Matrix ι κ ℂ) (j : κ) :
    (↑(∑ i, ‖A i j‖ ^ 2) : ℂ) = (A.conjTranspose * A) j j := by
  rw [ofReal_fintype_sum]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_congr rfl fun i _ => ofReal_sq_norm _

theorem ofReal_hsNormSq (A : Matrix ι κ ℂ) :
    (hsNormSq A : ℂ) = Matrix.trace (A.conjTranspose * A) := by
  rw [hsNormSq, Finset.sum_comm]
  rw [ofReal_fintype_sum]
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.sum_congr rfl fun j _ => ofReal_sum_sq_norm_column A j

theorem hsNormSq_eq_re_trace (A : Matrix ι κ ℂ) :
    hsNormSq A = (Matrix.trace (A.conjTranspose * A)).re := by
  exact congrArg Complex.re (ofReal_hsNormSq A)

@[simp] theorem hsNormSq_diagonal [DecidableEq ι] (d : ι → ℂ) :
    hsNormSq (Matrix.diagonal d) = ∑ i, ‖d i‖ ^ 2 := by
  simp [hsNormSq, Matrix.diagonal_apply, apply_ite]

@[simp] theorem hsNormSq_one [DecidableEq ι] :
    hsNormSq (1 : Matrix ι ι ℂ) = Fintype.card ι := by
  rw [hsNormSq_eq_re_trace]
  simp

theorem hsNormSq_of_unitary [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U.conjTranspose * U = 1) : hsNormSq U = Fintype.card ι := by
  rw [hsNormSq_eq_re_trace, hU]
  simp

end LeanBlast.GotsmanLinial

end OAI


