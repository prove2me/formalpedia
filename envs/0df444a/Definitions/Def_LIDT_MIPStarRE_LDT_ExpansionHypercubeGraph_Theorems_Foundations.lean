-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
-- name    : LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:41:08.125423+00:00
-- url     : https://prove2.me/theorems/6f16b4ba-11df-4dd0-9f03-ab110e409529
-- title:
--   LIDT definitions: LDT / ExpansionHypercubeGraph / Theorems / Foundations
-- statement:
--   This bundle defines the abstract and matrix-facing statements for the hypercube variance rewrites. It packages local and global rewrite records, translates an abstract operator family into matrices, handles empty outcome types, and provides the sum identities and state conversion needed by the trace-form proof.
--
--   Principal definitions:
--   - `LocalRewriteStatement`: the abstract local-variance rewrite statement.
--   - `GlobalRewriteStatement`: the abstract global-variance rewrite statement.
--   - `abstractMatrixModel`: the matrix realization of an abstract operator family and state.
--   - `localVariance_eq_zero_of_isEmpty`: vanishing of local variance for an empty outcome type.
--   - `globalVariance_eq_zero_of_isEmpty`: vanishing of global variance for an empty outcome type.
--   - `sum_sum_mul_left`: factors a common scalar from a double sum.
--   - `sum_sum_add`: distributes a double sum over pointwise addition.
--   - `matrixModelState`: converts a matrix realization state to an abstract quantum state.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Foundations.lean#L36-L256

-- Generated from MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Foundations.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

/-!
# Section 7 hypercube graph: trace-form foundations

This file provides the abstract theorem statements and trace-form identities
used to formalize the local and global variance rewrites in Section 7 of the LDT
paper.  The concrete matrix-realization statements are proved first; the
public-facing statements in `MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Results`
then specialize these identities to arbitrary finite-dimensional operator
families.

## References

- `references/ldt-paper/expansion.tex`, especially `lem:local-rewrite` and
  `lem:global-rewrite`
- `blueprint/src/chapter/ch05_expansion.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-! ## Statement structures and matrix realization -/

/-- Paper origin: `references/ldt-paper/expansion.tex:145-178`
(`\label{lem:local-rewrite}`).

Conclusion statement for `lem:local-rewrite`: the local variance is rewritten as a
trace-form expectation in the operator family `A`. -/
structure LocalRewriteStatement (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Prop where
  /-- The local variance agrees with the trace form built from the Laplacian. -/
  traceFormula :
    localVariance params A ψ = localVarianceTraceForm params A ψ

/-- Paper origin: `references/ldt-paper/expansion.tex:179-269`
(`\label{lem:global-rewrite}`).

Conclusion statement for `lem:global-rewrite`: the global variance is rewritten as a
trace-form expectation along the eigenbasis of the hypercube graph
Laplacian. -/
structure GlobalRewriteStatement (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Prop where
  /-- A Fourier-mode decomposition whose trace form recovers the global variance. -/
  decomposition :
    ∃ decomp : GlobalVarianceDecomposition params A,
      globalVariance params A ψ = globalVarianceTraceForm params A ψ decomp

/-- Reinterpret an abstract operator family and quantum state as the concrete
matrix realization used by the trace-form proof of Section 7. -/
def abstractMatrixModel (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) [Nonempty ι] :
    MatrixOperatorFamilyRealization params where
  space :=
    { carrier := ι
      instFintype := inferInstance
      instDecidableEq := inferInstance
      instNonempty := inferInstance }
  state :=
    { matrix := ψ.density
      positive := ψ.density_psd }
  family := A

/-- If the ambient outcome type is empty, the abstract local variance is zero. -/
lemma localVariance_eq_zero_of_isEmpty (hι : ¬ Nonempty ι) (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    localVariance params A ψ = 0 := by
  have : IsEmpty ι := not_nonempty_iff.mp hι
  have hzero : ∀ uv : Point params × Point params,
      ev ψ (pointDifferenceSquaredOperator A uv.1 uv.2) = 0 := by
    intro uv
    simp [pointDifferenceSquaredOperator, ev, MIPStarRE.Quantum.normalizedTrace]
  unfold localVariance
  rw [avgOver_congr _ _ (fun _ => 0) hzero, avgOver_zero]
  ring

/-- If the ambient outcome type is empty, the abstract global variance is zero. -/
lemma globalVariance_eq_zero_of_isEmpty (hι : ¬ Nonempty ι) (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    globalVariance params A ψ = 0 := by
  have : IsEmpty ι := not_nonempty_iff.mp hι
  have hzero : ∀ uv : Point params × Point params,
      ev ψ (pointDifferenceSquaredOperator A uv.1 uv.2) = 0 := by
    intro uv
    simp [pointDifferenceSquaredOperator, ev, MIPStarRE.Quantum.normalizedTrace]
  unfold globalVariance
  rw [avgOver_congr _ _ (fun _ => 0) hzero, avgOver_zero]
  ring





/-! ## Finite-sum helper lemmas -/



/-- Factor a common scalar out of a doubly indexed finite sum. -/
lemma sum_sum_mul_left {α β γ : Type*}
    [Fintype α] [Fintype β] [CommSemiring γ] (c : γ) (f : α → β → γ) :
    ∑ a, ∑ b, c * f a b = c * ∑ a, ∑ b, f a b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [Finset.mul_sum]

/-- Distribute a doubly indexed sum across pointwise addition. -/
lemma sum_sum_add {α β γ : Type*}
    [Fintype α] [Fintype β] [AddCommMonoid γ] (f g : α → β → γ) :
    ∑ a, ∑ b, (f a b + g a b) = (∑ a, ∑ b, f a b) + ∑ a, ∑ b, g a b := by
  calc
    ∑ a, ∑ b, (f a b + g a b) = ∑ a, ((∑ b, f a b) + ∑ b, g a b) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [Finset.sum_add_distrib]
    _ = (∑ a, ∑ b, f a b) + ∑ a, ∑ b, g a b := by
      rw [Finset.sum_add_distrib]

/-- Distribute a doubly indexed sum across pointwise subtraction. -/
lemma sum_sum_sub {α β γ : Type*}
    [Fintype α] [Fintype β] [AddCommGroup γ] (f g : α → β → γ) :
    ∑ a, ∑ b, (f a b - g a b) = (∑ a, ∑ b, f a b) - ∑ a, ∑ b, g a b := by
  calc
    ∑ a, ∑ b, (f a b - g a b) = ∑ a, ∑ b, (f a b + (-g a b)) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      refine Finset.sum_congr rfl ?_
      intro b hb
      rw [sub_eq_add_neg]
    _ = (∑ a, ∑ b, f a b) + ∑ a, ∑ b, (-g a b) := by
      exact sum_sum_add (f := f) (g := fun a b => -g a b)
    _ = (∑ a, ∑ b, f a b) - ∑ a, ∑ b, g a b := by
      simp [sub_eq_add_neg]

/-! ## Trace witness closed forms -/

/-- Turn a matrix realization state into the corresponding abstract quantum state. -/
def matrixModelState {params : Parameters}
    (model : MatrixOperatorFamilyRealization params) : QuantumState model.space.carrier where
  density := model.state.matrix
  density_psd := model.state.positive

private lemma trace_combined_tensor_eq (params : Parameters)
    (model : MatrixOperatorFamilyRealization params)
    (P : MatrixOperator (pointHilbertSpace params)) :
    (((matrixCombinedOperator params model)ᴴ *
        (matrixTensorOperator P model.state.matrix * matrixCombinedOperator params model)).trace) =
      ∑ u, ∑ v,
        P u v * (model.state.matrix * ((model.family v)ᴴ * model.family u)).trace := by
  rw [Matrix.trace_mul_comm]
  suffices
      ∑ a : (tensorHilbertSpace (pointHilbertSpace params) model.space).carrier,
        ∑ b : model.space.carrier,
        ((matrixTensorOperator P model.state.matrix *
          matrixCombinedOperator params model) a b) *
          model.family a.1 b a.2 =
        ∑ u, ∑ v, P u v *
          ∑ i, (model.state.matrix * ((model.family v)ᴴ * model.family u)).diag i by
    simpa [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      matrixCombinedOperator, mul_assoc] using this
  let f : (Point params × model.space.carrier) → model.space.carrier →
      (Point params × model.space.carrier) → ℂ :=
    fun x i z => P x.1 z.1 * model.state.matrix x.2 z.2 *
      (starRingEnd ℂ) (model.family z.1 i z.2)
  let g : (Point params × model.space.carrier) → model.space.carrier → ℂ :=
    fun x i => model.family x.1 i x.2
  change ∑ a, ∑ b, (∑ c, f a b c) * g a b = _
  simp_rw [Finset.sum_mul]
  simp_rw [f, g, Fintype.sum_prod_type, Finset.mul_sum]
  conv =>
    rhs
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, mul_assoc]
  refine Finset.sum_congr rfl ?_
  intro x hx
  calc
    ∑ x₁, ∑ x₂, ∑ x₃, ∑ x₄,
        P x x₃ * model.state.matrix x₁ x₄ *
          (starRingEnd ℂ) (model.family x₃ x₂ x₄) * model.family x x₂ x₁
      = ∑ x₁, ∑ x₃, ∑ x₂, ∑ x₄,
          P x x₃ * model.state.matrix x₁ x₄ *
            (starRingEnd ℂ) (model.family x₃ x₂ x₄) * model.family x x₂ x₁ := by
          refine Finset.sum_congr rfl ?_
          intro x₁ _
          rw [Finset.sum_comm]
    _ = ∑ x₃, ∑ x₁, ∑ x₂, ∑ x₄,
          P x x₃ * model.state.matrix x₁ x₄ *
            (starRingEnd ℂ) (model.family x₃ x₂ x₄) * model.family x x₂ x₁ := by
          rw [Finset.sum_comm]
    _ = ∑ x₃, ∑ x₁, ∑ x₄, ∑ x₂,
          P x x₃ * model.state.matrix x₁ x₄ *
            (starRingEnd ℂ) (model.family x₃ x₂ x₄) * model.family x x₂ x₁ := by
          refine Finset.sum_congr rfl ?_
          intro x₃ _
          refine Finset.sum_congr rfl ?_
          intro x₁ _
          rw [Finset.sum_comm]
    _ = ∑ x₁, ∑ x₂, ∑ x₃, ∑ i,
          P x x₁ *
            (model.state.matrix x₂ x₃ *
              ((starRingEnd ℂ) (model.family x₁ i x₃) * model.family x i x₂)) := by
          simp [mul_assoc, mul_left_comm, mul_comm]

/-- Expand the normalized trace of the combined tensor witness into its explicit
double-sum form. -/
lemma normalizedTrace_combined_tensor_eq (params : Parameters)
    (model : MatrixOperatorFamilyRealization params)
    (P : MatrixOperator (pointHilbertSpace params)) :
    MIPStarRE.Quantum.normalizedTrace
      ((matrixCombinedOperator params model)ᴴ *
        (matrixTensorOperator P model.state.matrix * matrixCombinedOperator params model)) =
      ∑ u, ∑ v,
        P u v * matrixExpectation model.state ((model.family v)ᴴ * model.family u) := by
  unfold MIPStarRE.Quantum.normalizedTrace matrixExpectation
  rw [trace_combined_tensor_eq]
  simp_rw [div_eq_mul_inv]
  simp [MIPStarRE.Quantum.normalizedTrace, Finset.sum_mul, div_eq_mul_inv, mul_assoc]





end MIPStarRE.LDT.ExpansionHypercubeGraph

end

end LIDT


