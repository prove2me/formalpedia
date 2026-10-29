-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
-- name    : LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:38:19.313754+00:00
-- url     : https://prove2.me/theorems/a141f3ea-f06f-470a-93cd-0dcd9f26660b
-- title:
--   LIDT definitions: LDT / ExpansionHypercubeGraph / MatrixRealization / TraceForms
-- statement:
--   This bundle defines the trace-form realization of local and global variance. It packages the normalized quadratic difference, edge and independent-point variances, combined column operators, and the matrix statements and witnesses that implement the paper's variance rewrites.
--
--   Principal definitions:
--   - `matrixSquaredDifferenceExpectation`: the normalized trace quadratic form for an operator difference.
--   - `matrixLocalVariance`: the edge-averaged local variance.
--   - `matrixGlobalVariance`: the independent-point global variance.
--   - `matrixCombinedOperator`: the combined operator used in the trace identities.
--   - `matrixCombinedColumnOperator`: the column-operator bridge for the witnesses.
--   - `matrixLocalVarianceTraceWitness`: the matrix local-variance trace witness.
--   - `MatrixLocalRewriteStatement`: the matrix local rewrite statement.
--   - `MatrixGlobalRewriteStatement`: the matrix global rewrite statement.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/ExpansionHypercubeGraph/MatrixRealization/TraceForms.lean#L26-L147

-- Generated from MIPStarRE/LDT/ExpansionHypercubeGraph/MatrixRealization/TraceForms.lean by skeleton subtraction.
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
# Section 7 — Matrix variance trace forms

This file contains the matrix-level variance quantities and trace-form rewrite
statements used after the Fourier spectral-gap material in `MatrixRealization.Core`.

## References

- `blueprint/src/chapter/ch05_expansion.tex`
- `references/ldt-paper/expansion.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

/-- The quadratic form `τ(ρ (X-Y)^*(X-Y))`. -/
noncomputable def matrixSquaredDifferenceExpectation {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H) (X Y : MatrixOperator H) : Error :=
  Complex.re (matrixExpectation ρ (((X - Y)ᴴ) * (X - Y)))

/-- The actual local variance, averaged over the hypercube edge set.
This matches the Section 7.1 rerandomization distribution on ordered edges. -/
noncomputable def matrixLocalVariance (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  (1 / (2 : Error)) *
    avgOver (matrixHypercubeEdgeDistribution params) (fun uv =>
      matrixSquaredDifferenceExpectation model.state
        (model.family uv.1) (model.family uv.2))

/-- The actual global variance, averaged over two independent points. -/
noncomputable def matrixGlobalVariance (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  (1 / (2 : Error)) *
    avgOver (independentPointPair params) (fun uv =>
      matrixSquaredDifferenceExpectation model.state
        (model.family uv.1) (model.family uv.2))

/-- The matrix-level combined column operator used for the trace rewrites.
Its `u`-th block is `(A^u)ᴴ`, so that the trace witnesses match the
quadratic forms `τ(ρ · (A^u - A^v)ᴴ (A^u - A^v))` for arbitrary families. -/
noncomputable def matrixCombinedOperator (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    RectangularMatrixOperator model.space
      (tensorHilbertSpace (pointHilbertSpace params) model.space) :=
  fun ui j => star (model.family ui.1 j ui.2)

/-- Bridge for the column-operator view used in the quadratic-form witnesses. -/
noncomputable def matrixCombinedColumnOperator (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    RectangularMatrixOperator model.space
      (tensorHilbertSpace (pointHilbertSpace params) model.space) :=
  matrixCombinedOperator params model

/-- Paper origin: `references/ldt-paper/expansion.tex:145-154`
(`\label{lem:local-rewrite}`); trace witness for the local-variance
rewrite, matrix realization. -/
noncomputable def matrixLocalVarianceTraceWitness (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixOperator model.space :=
  (matrixCombinedColumnOperator params model)ᴴ *
    (matrixTensorOperator (matrixLaplacianOperator params) model.state.matrix *
      matrixCombinedColumnOperator params model)

/-- The actual trace form for the local variance. -/
noncomputable def matrixLocalVarianceTraceForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  Complex.re (MIPStarRE.Quantum.normalizedTrace (matrixLocalVarianceTraceWitness params model))

/-- Paper origin: `references/ldt-paper/expansion.tex:179-190`
(`\label{lem:global-rewrite}`); trace witness for the global-variance
rewrite, matrix realization. -/
noncomputable def matrixGlobalVarianceTraceWitness (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixOperator model.space :=
  (matrixCombinedColumnOperator params model)ᴴ *
    (matrixTensorOperator (orthogonalModeProjectorMatrix params) model.state.matrix *
      matrixCombinedColumnOperator params model)

/-- The actual trace form for the global variance.

The `1 / hypercubeVertexCount` factor (= `1 / M` where `M = q^m`) matches the paper's
`lem:global-rewrite`: the global variance equals
  `(1/M) · Tr(⟨φ⊥| ⊗ A⊥ · (I ⊗ |ψ⟩⟨ψ|) · |φ⊥⟩ ⊗ A⊥)`,
which in turn equals `(1/2) · E_{u,v} ⟨ψ| (Aᵘ − Aᵛ)² ⊗ I |ψ⟩`. -/
noncomputable def matrixGlobalVarianceTraceForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  (1 / (hypercubeVertexCount params : Error)) *
    Complex.re (MIPStarRE.Quantum.normalizedTrace
      (matrixGlobalVarianceTraceWitness params model))

/-- Adjoint sandwiching is monotone in the middle factor. -/
lemma conjTranspose_mul_mul_mono {H K : FiniteHilbertSpace}
    (M : RectangularMatrixOperator H K) {A B : MatrixOperator K} (hAB : A ≤ B) :
    Mᴴ * (A * M) ≤ Mᴴ * (B * M) := by
  have hpsd : 0 ≤ Mᴴ * (B - A) * M := by
    exact
      (Matrix.PosSemidef.conjTranspose_mul_mul_same
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hAB)) M).nonneg
  have hrewrite : Mᴴ * (B - A) * M = Mᴴ * (B * M) - Mᴴ * (A * M) := by
    ext i j
    conv =>
      lhs
      simp [Matrix.mul_apply, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.mul_sum, sub_eq_add_neg, mul_add, add_mul]
    conv =>
      rhs
      simp [Matrix.mul_apply, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.mul_sum, sub_eq_add_neg, mul_add, add_mul]
    congr 1 <;> (rw [Finset.sum_comm]; simp [mul_assoc])
  rw [hrewrite] at hpsd
  exact sub_nonneg.mp hpsd

/-- Monotonicity of `Re τ` with respect to the matrix order. -/
lemma normalizedTrace_re_mono {H : FiniteHilbertSpace}
    {A B : MatrixOperator H} (hAB : A ≤ B) :
    Complex.re (MIPStarRE.Quantum.normalizedTrace A) ≤
      Complex.re (MIPStarRE.Quantum.normalizedTrace B) := by
  let ψ : QuantumState H.carrier := { density := 1 }
  simpa [ψ, ev] using (ev_mono ψ A B hAB)

/-- Paper origin: `references/ldt-paper/expansion.tex:145-178`
(`\label{lem:local-rewrite}`); matrix realization of `LocalRewriteStatement`.

Matrix-level rewrite identity for the local variance. -/
structure MatrixLocalRewriteStatement (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Prop where
  traceFormula :
    matrixLocalVariance params model = matrixLocalVarianceTraceForm params model

/-- Paper origin: `references/ldt-paper/expansion.tex:179-269`
(`\label{lem:global-rewrite}`); matrix realization of `GlobalRewriteStatement`.

Matrix-level rewrite identity for the global variance. -/
structure MatrixGlobalRewriteStatement (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Prop where
  traceFormula :
    matrixGlobalVariance params model = matrixGlobalVarianceTraceForm params model

end MIPStarRE.LDT.ExpansionHypercubeGraph

end

end LIDT


