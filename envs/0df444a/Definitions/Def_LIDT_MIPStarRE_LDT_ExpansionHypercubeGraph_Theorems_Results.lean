-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
-- name    : LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:45:06.845844+00:00
-- url     : https://prove2.me/theorems/418d5741-86cf-4d22-b043-723c1e2e8e8d
-- title:
--   LIDT definitions: LDT / ExpansionHypercubeGraph / Theorems / Results
-- statement:
--   This bundle connects the normalized $q$-ary hypercube graph to operator variance. It identifies independent-point averaging with product-uniform averaging, rewrites local and global variances in trace form, and proves the local-to-global factor-$m$ inequality used in the variance part of commutativity.
--
--   Principal definitions:
--   - `avgOver_independentPointPair_eq_uniform_prod`: The average over two independently uniform points equals the average under the uniform distribution on their product.
--   - `matrixLocalVariance_eq_closedForm`: Expresses matrix local variance as diagonal energy minus the weighted correlation over rerandomized-coordinate edges.
--   - `matrixLocalToGlobal`: Bounds matrix global variance by $m$ times matrix local variance.
--   - `localToGlobal`: For any operator family $A^u$ and state, global variance over two independent points is at most $m$ times the local variance over hypercube edges.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Results.lean#L32-L325

-- Generated from MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Results.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
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
# Section 7 hypercube graph: local-to-global variance theorems

This file assembles the public Section 7 results about the hypercube graph:
the Laplacian edge-difference formula, the local and global variance rewrites,
and the local-to-global inequality.  The proof route passes through the
matrix-realization theorems and then exposes the statements in the
`QuantumState` and operator-family language used elsewhere in the LDT
formalization.

## References

- `references/ldt-paper/expansion.tex`, especially `prop:laplacian-rewrite`,
  `lem:local-rewrite`, `lem:global-rewrite`, and `lem:local-to-global`
- `blueprint/src/chapter/ch05_expansion.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Averaging over two independently sampled hypercube points is the same as
averaging over the uniform distribution on the product of point types. -/
lemma avgOver_independentPointPair_eq_uniform_prod
    (params : Parameters) [FieldModel params.q]
    (f : Point params × Point params → Error) :
    avgOver (independentPointPair params) f =
      avgOver (uniformDistribution (Point params × Point params)) f := by
  rfl

private lemma matrixLocalVariance_eq_closedForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixLocalVariance params model =
      (hypercubeVertexCount params : Error)⁻¹ *
          ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) -
        ∑ u, ∑ v,
          rerandomizeCoordWeight params u v *
            ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
  let diag : Point params → Error :=
    fun u => ev (matrixModelState model) ((model.family u)ᴴ * model.family u)
  let corr : Point params → Point params → Error :=
    fun u v => ev (matrixModelState model) ((model.family v)ᴴ * model.family u)
  let w : Point params → Point params → Error := rerandomizeCoordWeight params
  have hsqdiff : ∀ u v,
      matrixSquaredDifferenceExpectation model.state (model.family u) (model.family v) =
        diag u + diag v - corr u v - corr u v := by
    intro u v
    simp [diag, corr, sqdiff_eq_corr, corr_symm]
  have hdiagLeft :
      ∑ u : Point params, ∑ v : Point params, w u v * diag u =
        (hypercubeVertexCount params : Error)⁻¹ * ∑ u : Point params, diag u := by
    calc
      ∑ u : Point params, ∑ v : Point params, w u v * diag u
        = ∑ u : Point params, (∑ v : Point params, w u v) * diag u := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            simpa using
              (Finset.sum_mul
                (s := (Finset.univ : Finset (Point params)))
                (f := fun v : Point params => w u v)
                (a := diag u)).symm
      _ = ∑ u : Point params, (hypercubeVertexCount params : Error)⁻¹ * diag u := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            simp [w, rerandomizeCoordWeight_rowSum]
      _ = (hypercubeVertexCount params : Error)⁻¹ * ∑ u : Point params, diag u := by
            simpa using
              (Finset.mul_sum
                (s := (Finset.univ : Finset (Point params)))
                (f := diag)
                (a := (hypercubeVertexCount params : Error)⁻¹)).symm
  have hdiagRight :
      ∑ u : Point params, ∑ v : Point params, w u v * diag v =
        (hypercubeVertexCount params : Error)⁻¹ * ∑ u : Point params, diag u := by
    calc
      ∑ u : Point params, ∑ v : Point params, w u v * diag v
        = ∑ v : Point params, ∑ u : Point params, w u v * diag v := by
            rw [Finset.sum_comm]
      _ = ∑ v : Point params, (∑ u : Point params, w u v) * diag v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa using
              (Finset.sum_mul
                (s := (Finset.univ : Finset (Point params)))
                (f := fun u : Point params => w u v)
                (a := diag v)).symm
      _ = ∑ v : Point params, (hypercubeVertexCount params : Error)⁻¹ * diag v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simp [w, rerandomizeCoordWeight_colSum]
      _ = (hypercubeVertexCount params : Error)⁻¹ * ∑ v : Point params, diag v := by
            simpa using
              (Finset.mul_sum
                (s := (Finset.univ : Finset (Point params)))
                (f := diag)
                (a := (hypercubeVertexCount params : Error)⁻¹)).symm
  unfold matrixLocalVariance matrixHypercubeEdgeDistribution
  rw [avgOver_rerandomizeCoord_eq_weight_sum]
  rw [Fintype.sum_prod_type]
  simp_rw [hsqdiff]
  let diagSum : Error := ∑ u, diag u
  let corrSum : Error := ∑ u, ∑ v, w u v * corr u v
  let diagLeft : Error := ∑ u : Point params, ∑ v : Point params, w u v * diag u
  let diagRight : Error := ∑ u : Point params, ∑ v : Point params, w u v * diag v
  have hsplit :
      ∑ u, ∑ v, w u v * (diag u + diag v - corr u v - corr u v) =
        diagLeft + diagRight - corrSum - corrSum := by
    unfold diagLeft diagRight corrSum
    calc
      ∑ u, ∑ v, w u v * (diag u + diag v - corr u v - corr u v)
          = ∑ u, ∑ v,
              (w u v * diag u +
                (w u v * diag v - w u v * corr u v - w u v * corr u v)) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              refine Finset.sum_congr rfl ?_
              intro v hv
              ring
      _ = ∑ u, ∑ v, w u v * diag u +
            ∑ u, ∑ v, (w u v * diag v - w u v * corr u v - w u v * corr u v) := by
              exact sum_sum_add
                (f := fun u v => w u v * diag u)
                (g := fun u v => w u v * diag v - w u v * corr u v - w u v * corr u v)
      _ = ∑ u, ∑ v, w u v * diag u +
            ((∑ u, ∑ v, w u v * diag v) - (∑ u, ∑ v, w u v * corr u v) -
              (∑ u, ∑ v, w u v * corr u v)) := by
              congr 1
              rw [sum_sum_sub, sum_sum_sub]
      _ = diagLeft + diagRight - corrSum - corrSum := by ring
  have hsum :
      ∑ u, ∑ v, w u v * (diag u + diag v - corr u v - corr u v) =
        2 * ((hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum) := by
    calc
      ∑ u, ∑ v, w u v * (diag u + diag v - corr u v - corr u v)
          = diagLeft + diagRight - corrSum - corrSum := hsplit
      _ = (hypercubeVertexCount params : Error)⁻¹ * diagSum +
            (hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum - corrSum := by
              rw [show diagLeft = (hypercubeVertexCount params : Error)⁻¹ * diagSum by
                    simpa [diagLeft, diagSum] using hdiagLeft]
              rw [show diagRight = (hypercubeVertexCount params : Error)⁻¹ * diagSum by
                    simpa [diagRight, diagSum] using hdiagRight]
      _ = 2 * ((hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum) := by ring
  rw [hsum]
  calc
    (1 / 2 : Error) * (2 * ((hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum))
      = (hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum := by ring
    _ =
        (hypercubeVertexCount params : Error)⁻¹ *
            ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) -
          ∑ u, ∑ v,
            rerandomizeCoordWeight params u v *
              ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
            simp [diagSum, corrSum, w, diag, corr]

private lemma matrixTraceForm_localToGlobal (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixGlobalVarianceTraceForm params model ≤
      (params.m : Error) * matrixLocalVarianceTraceForm params model := by
  have htensor :
      matrixTensorOperator (((hypercubeSpectralGap params : ℂ) •
          orthogonalModeProjectorMatrix params)) model.state.matrix ≤
        matrixTensorOperator (matrixLaplacianOperator params) model.state.matrix := by
    change Matrix.kronecker
        (((hypercubeSpectralGap params : ℂ) • orthogonalModeProjectorMatrix params))
        model.state.matrix ≤
      Matrix.kronecker (matrixLaplacianOperator params) model.state.matrix
    exact MIPStarRE.Quantum.kronecker_mono_left
      (hypercubeSpectralGap_operator params) model.state.positive
  have hwitness :
      ((hypercubeSpectralGap params : ℂ) • matrixGlobalVarianceTraceWitness params model) ≤
        matrixLocalVarianceTraceWitness params model := by
    have hraw :=
      MIPStarRE.LDT.ExpansionHypercubeGraph.conjTranspose_mul_mul_mono
        (matrixCombinedColumnOperator params model) htensor
    let c : ℂ := hypercubeSpectralGap params
    have hscale :
        (matrixCombinedColumnOperator params model)ᴴ *
            (matrixTensorOperator (c • orthogonalModeProjectorMatrix params) model.state.matrix *
              matrixCombinedColumnOperator params model) =
          c • matrixGlobalVarianceTraceWitness params model := by
      calc
        (matrixCombinedColumnOperator params model)ᴴ *
            (matrixTensorOperator (c • orthogonalModeProjectorMatrix params) model.state.matrix *
              matrixCombinedColumnOperator params model)
          = (matrixCombinedColumnOperator params model)ᴴ *
              (((c • matrixTensorOperator (orthogonalModeProjectorMatrix params)
                  model.state.matrix) *
                matrixCombinedColumnOperator params model)) := by
                  simp [matrixTensorOperator, Matrix.smul_kronecker]
                  rfl
        _ = c •
              ((matrixCombinedColumnOperator params model)ᴴ *
                (matrixTensorOperator (orthogonalModeProjectorMatrix params)
                  model.state.matrix *
                  matrixCombinedColumnOperator params model)) := by
                  simp
        _ = c • matrixGlobalVarianceTraceWitness params model := by
                  simp [matrixGlobalVarianceTraceWitness]
    change
      (matrixCombinedColumnOperator params model)ᴴ *
          (matrixTensorOperator (c • orthogonalModeProjectorMatrix params) model.state.matrix *
            matrixCombinedColumnOperator params model) ≤
        matrixLocalVarianceTraceWitness params model at hraw
    rw [hscale] at hraw
    simpa [c] using hraw
  have htrace :
      hypercubeSpectralGap params *
          Complex.re (MIPStarRE.Quantum.normalizedTrace
            (matrixGlobalVarianceTraceWitness params model)) ≤
        Complex.re (MIPStarRE.Quantum.normalizedTrace
          (matrixLocalVarianceTraceWitness params model)) := by
    have hmono := MIPStarRE.LDT.ExpansionHypercubeGraph.normalizedTrace_re_mono hwitness
    rw [MIPStarRE.Quantum.normalizedTrace_smul] at hmono
    simpa [Complex.mul_re] using hmono
  have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
  have hm_ne : (params.m : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hm)
  have hM_pos : 0 < hypercubeVertexCount params := by
    simp [hypercubeVertexCount, pow_pos params.hq]
  have hM_ne : (hypercubeVertexCount params : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hM_pos)
  have hgap_scale :
      (params.m : Error) * hypercubeSpectralGap params =
        (hypercubeVertexCount params : Error)⁻¹ := by
    unfold hypercubeSpectralGap
    field_simp [hm_ne, hM_ne]
  have hgap_scale' :
      1 / (hypercubeVertexCount params : Error) =
        (params.m : Error) * hypercubeSpectralGap params := by
    simpa [one_div] using hgap_scale.symm
  have hmul := mul_le_mul_of_nonneg_left htrace hm_nonneg
  calc
    matrixGlobalVarianceTraceForm params model
      = (params.m : Error) *
          (hypercubeSpectralGap params *
            Complex.re (MIPStarRE.Quantum.normalizedTrace
              (matrixGlobalVarianceTraceWitness params model))) := by
          rw [matrixGlobalVarianceTraceForm, hgap_scale']
          ring
    _ ≤ (params.m : Error) *
          Complex.re (MIPStarRE.Quantum.normalizedTrace
            (matrixLocalVarianceTraceWitness params model)) := hmul
    _ = (params.m : Error) * matrixLocalVarianceTraceForm params model := by
          simp [matrixLocalVarianceTraceForm]

/-- The concrete matrix-level counterpart of `lem:local-to-global`. -/
lemma matrixLocalToGlobal (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixGlobalVariance params model ≤
      (params.m : Error) * matrixLocalVariance params model := by
  calc
    matrixGlobalVariance params model = matrixGlobalVarianceTraceForm params model := by
      rw [matrixGlobalVariance_eq_closedForm, matrixGlobalVarianceTraceForm_eq_closedForm]
    _ ≤ (params.m : Error) * matrixLocalVarianceTraceForm params model :=
      matrixTraceForm_localToGlobal params model
    _ = (params.m : Error) * matrixLocalVariance params model := by
      rw [matrixLocalVariance_eq_closedForm, matrixLocalVarianceTraceForm_eq_closedForm]







/-! ## Public theorem wrappers -/





/-- General local-to-global inequality for an arbitrary operator family on a
finite-dimensional state space.

This is the abstract form behind `lem:local-to-global`: the global variance over
two independent vertices is bounded by `m` times the local variance over the
rerandomized-coordinate edge distribution. -/
lemma localToGlobal (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    globalVariance params A ψ ≤ (params.m : Error) * localVariance params A ψ := by
  by_cases hι : Nonempty ι
  · let := hι
    change matrixGlobalVariance params (abstractMatrixModel params A ψ) ≤
      (params.m : Error) * matrixLocalVariance params (abstractMatrixModel params A ψ)
    exact matrixLocalToGlobal params (abstractMatrixModel params A ψ)
  · rw [globalVariance_eq_zero_of_isEmpty hι params A ψ,
      localVariance_eq_zero_of_isEmpty hι params A ψ]
    positivity







end MIPStarRE.LDT.ExpansionHypercubeGraph

end

end LIDT


