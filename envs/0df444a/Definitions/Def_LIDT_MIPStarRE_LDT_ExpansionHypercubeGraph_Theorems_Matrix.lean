-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
-- name    : LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:43:44.561721+00:00
-- url     : https://prove2.me/theorems/a6fa65c1-1f45-4e7d-93ef-21a490a7d2d0
-- title:
--   LIDT definitions: LDT / ExpansionHypercubeGraph / Theorems / Matrix
-- statement:
--   This bundle proves the main closed-form identities for the matrix hypercube variance model. It establishes symmetry of the correlation term, expands squared differences, verifies edge-weight row and column sums, and identifies closed forms for local and global variance trace expressions.
--
--   Principal definitions:
--   - `corr_symm`: symmetry of the matrix correlation term under point exchange.
--   - `sqdiff_eq_corr`: the diagonal and correlation expansion of squared difference.
--   - `orthogonalModeProjector_re_sum`: the real-part sum identity for the orthogonal-mode projector.
--   - `matrixGlobalVarianceTraceForm_eq_closedForm`: the closed global-variance trace form.
--   - `matrixGlobalVariance_eq_closedForm`: the closed matrix global variance.
--   - `rerandomizeCoordWeight_rowSum`: the row sum of rerandomized-edge weights.
--   - `rerandomizeCoordWeight_colSum`: the column sum of rerandomized-edge weights.
--   - `matrixLocalVarianceTraceForm_eq_closedForm`: the closed local-variance trace form.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Matrix.lean#L28-L769

-- Generated from MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Matrix.lean by skeleton subtraction.
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
# Section 7 hypercube graph: matrix-realization theorems

Translating the squared-difference expectation of the hypercube graph
operators into the `ev`-based inner-product language of the matrix
realization model.

## References

- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch05_expansion.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix correlation term is symmetric under swapping the two points. -/
lemma corr_symm (params : Parameters) (model : MatrixOperatorFamilyRealization params)
    (u v : Point params) :
    ev (matrixModelState model) ((model.family v)ᴴ * model.family u) =
      ev (matrixModelState model) ((model.family u)ᴴ * model.family v) := by
  simpa [matrixModelState] using
    (ev_conjTranspose (ψ := matrixModelState model) (((model.family v)ᴴ) * model.family u)).symm

/-- Expand the matrix squared-difference expectation into diagonal and correlation terms. -/
lemma sqdiff_eq_corr (params : Parameters) (model : MatrixOperatorFamilyRealization params)
    (u v : Point params) :
    matrixSquaredDifferenceExpectation model.state (model.family u) (model.family v) =
      ev (matrixModelState model) ((model.family u)ᴴ * model.family u) +
        ev (matrixModelState model) ((model.family v)ᴴ * model.family v) -
        ev (matrixModelState model) ((model.family u)ᴴ * model.family v) -
        ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
  change ev (matrixModelState model)
      (((model.family u - model.family v)ᴴ) * (model.family u - model.family v)) = _
  have hexpand :
      (((model.family u - model.family v)ᴴ) * (model.family u - model.family v)) =
        (model.family u)ᴴ * model.family u + (model.family v)ᴴ * model.family v -
          (model.family u)ᴴ * model.family v - (model.family v)ᴴ * model.family u := by
    simp [mul_add, add_mul, sub_eq_add_neg]
    abel
  rw [hexpand, ev_sub, ev_sub, ev_add]

private lemma orthogonalModeProjector_re_sum (params : Parameters)
    (z : Point params → Point params → ℂ) :
    Complex.re (∑ u, ∑ v, orthogonalModeProjectorMatrix params u v * z u v) =
      ∑ u, Complex.re (z u u) -
        (hypercubeVertexCount params : Error)⁻¹ * ∑ u, ∑ v, Complex.re (z u v) := by
  have hdiag :
      ∑ u, ∑ v, Complex.re (((if u = v then (1 : ℂ) else 0) * z u v)) =
        ∑ u, Complex.re (z u u) := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    calc
      ∑ v, Complex.re (((if u = v then (1 : ℂ) else 0) * z u v))
        = ∑ v, if u = v then Complex.re (z u v) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            by_cases huv : u = v <;> simp [huv]
        _ = Complex.re (z u u) := by
              rw [Finset.sum_ite_eq]
              simp
  have hconst :
      ∑ u, ∑ v, Complex.re (((hypercubeVertexCount params : ℂ)⁻¹ * z u v)) =
        (hypercubeVertexCount params : Error)⁻¹ * ∑ u, ∑ v, Complex.re (z u v) := by
    calc
      ∑ u, ∑ v, Complex.re (((hypercubeVertexCount params : ℂ)⁻¹ * z u v))
        = ∑ u, ∑ v, (hypercubeVertexCount params : Error)⁻¹ * Complex.re (z u v) := by
            simp [Complex.mul_re]
      _ = (hypercubeVertexCount params : Error)⁻¹ * ∑ u, ∑ v, Complex.re (z u v) := by
            exact sum_sum_mul_left (c := (hypercubeVertexCount params : Error)⁻¹)
              (f := fun u v => Complex.re (z u v))
  calc
    Complex.re (∑ u, ∑ v, orthogonalModeProjectorMatrix params u v * z u v)
      = ∑ u, ∑ v, Complex.re (orthogonalModeProjectorMatrix params u v * z u v) := by
          simp
    _ = ∑ u, ∑ v,
          (Complex.re (((if u = v then (1 : ℂ) else 0) * z u v)) -
            Complex.re (((hypercubeVertexCount params : ℂ)⁻¹ * z u v))) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          refine Finset.sum_congr rfl ?_
          intro v hv
          simp [orthogonalModeProjectorMatrix, constantModeProjectorMatrix, Matrix.one_apply,
            sub_mul]
    _ = ∑ u, ∑ v, Complex.re (((if u = v then (1 : ℂ) else 0) * z u v)) -
          ∑ u, ∑ v, Complex.re (((hypercubeVertexCount params : ℂ)⁻¹ * z u v)) := by
          simp_rw [Finset.sum_sub_distrib]
    _ = ∑ u, Complex.re (z u u) -
          (hypercubeVertexCount params : Error)⁻¹ * ∑ u, ∑ v, Complex.re (z u v) := by
          rw [hdiag, hconst]

/-- Closed form for the matrix global-variance trace expression. -/
lemma matrixGlobalVarianceTraceForm_eq_closedForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixGlobalVarianceTraceForm params model =
      (hypercubeVertexCount params : Error)⁻¹ *
          ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) -
        (hypercubeVertexCount params : Error)⁻¹ *
          (hypercubeVertexCount params : Error)⁻¹ *
            ∑ u, ∑ v, ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
  unfold matrixGlobalVarianceTraceForm matrixGlobalVarianceTraceWitness
    matrixCombinedColumnOperator
  rw [normalizedTrace_combined_tensor_eq]
  rw [orthogonalModeProjector_re_sum]
  simp [matrixExpectation, ev, matrixModelState]
  ring

/-- Closed form for the matrix global variance. -/
lemma matrixGlobalVariance_eq_closedForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixGlobalVariance params model =
      (hypercubeVertexCount params : Error)⁻¹ *
          ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) -
        (hypercubeVertexCount params : Error)⁻¹ *
          (hypercubeVertexCount params : Error)⁻¹ *
            ∑ u, ∑ v, ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
  let diag : Point params → Error :=
    fun u => ev (matrixModelState model) ((model.family u)ᴴ * model.family u)
  let corr : Point params → Point params → Error :=
    fun u v => ev (matrixModelState model) ((model.family v)ᴴ * model.family u)
  have hsqdiff : ∀ u v,
      matrixSquaredDifferenceExpectation model.state (model.family u) (model.family v) =
        diag u + diag v - corr u v - corr u v := by
    intro u v
    simp [diag, corr, sqdiff_eq_corr, corr_symm]
  have hdiag_left :
      ∑ u : Point params, ∑ v : Point params, diag u =
        (hypercubeVertexCount params : Error) * ∑ u : Point params, diag u := by
    calc
      ∑ u : Point params, ∑ v : Point params, diag u =
          ∑ u : Point params, (Fintype.card (Point params) : Error) * diag u := by
            simp
      _ = (Fintype.card (Point params) : Error) * ∑ u : Point params, diag u := by
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset (Point params)))
                (f := diag) (a := (Fintype.card (Point params) : Error))).symm
      _ = (hypercubeVertexCount params : Error) * ∑ u : Point params, diag u := by
            simp [hypercubeVertexCount]
  have hdiag_right :
      ∑ u : Point params, ∑ v : Point params, diag v =
        (hypercubeVertexCount params : Error) * ∑ u : Point params, diag u := by
    calc
      ∑ u : Point params, ∑ v : Point params, diag v =
          ∑ v : Point params, ∑ u : Point params, diag v := by
            rw [Finset.sum_comm]
      _ = (hypercubeVertexCount params : Error) * ∑ u : Point params, diag u := by
            simpa [diag] using hdiag_left
  have hM_ne : (hypercubeVertexCount params : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (pow_pos params.hq params.m))
  unfold matrixGlobalVariance avgOver independentPointPair uniformDistribution
  rw [Distribution.uniformOnFinset_support]
  simp_rw [Distribution.uniformOnFinset_weight]
  simp only [Finset.mem_univ, ite_true]
  rw [Fintype.sum_prod_type]
  simp_rw [hsqdiff]
  let M : Error := hypercubeVertexCount params
  have huniformWeight :
      (1 / (((Finset.univ : Finset (Point params × Point params)).card : Error))) =
        M⁻¹ * M⁻¹ := by
    have hcard :
        (((Finset.univ : Finset (Point params × Point params)).card : Error)) = M * M := by
      rw [Finset.card_univ, Fintype.card_prod]
      simp [M, hypercubeVertexCount]
    rw [hcard]
    field_simp [M, hM_ne]
  simp_rw [huniformWeight]
  let diagSum : Error := ∑ u, diag u
  let corrSum : Error := ∑ u, ∑ v, corr u v
  let diagLeft : Error := ∑ u : Point params, ∑ v : Point params, diag u
  let diagRight : Error := ∑ u : Point params, ∑ v : Point params, diag v
  have hfactor :
      ∑ u, ∑ v, (M⁻¹ * M⁻¹) * (diag u + diag v - corr u v - corr u v) =
        (M⁻¹ * M⁻¹) * ∑ u, ∑ v, (diag u + diag v - corr u v - corr u v) := by
    simpa [M, mul_comm, mul_left_comm, mul_assoc] using
      (sum_sum_mul_left
        (c := M⁻¹ * M⁻¹)
        (f := fun u v => diag u + diag v - corr u v - corr u v))
  rw [hfactor]
  have hdiagLeft : diagLeft = M * diagSum := by
    simpa [M, diagLeft, diagSum] using hdiag_left
  have hdiagRight : diagRight = M * diagSum := by
    simpa [M, diagRight, diagSum, diag] using hdiag_right
  have hsplit :
      ∑ u, ∑ v, (diag u + diag v - corr u v - corr u v) =
        diagLeft + diagRight - corrSum - corrSum := by
    unfold diagLeft diagRight corrSum
    calc
      ∑ u, ∑ v, (diag u + diag v - corr u v - corr u v)
          = ∑ u, ∑ v, (diag u + (diag v - corr u v - corr u v)) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              refine Finset.sum_congr rfl ?_
              intro v hv
              ring
      _ = ∑ u, ∑ v, diag u + ∑ u, ∑ v, (diag v - corr u v - corr u v) := by
              exact
                sum_sum_add
                  (f := fun u v => diag u)
                  (g := fun u v => diag v - corr u v - corr u v)
      _ = ∑ u, ∑ v, diag u + ((∑ u, ∑ v, diag v) - (∑ u, ∑ v, corr u v) -
              (∑ u, ∑ v, corr u v)) := by
              congr 1
              rw [sum_sum_sub, sum_sum_sub]
      _ = diagLeft + diagRight - corrSum - corrSum := by ring
  have hsum :
      ∑ u, ∑ v, (diag u + diag v - corr u v - corr u v) = 2 * (M * diagSum - corrSum) := by
    calc
      ∑ u, ∑ v, (diag u + diag v - corr u v - corr u v)
          = diagLeft + diagRight - corrSum - corrSum := hsplit
      _ = M * diagSum + M * diagSum - corrSum - corrSum := by rw [hdiagLeft, hdiagRight]
      _ = 2 * (M * diagSum - corrSum) := by ring
  rw [hsum]
  have hfinal :
      (1 / 2 : Error) * (M⁻¹ * M⁻¹) * (2 * (M * diagSum - corrSum)) =
        M⁻¹ * diagSum - M⁻¹ * M⁻¹ * corrSum := by
    field_simp [M, hM_ne]
  simpa [M, diagSum, corrSum, mul_assoc] using hfinal

/-- The rerandomized-edge weight sums to the uniform point weight across each source row. -/
lemma rerandomizeCoordWeight_rowSum (params : Parameters) (u : Point params) :
    ∑ v, rerandomizeCoordWeight params u v = (hypercubeVertexCount params : Error)⁻¹ := by
  have hcount :
      (∑ v : Point params,
        ∑ p : Fin params.m × Fq params,
          if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) = params.m * params.q := by
    rw [Finset.sum_comm]
    simp [Fintype.card_fin]
  have hcount_cast :
      (∑ v : Point params,
        (((∑ p : Fin params.m × Fq params,
            if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) : ℕ) : Error)) =
          (params.m * params.q : Error) := by
    simpa using congrArg (fun n : ℕ => (n : Error)) hcount
  have hM_ne : (hypercubeVertexCount params : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (pow_pos params.hq _))
  have hm_ne : (params.m : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hm)
  have hq_ne : (params.q : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hq)
  unfold rerandomizeCoordWeight
  simp_rw [div_eq_mul_inv]
  calc
    ∑ v : Point params,
        ↑(∑ p : Fin params.m × Fq params,
            if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) *
          (↑(hypercubeVertexCount params * params.m * params.q) : Error)⁻¹
      = (∑ v : Point params,
          ↑(∑ p : Fin params.m × Fq params,
              if Function.update u p.1 p.2 = v then (1 : ℕ) else 0)) *
            (↑(hypercubeVertexCount params * params.m * params.q) : Error)⁻¹ := by
          simpa using
            (Finset.sum_mul
              (s := (Finset.univ : Finset (Point params)))
              (f := fun v : Point params =>
                ↑(∑ p : Fin params.m × Fq params,
                    if Function.update u p.1 p.2 = v then (1 : ℕ) else 0))
              (a := (↑(hypercubeVertexCount params * params.m * params.q) : Error)⁻¹)).symm
    _ = (hypercubeVertexCount params : Error)⁻¹ := by
          rw [hcount_cast]
          field_simp [hM_ne, hm_ne, hq_ne]
          rw [Nat.cast_mul, Nat.cast_mul]
          ring

private lemma update_eq_fixed_count (params : Parameters)
    (i : Fin params.m) (x : Fq params) (v : Point params) :
    (∑ u : Point params, if Function.update u i x = v then (1 : ℕ) else 0) =
      if x = v i then params.q else 0 := by
  classical
  by_cases hx : x = v i
  · let toFun : {u : Point params // Function.update u i x = v} → Fq params :=
      fun u => u.1 i
    let invFun : Fq params → {u : Point params // Function.update u i x = v} := fun a =>
      ⟨Function.update v i a, by
        ext j
        by_cases hji : j = i
        · subst hji
          simp [Function.update, hx]
        · simp [Function.update, hji]⟩
    have hleft : Function.LeftInverse invFun toFun := by
      intro u
      apply Subtype.ext
      ext j
      by_cases hji : j = i
      · subst hji
        simp [toFun, invFun]
      · have huj : (u.1 j).1 = (v j).1 := by
          simpa [Function.update, hji] using congrArg (fun f => (f j).1) u.property
        simpa [toFun, invFun, Function.update, hji] using huj.symm
    have hright : Function.RightInverse invFun toFun := by
      intro a
      simp [toFun, invFun]
    let e : {u : Point params // Function.update u i x = v} ≃ Fq params :=
      { toFun := toFun, invFun := invFun, left_inv := hleft, right_inv := hright }
    have hcard : Fintype.card {u : Point params // Function.update u i x = v} = params.q := by
      simpa using Fintype.card_congr e
    have hfiltercard :
        (Finset.univ.filter fun u : Point params => Function.update u i x = v).card = params.q := by
      calc
        (Finset.univ.filter fun u : Point params => Function.update u i x = v).card
            = Fintype.card {u : Point params // Function.update u i x = v} := by
                simpa using
                  (Fintype.card_subtype
                    (fun u : Point params => Function.update u i x = v)).symm
        _ = params.q := hcard
    calc
      (∑ u : Point params, if Function.update u i x = v then (1 : ℕ) else 0)
          = (Finset.univ.filter fun u : Point params => Function.update u i x = v).card := by
              simp
      _ = params.q := hfiltercard
      _ = if x = v i then params.q else 0 := by simp [hx]
  · have hsum_zero :
      (∑ u : Point params, if Function.update u i x = v then (1 : ℕ) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro u hu
      by_cases huv : Function.update u i x = v
      · exfalso
        have hi := congrArg (fun f => f i) huv
        simp [Function.update, hx] at hi
      · simp [huv]
    simp [hx, hsum_zero]

private lemma hypercubeAdjacencyWeight_eq_rerandomizeCoordWeight (params : Parameters)
    (u v : Point params) :
    hypercubeAdjacencyWeight params u v = (rerandomizeCoordWeight params u v : ℂ) := by
  unfold hypercubeAdjacencyWeight rerandomizeCoordWeight
  simp_rw [div_eq_mul_inv]
  rw [Nat.cast_mul, Nat.cast_mul]
  apply Complex.ext <;> simp
  ring

/-- The rerandomized-edge weight sums to the uniform point weight across each target column. -/
lemma rerandomizeCoordWeight_colSum (params : Parameters) (v : Point params) :
    ∑ u, rerandomizeCoordWeight params u v = (hypercubeVertexCount params : Error)⁻¹ := by
  have hcount :
      (∑ u : Point params,
        ∑ p : Fin params.m × Fq params,
          if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) = params.m * params.q := by
    rw [Finset.sum_comm]
    calc
      (∑ p : Fin params.m × Fq params,
          ∑ u : Point params, if Function.update u p.1 p.2 = v then (1 : ℕ) else 0)
        = ∑ p : Fin params.m × Fq params, if p.2 = v p.1 then params.q else 0 := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            rcases p with ⟨i, x⟩
            simpa using update_eq_fixed_count params i x v
      _ = params.m * params.q := by
            rw [Fintype.sum_prod_type]
            simp [Fintype.card_fin]
  have hcount_cast :
      (∑ u : Point params,
        (((∑ p : Fin params.m × Fq params,
            if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) : ℕ) : Error)) =
          (params.m * params.q : Error) := by
    simpa using congrArg (fun n : ℕ => (n : Error)) hcount
  have hM_ne : (hypercubeVertexCount params : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (pow_pos params.hq _))
  have hm_ne : (params.m : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hm)
  have hq_ne : (params.q : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hq)
  unfold rerandomizeCoordWeight
  simp_rw [div_eq_mul_inv]
  calc
    ∑ u : Point params,
        ↑(∑ p : Fin params.m × Fq params,
            if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) *
          (↑(hypercubeVertexCount params * params.m * params.q) : Error)⁻¹
      = (∑ u : Point params,
          ↑(∑ p : Fin params.m × Fq params,
              if Function.update u p.1 p.2 = v then (1 : ℕ) else 0)) *
            (↑(hypercubeVertexCount params * params.m * params.q) : Error)⁻¹ := by
          simpa using
            (Finset.sum_mul
              (s := (Finset.univ : Finset (Point params)))
              (f := fun u : Point params =>
                ↑(∑ p : Fin params.m × Fq params,
                    if Function.update u p.1 p.2 = v then (1 : ℕ) else 0))
              (a := (↑(hypercubeVertexCount params * params.m * params.q) : Error)⁻¹)).symm
    _ = (hypercubeVertexCount params : Error)⁻¹ := by
          rw [hcount_cast]
          field_simp [hM_ne, hm_ne, hq_ne]
          rw [Nat.cast_mul, Nat.cast_mul]
          ring

/-! ## Symmetry of edge weights and the Laplacian edge-difference form -/









/-- Closed form for the matrix local-variance trace expression. -/
lemma matrixLocalVarianceTraceForm_eq_closedForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixLocalVarianceTraceForm params model =
      (hypercubeVertexCount params : Error)⁻¹ *
          ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) -
        ∑ u, ∑ v,
          rerandomizeCoordWeight params u v *
            ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
  have hdiag :
      ∑ u, ∑ v,
          Complex.re
            (((if u = v then ((hypercubeVertexCount params : ℂ)⁻¹) else 0) *
                matrixExpectation model.state ((model.family v)ᴴ * model.family u))) =
        (hypercubeVertexCount params : Error)⁻¹ *
          ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) := by
    calc
      ∑ u, ∑ v,
          Complex.re
            (((if u = v then ((hypercubeVertexCount params : ℂ)⁻¹) else 0) *
                matrixExpectation model.state ((model.family v)ᴴ * model.family u)))
        = ∑ u,
            ((hypercubeVertexCount params : Error)⁻¹ *
              ev (matrixModelState model) ((model.family u)ᴴ * model.family u)) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              calc
                ∑ v,
                    Complex.re
                      (((if u = v then ((hypercubeVertexCount params : ℂ)⁻¹) else 0) *
                          matrixExpectation model.state ((model.family v)ᴴ * model.family u)))
                  = ∑ v,
                      if u = v then
                        (hypercubeVertexCount params : Error)⁻¹ *
                          ev (matrixModelState model) ((model.family u)ᴴ * model.family u)
                      else 0 := by
                          refine Finset.sum_congr rfl ?_
                          intro v hv
                          by_cases huv : u = v
                          · subst huv
                            simp [matrixExpectation, ev, matrixModelState, Complex.mul_re]
                          · simp [huv]
                  _ = (hypercubeVertexCount params : Error)⁻¹ *
                        ev (matrixModelState model) ((model.family u)ᴴ * model.family u) := by
                        rw [Finset.sum_ite_eq]
                        simp
      _ = (hypercubeVertexCount params : Error)⁻¹ *
            ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) := by
            simpa using
              (Finset.mul_sum
                (s := (Finset.univ : Finset (Point params)))
                (f := fun u => ev (matrixModelState model) ((model.family u)ᴴ * model.family u))
                (a := (hypercubeVertexCount params : Error)⁻¹)).symm
  have hadj :
      ∑ u, ∑ v,
          Complex.re
            (matrixAdjacencyOperator params u v *
              matrixExpectation model.state ((model.family v)ᴴ * model.family u)) =
        ∑ u, ∑ v,
          rerandomizeCoordWeight params u v *
            ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    refine Finset.sum_congr rfl ?_
    intro v hv
    rw [matrixAdjacencyOperator, hypercubeAdjacencyWeight_eq_rerandomizeCoordWeight]
    simp [matrixExpectation, ev, matrixModelState, Complex.mul_re]
  unfold matrixLocalVarianceTraceForm matrixLocalVarianceTraceWitness
    matrixCombinedColumnOperator
  rw [normalizedTrace_combined_tensor_eq]
  calc
    Complex.re
        (∑ u, ∑ v,
          matrixLaplacianOperator params u v *
            matrixExpectation model.state ((model.family v)ᴴ * model.family u))
      = ∑ u, ∑ v,
          Complex.re
            (matrixLaplacianOperator params u v *
              matrixExpectation model.state ((model.family v)ᴴ * model.family u)) := by
              simp
    _ = ∑ u, ∑ v,
          (Complex.re
              (((if u = v then ((hypercubeVertexCount params : ℂ)⁻¹) else 0) *
                  matrixExpectation model.state ((model.family v)ᴴ * model.family u))) -
            Complex.re
              (matrixAdjacencyOperator params u v *
                matrixExpectation model.state ((model.family v)ᴴ * model.family u))) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              refine Finset.sum_congr rfl ?_
              intro v hv
              simp [matrixLaplacianOperator, Matrix.one_apply, sub_mul]
    _ = ∑ u, ∑ v,
          Complex.re
            (((if u = v then ((hypercubeVertexCount params : ℂ)⁻¹) else 0) *
                matrixExpectation model.state ((model.family v)ᴴ * model.family u))) -
          ∑ u, ∑ v,
            Complex.re
              (matrixAdjacencyOperator params u v *
                matrixExpectation model.state ((model.family v)ᴴ * model.family u)) := by
              exact
                sum_sum_sub
                  (f := fun u v =>
                    Complex.re
                      (((if u = v then ((hypercubeVertexCount params : ℂ)⁻¹) else 0) *
                          matrixExpectation model.state ((model.family v)ᴴ * model.family u))))
                  (g := fun u v =>
                    Complex.re
                      (matrixAdjacencyOperator params u v *
                        matrixExpectation model.state ((model.family v)ᴴ * model.family u)))
    _ =
        (hypercubeVertexCount params : Error)⁻¹ *
            ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) -
          ∑ u, ∑ v,
            rerandomizeCoordWeight params u v *
              ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
              rw [hadj, hdiag]

end MIPStarRE.LDT.ExpansionHypercubeGraph

end

end LIDT


