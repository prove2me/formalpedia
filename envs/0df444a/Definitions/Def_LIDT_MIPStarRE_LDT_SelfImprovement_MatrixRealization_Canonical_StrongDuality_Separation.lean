-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Separation
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Separation
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:17:03.094224+00:00
-- url     : https://prove2.me/theorems/1500bffb-2496-4a72-83eb-86b907104231
-- title:
--   LIDT definitions: LDT / SelfImprovement / MatrixRealization / Canonical / StrongDuality / Separation
-- statement:
--   This bundle develops the separation and attainment steps for the canonical matrix SDP. It constructs the primal image cone, characterizes its identity fiber, converts functional dual feasibility into a trace-pairing matrix witness, and proves attainment of the canonical primal objective.
--
--   Principal definitions:
--   - `matrixSdpCanonicalPrimalConeMap`: maps a primal matrix to its constraint and objective values.
--   - `matrixSdpCanonicalPrimalImageCone`: the closed image cone of positive canonical primal matrices.
--   - `matrixSdpCanonicalPrimalImageCone_mem_of_nonnegative`: places a positive primal matrix in the image cone.
--   - `matrixSdpCanonicalPrimalImageCone_mem_of_feasible`: places a feasible matrix on the identity constraint fiber.
--   - `matrixSdpCanonicalPrimalImageCone_identity_mem_iff_exists_feasible_objective`: characterizes objective values on that fiber.
--   - `matrixSdpCanonicalTracePairingDualMatrix_dualFeasible_of_conicFunctionalDualFeasible`: converts a functional dual bound to a feasible matrix dual.
--   - `matrixSdpCanonicalFunctionalDualObjective_min_of_matrixDualMin`: transfers matrix dual minimality to functional dual minimality.
--   - `matrixSdpCanonicalPrimalObjective_exists_isMaxOn`: proves primal objective attainment.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/StrongDuality/Separation.lean#L35-L573

-- Generated from MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/StrongDuality/Separation.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteConicDuality
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 9 -- Canonical SDP separation argument

This module contains the closed-image-cone separation argument and the resulting
zero-duality-gap theorem for the canonical finite-dimensional matrix SDP.

## References

- `references/ldt-paper/self_improvement.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder _root_.Matrix.Norms.Elementwise Topology

/-- The map sending a primal matrix to its constraint image and objective value. -/
noncomputable def matrixSdpCanonicalPrimalConeMap
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) →L[ℝ]
      MatrixOperator model.space × ℝ :=
  (matrixSdpCanonicalConstraintOperatorCLM params model).prod
    (matrixSdpCanonicalPrimalObjectiveCLM params model)

@[simp]
theorem matrixSdpCanonicalPrimalConeMap_apply
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalPrimalConeMap params model X =
      (matrixSdpCanonicalConstraintOperator params model X,
        Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X))) := by
  simp [matrixSdpCanonicalPrimalConeMap, matrixSdpCanonicalPrimalObjectiveCLM]

/-- The closed image cone of positive semidefinite canonical primal matrices under
the constraint-objective map. -/
noncomputable def matrixSdpCanonicalPrimalImageCone
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ProperCone ℝ (MatrixOperator model.space × ℝ) :=
  (MIPStarRE.Quantum.opNonnegativeProperCone
      (matrixSdpCanonicalBlockHilbertSpace params model).carrier).map
    (matrixSdpCanonicalPrimalConeMap params model)

/-- An actual positive semidefinite canonical primal matrix maps into the closed
canonical primal image cone. -/
theorem matrixSdpCanonicalPrimalImageCone_mem_of_nonnegative
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : 0 ≤ X) :
    (matrixSdpCanonicalConstraintOperator params model X,
        Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X))) ∈
      matrixSdpCanonicalPrimalImageCone params model := by
  rw [← matrixSdpCanonicalPrimalConeMap_apply params model X]
  rw [matrixSdpCanonicalPrimalImageCone, ProperCone.mem_map]
  exact subset_closure <| by
    have hXcone :
        X ∈ (MIPStarRE.Quantum.opNonnegativeProperCone
          (matrixSdpCanonicalBlockHilbertSpace params model).carrier).toPointedCone := by
      change 0 ≤ X
      exact hX
    exact (PointedCone.mem_map).2 ⟨X, hXcone, rfl⟩

/-- A feasible canonical primal matrix maps to the image-cone point with
constraint component equal to the identity. -/
theorem matrixSdpCanonicalPrimalImageCone_mem_of_feasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    ((1 : MatrixOperator model.space),
        Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X))) ∈
      matrixSdpCanonicalPrimalImageCone params model := by
  simpa [hX.constraintEqOne] using
    matrixSdpCanonicalPrimalImageCone_mem_of_nonnegative params model X hX.nonnegative

/-- On the identity constraint fiber, the closed primal image cone contains
exactly the objective values of feasible canonical primal matrices. -/
theorem matrixSdpCanonicalPrimalImageCone_identity_mem_iff_exists_feasible_objective
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) (t : ℝ) :
    ((1 : MatrixOperator model.space), t) ∈
        matrixSdpCanonicalPrimalImageCone params model ↔
      ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
        MatrixSdpCanonicalPrimalFeasible params model X ∧
          Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X)) = t := by
  classical
  constructor
  · intro hmem
    rw [matrixSdpCanonicalPrimalImageCone, ProperCone.mem_map] at hmem
    obtain ⟨u, hu_mem, hu_tendsto⟩ := mem_closure_iff_seq_limit.mp hmem
    have hu_witness : ∀ n : ℕ,
        ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
          X ∈ (MIPStarRE.Quantum.opNonnegativeProperCone
            (matrixSdpCanonicalBlockHilbertSpace params model).carrier).toPointedCone ∧
          (matrixSdpCanonicalPrimalConeMap params model :
            MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) →ₗ[ℝ]
              MatrixOperator model.space × ℝ) X = u n := by
      intro n
      exact PointedCone.mem_map.mp (hu_mem n)
    choose X hXcone hmap using hu_witness
    have hXnonneg : ∀ n : ℕ, 0 ≤ X n := by
      intro n
      have hx := hXcone n
      change 0 ≤ X n at hx
      exact hx
    have hmapCLM : ∀ n : ℕ,
        matrixSdpCanonicalPrimalConeMap params model (X n) = u n := by
      intro n
      simpa using hmap n
    let dimR : ℝ := Fintype.card model.space.carrier
    let R : ℝ := dimR + 1
    let s : Set (MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :=
      {Y | 0 ≤ Y ∧ ‖Y‖ ≤ R}
    have hsBounded : Bornology.IsBounded s := by
      rw [isBounded_iff_forall_norm_le]
      exact ⟨R, fun Y hY => hY.2⟩
    have hcoords :=
      (Prod.tendsto_iff u ((1 : MatrixOperator model.space), t)).mp hu_tendsto
    have htrace_cont : Continuous fun Y : MatrixOperator model.space =>
        Complex.re (Matrix.trace Y) :=
      Complex.continuous_re.comp continuous_id.matrix_trace
    have htrace_tendsto_u :
        Tendsto (fun n : ℕ => Complex.re (Matrix.trace ((u n).1))) atTop
          (𝓝 (Fintype.card model.space.carrier : ℝ)) := by
      change Tendsto (((fun Y : MatrixOperator model.space =>
        Complex.re (Matrix.trace Y)) ∘ fun n : ℕ => (u n).1)) atTop
          (𝓝 (Fintype.card model.space.carrier : ℝ))
      simpa [Matrix.trace_one] using
        (htrace_cont.tendsto (1 : MatrixOperator model.space)).comp hcoords.1
    have htrace_tendsto :
        Tendsto
          (fun n : ℕ => Complex.re (Matrix.trace
            (matrixSdpCanonicalConstraintOperator params model (X n)))) atTop
          (𝓝 dimR) := by
      have htrace_eq :
          (fun n : ℕ => Complex.re (Matrix.trace
            (matrixSdpCanonicalConstraintOperator params model (X n)))) =
            fun n : ℕ => Complex.re (Matrix.trace ((u n).1)) := by
        funext n
        rw [← hmapCLM n]
        rw [matrixSdpCanonicalPrimalConeMap_apply]
      rw [htrace_eq]
      simpa [dimR] using htrace_tendsto_u
    have hdim_lt_R : dimR < R := by
      simp [R]
    have heventTrace : ∀ᶠ n : ℕ in atTop,
        Complex.re (Matrix.trace
          (matrixSdpCanonicalConstraintOperator params model (X n))) < R :=
      htrace_tendsto.eventually (Iio_mem_nhds hdim_lt_R)
    have heventS : ∀ᶠ n : ℕ in atTop, X n ∈ s := by
      filter_upwards [heventTrace] with n hn
      refine ⟨hXnonneg n, ?_⟩
      exact (matrixSdpCanonicalNonnegative_norm_le_constraint_trace_re
        params model (X n) (hXnonneg n)).trans (le_of_lt hn)
    obtain ⟨X₀, _hX₀closure, k, hkmono, hX₀tendsto⟩ :=
      tendsto_subseq_of_frequently_bounded hsBounded heventS.frequently
    have hX₀nonneg : 0 ≤ X₀ :=
      (MIPStarRE.Quantum.isClosed_op_nonnegative
        (ι := (matrixSdpCanonicalBlockHilbertSpace params model).carrier)).mem_of_tendsto
        hX₀tendsto (Eventually.of_forall fun n => hXnonneg (k n))
    have hmap_tendsto_X₀ :
        Tendsto
          (fun n : ℕ => matrixSdpCanonicalPrimalConeMap params model (X (k n)))
          atTop (𝓝 (matrixSdpCanonicalPrimalConeMap params model X₀)) :=
      ((matrixSdpCanonicalPrimalConeMap params model).continuous.tendsto X₀).comp
        hX₀tendsto
    have hu_subseq_tendsto :
        Tendsto (u ∘ k) atTop (𝓝 ((1 : MatrixOperator model.space), t)) :=
      hu_tendsto.comp hkmono.tendsto_atTop
    have hmap_tendsto_identity :
        Tendsto
          (fun n : ℕ => matrixSdpCanonicalPrimalConeMap params model (X (k n)))
          atTop (𝓝 ((1 : MatrixOperator model.space), t)) := by
      have hfun :
          (fun n : ℕ => matrixSdpCanonicalPrimalConeMap params model (X (k n))) =
            u ∘ k := by
        funext n
        exact hmapCLM (k n)
      rw [hfun]
      exact hu_subseq_tendsto
    have hlimit :
        matrixSdpCanonicalPrimalConeMap params model X₀ =
          ((1 : MatrixOperator model.space), t) :=
      tendsto_nhds_unique hmap_tendsto_X₀ hmap_tendsto_identity
    have hconstraint :
        matrixSdpCanonicalConstraintOperator params model X₀ =
          (1 : MatrixOperator model.space) := by
      have := congrArg Prod.fst hlimit
      simpa [matrixSdpCanonicalPrimalConeMap_apply] using this
    have hobjective :
        Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X₀)) = t := by
      have := congrArg Prod.snd hlimit
      simpa [matrixSdpCanonicalPrimalConeMap_apply] using this
    exact ⟨X₀, ⟨hX₀nonneg, hconstraint⟩, hobjective⟩
  · rintro ⟨X, hX, hobj⟩
    simpa [hobj] using matrixSdpCanonicalPrimalImageCone_mem_of_feasible params model X hX













/-- A feasible functional dual bound on the canonical primal image cone gives a
paper-form dual feasible matrix through the Hermitian trace-pairing
representation. -/
theorem matrixSdpCanonicalTracePairingDualMatrix_dualFeasible_of_conicFunctionalDualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (ψ : StrongDual ℝ (MatrixOperator model.space))
    (hψ : ∀ z ∈ matrixSdpCanonicalPrimalImageCone params model, z.2 ≤ ψ z.1) :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model
        (MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM ψ) g := by
  let W := MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM ψ
  refine matrixSdpCanonicalDualConstraint_nonneg_of_trace_pairing_nonneg
    params model W ?_ ?_
  · exact matrixSdpCanonicalDualOperator_sub_objectiveOperator_isHermitian
      params model W (MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM_isHermitian ψ)
  · intro X hX
    have hle :
        Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
          Complex.re (Matrix.trace
            (matrixSdpCanonicalDualOperator params model W * X)) := by
      have hmem :=
        matrixSdpCanonicalPrimalImageCone_mem_of_nonnegative params model X hX
      have hfunctional := hψ
        (matrixSdpCanonicalConstraintOperator params model X,
          Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X))) hmem
      have hconstraintHerm :
          (matrixSdpCanonicalConstraintOperator params model X).IsHermitian :=
        matrixSdpCanonicalConstraintOperator_isHermitian_of_nonnegative params model hX
      rw [MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM_apply_of_isHermitian
        ψ hconstraintHerm] at hfunctional
      rwa [← matrixSdpCanonicalDualOperator_trace_constraint params model X W]
        at hfunctional
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
    exact sub_nonneg.mpr hle

/-- A paper-form dual minimizer is also minimal among feasible functional dual
bounds on the canonical primal image cone. -/
theorem matrixSdpCanonicalFunctionalDualObjective_min_of_matrixDualMin
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hZmin : ∀ W : MatrixOperator model.space,
      (∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model W g) →
      matrixSdpDualObjective model Z ≤ matrixSdpDualObjective model W) :
    ∀ ψ : StrongDual ℝ (MatrixOperator model.space),
      (∀ z ∈ matrixSdpCanonicalPrimalImageCone params model, z.2 ≤ ψ z.1) →
      matrixSdpDualObjective model Z ≤ ψ (1 : MatrixOperator model.space) := by
  intro ψ hψ
  let W := MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM ψ
  have hWdual :
      ∀ g : Polynomial params, 0 ≤ matrixSdpDualSlackOperator params model W g := by
    simpa [W] using
      matrixSdpCanonicalTracePairingDualMatrix_dualFeasible_of_conicFunctionalDualFeasible
        params model ψ hψ
  have hd_le_W := hZmin W hWdual
  have hI : (1 : MatrixOperator model.space).IsHermitian := Matrix.isHermitian_one
  have hWobj : matrixSdpDualObjective model W = ψ (1 : MatrixOperator model.space) := by
    have hψI :=
      MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM_apply_of_isHermitian ψ hI
    simpa [matrixSdpDualObjective, W] using hψI.symm
  simpa [hWobj] using hd_le_W









/-- The canonical primal objective attains a maximum on the feasible set. -/
theorem matrixSdpCanonicalPrimalObjective_exists_isMaxOn
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      MatrixSdpCanonicalPrimalFeasible params model X ∧
        ∀ Y : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
          MatrixSdpCanonicalPrimalFeasible params model Y →
            Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * Y)) ≤
              Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X)) := by
  obtain ⟨X, hX, hmax⟩ :=
    (matrixSdpCanonicalPrimalFeasible_isCompact params model).exists_isMaxOn
      (Set.nonempty_def.mpr (matrixSdpCanonicalPrimalFeasible_nonempty params model))
      (continuous_matrixSdpCanonicalPrimalObjective params model).continuousOn
  exact ⟨X, hX, fun Y hY => hmax hY⟩

/-- The canonical primal maximizer and dual minimizer exist, and their attained
values satisfy weak duality. This packages the attained optima but is not the
zero-gap strong-duality theorem. -/
theorem matrixSdpCanonicalPrimalDualOptima_exist
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      ∃ Z : MatrixOperator model.space,
        MatrixSdpCanonicalPrimalFeasible params model X ∧
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        (∀ Y : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
          MatrixSdpCanonicalPrimalFeasible params model Y →
            Complex.re (Matrix.trace
              (matrixSdpCanonicalObjectiveOperator params model * Y)) ≤
              Complex.re (Matrix.trace
                (matrixSdpCanonicalObjectiveOperator params model * X))) ∧
        (∀ W : MatrixOperator model.space,
          (∀ g : Polynomial params,
            0 ≤ matrixSdpDualSlackOperator params model W g) →
          matrixSdpDualObjective model Z ≤ matrixSdpDualObjective model W) ∧
        Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
          matrixSdpDualObjective model Z := by
  obtain ⟨X, hX, hXmax⟩ :=
    matrixSdpCanonicalPrimalObjective_exists_isMaxOn params model
  obtain ⟨Z, hZ, hZmin⟩ :=
    matrixSdpCanonicalDualObjective_exists_isMinOn params model
  refine ⟨X, Z, hX, hZ, hXmax, hZmin, ?_⟩
  exact matrixSdpCanonicalWeakDuality params model X hX Z
    (matrixSdpCanonicalDualConstraint_nonneg_of_dualFeasible params model Z hZ)

/-- The canonical matrix SDP has a primal-dual optimal pair with zero duality
gap.

This is the finite-dimensional strong-duality conclusion used in the paper's
Section 9 SDP argument.  The proof combines compact attainment, separation of
the closed primal image cone, and the trace-pairing representation of the
normalized separator; it does not add an auxiliary dominance hypothesis on the
dual matrix. -/
theorem matrixSdpCanonicalStrongDuality
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      ∃ Z : MatrixOperator model.space,
        MatrixSdpCanonicalPrimalFeasible params model X ∧
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X)) =
          matrixSdpDualObjective model Z := by
  obtain ⟨X, Z, hX, hZ, hXmax, hZmin, hweak⟩ :=
    matrixSdpCanonicalPrimalDualOptima_exist params model
  let p : ℝ := Complex.re (Matrix.trace
    (matrixSdpCanonicalObjectiveOperator params model * X))
  let d : ℝ := matrixSdpDualObjective model Z
  have hp_eq_d : p = d := by
    refine MIPStarRE.Quantum.conic_primalValue_eq_dualValue_of_fiber_max_dual_min
      (C := matrixSdpCanonicalPrimalImageCone params model)
      (y := (1 : MatrixOperator model.space)) (p := p) (d := d) ?_ ?_ ?_ ?_
    · simpa [p] using matrixSdpCanonicalPrimalImageCone_mem_of_feasible params model X hX
    · intro t hmem
      obtain ⟨Y, hY, hYobj⟩ :=
        (matrixSdpCanonicalPrimalImageCone_identity_mem_iff_exists_feasible_objective
          params model t).mp hmem
      have ht_le : t ≤ p := by
        simpa [p, hYobj] using hXmax Y hY
      exact ht_le
    · intro ψ hψ
      simpa [d] using
        matrixSdpCanonicalFunctionalDualObjective_min_of_matrixDualMin
          params model Z hZmin ψ hψ
    · simpa [p, d] using hweak
  refine ⟨X, Z, hX, hZ, ?_⟩
  simpa [p, d] using hp_eq_d

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


