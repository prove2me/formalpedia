-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Defs
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:00:32.209982+00:00
-- url     : https://prove2.me/theorems/c397857e-2660-42b3-88df-2a86b244c399
-- title:
--   LIDT definitions: LDT / SelfImprovement / Defs
-- statement:
--   This bundle defines the canonical SDP witnesses and add-in-$u$ data for self-improvement. It includes strict primal and dual witnesses, averaged point effects and dual slack, complementary slackness, selected point-polynomial pairs, sandwiched submeasurements, and the named error scales.
--
--   Principal definitions:
--   - `sdpDistinguishedPolynomial`: The zero polynomial used as the distinguished SDP block.
--   - `sdpStrictPrimalWeight` and `sdpStrictPrimalSubMeas`: The uniform strictly feasible primal witness with weight $1/(2|\mathcal P|)$.
--   - `sdpStrictDualWitness`: The dual witness $2I$.
--   - `averagedPointOperator`: The averaged point effect $A_g=\mathbb E_u A^u_{g(u)}$.
--   - `sdpDualSlackOperator`: The dual slack $Z-A_g$.
--   - `sdpComplementarySlacknessEquation`: The equation $T_gZ=T_gA_g$.
--   - `AddInUSelection` and `addInUSelectionPairs`: The selected point-indexed outcomes and polynomial pairs.
--   - `sandwichedPolynomialSubMeasAt`, `averagedSandwichedPolynomialSubMeas`, and `selfImprovementError`: The sandwiched families and their error scales.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Defs.lean#L32-L384

-- Generated from MIPStarRE/LDT/SelfImprovement/Defs.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 9 — Definitions

This file exposes the paper's SDP witnesses, the `add-in-u` transfer identity,
and the non-projective/projective self-improvement outputs through explicit named
constructions and error terms.

## References

- `references/ldt-paper/self_improvement.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.Quantum
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The zero polynomial used as the distinguished polynomial block in canonical
SDP completion arguments. -/
noncomputable def sdpDistinguishedPolynomial (params : Parameters) [FieldModel params.q] :
    Polynomial params :=
  ⟨0, by
    intro i
    simp [MvPolynomial.degreeOf_zero]⟩

/-- The paper's strict-feasibility weight `1 / (2 |\polyfunc{m}{q}{d}|)`. -/
noncomputable def sdpStrictPrimalWeight (params : Parameters)
    [FieldModel params.q] : Error :=
  1 / (2 * (Fintype.card (Polynomial params) : Error))

omit [Fintype ι] in
/-- Paper origin: `references/ldt-paper/self_improvement.tex:168-176`
(`\label{lem:sdp}` strict feasible primal witness
`T_g = (2 |\polyfunc{m}{q}{d}|)^{-1} I`).

The constant strict primal effects have total mass `(1/2)I`.  This is the
scalar identity behind the paper's strict feasible primal witness. -/
theorem sdpStrictPrimalConstantSum (params : Parameters)
    [FieldModel params.q] :
    ∑ _ : Polynomial params, sdpStrictPrimalWeight params •
        (1 : MIPStarRE.Quantum.Op ι) =
      ((1 / 2 : Error) • (1 : MIPStarRE.Quantum.Op ι)) := by
  have hdenom : (2 * (Fintype.card (Polynomial params) : Error)) ≠ 0 := by
    positivity
  calc
    ∑ g : Polynomial params, sdpStrictPrimalWeight params •
        (1 : MIPStarRE.Quantum.Op ι)
        = ((∑ g : Polynomial params, sdpStrictPrimalWeight params) : Error) •
            (1 : MIPStarRE.Quantum.Op ι) := by
              simpa using
                (Finset.sum_smul (s := Finset.univ)
                  (f := fun _ : Polynomial params => sdpStrictPrimalWeight params)
                  (x := (1 : MIPStarRE.Quantum.Op ι))).symm
    _ = ((Fintype.card (Polynomial params) : Error) *
          sdpStrictPrimalWeight params) •
          (1 : MIPStarRE.Quantum.Op ι) := by
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = ((1 / 2 : Error) • (1 : MIPStarRE.Quantum.Op ι)) := by
          congr 1
          unfold sdpStrictPrimalWeight
          field_simp [hdenom]

/-- The paper's strict-feasible primal SDP witness
`T_g = (2 |\polyfunc{m}{q}{d}|)^{-1} I`. -/
noncomputable def sdpStrictPrimalSubMeas (params : Parameters)
    [FieldModel params.q] : SubMeas (Polynomial params) ι :=
  { outcome := fun _ => sdpStrictPrimalWeight params • (1 : MIPStarRE.Quantum.Op ι)
    total := ∑ g : Polynomial params,
      sdpStrictPrimalWeight params • (1 : MIPStarRE.Quantum.Op ι)
    outcome_pos := fun _ => smul_nonneg (by
      unfold sdpStrictPrimalWeight
      positivity) (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι))
    sum_eq_total := rfl
    total_le_one := (le_of_eq (sdpStrictPrimalConstantSum (ι := ι) params)).trans (by
      simpa using smul_le_smul_of_nonneg_right
        (show (1 / 2 : Error) ≤ 1 by norm_num)
        (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι))) }

/-- The paper's uniform strict-feasible primal witness has total mass
`(1 / 2) • I`. -/
@[simp] theorem sdpStrictPrimalSubMeas_total (params : Parameters)
    [FieldModel params.q] :
    (sdpStrictPrimalSubMeas (ι := ι) params).total =
      ((1 / 2 : Error) • (1 : MIPStarRE.Quantum.Op ι)) := by
  simpa [sdpStrictPrimalSubMeas] using
    sdpStrictPrimalConstantSum (ι := ι) params

/-- Paper origin: `references/ldt-paper/self_improvement.tex:168-176`
(`\label{lem:sdp}` strict feasible dual witness `Z = 2I`);
blueprint `\label{lem:sdp-uniform-feasible-witness}`.

The paper's strict-feasible dual SDP witness `Z = 2I`. -/
noncomputable def sdpStrictDualWitness : MIPStarRE.Quantum.Op ι :=
  (2 : Error) • (1 : MIPStarRE.Quantum.Op ι)

/-- The paper's strict-feasible dual witness `2I` is positive semidefinite. -/
@[simp] theorem sdpStrictDualWitness_nonneg {ι : Type*} [Finite ι] [DecidableEq ι] :
    0 ≤ (sdpStrictDualWitness (ι := ι)) := by
  let := Fintype.ofFinite ι
  unfold sdpStrictDualWitness
  exact smul_nonneg (by norm_num)
    (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι))

/-- The paper's strict-feasible dual witness dominates the identity: `I ≤ 2I`. -/
theorem one_le_sdpStrictDualWitness {ι : Type*} [Finite ι] [DecidableEq ι] :
    (1 : MIPStarRE.Quantum.Op ι) ≤ sdpStrictDualWitness (ι := ι) := by
  let := Fintype.ofFinite ι
  simpa [sdpStrictDualWitness] using
    (smul_le_smul_of_nonneg_right
      (show (1 : Error) ≤ 2 by norm_num)
      (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι)))

/-- The averaged point operator `A_g = E_u A^u_{g(u)}`. -/
noncomputable def averagedPointOperator (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g)

/-- The averaged point operator `A_g` is positive semidefinite. -/
theorem averagedPointOperator_nonneg (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) (g : Polynomial params) :
    0 ≤ averagedPointOperator params strategy g := by
  unfold averagedPointOperator
  exact averageOperatorOverDistribution_nonneg (uniformDistribution (Point params))
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g)
    (fun u => (strategy.pointMeasurement u).toSubMeas.outcome_pos (g u))







/-- The dual slack operator `Z - A_g`. -/
noncomputable def sdpDualSlackOperator (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (Z : MIPStarRE.Quantum.Op ι) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  Z - averagedPointOperator params strategy g

/-- Dual feasibility already implies that the dual operator is positive
semidefinite, since every averaged point operator `A_g` is positive. -/
theorem sdpDualPositive_of_dualFeasible (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ sdpDualSlackOperator params strategy Z g) :
    0 ≤ Z := by
  -- Any polynomial would suffice here; the distinguished one is only a
  -- convenient fixed element of the finite polynomial type.
  let g0 : Polynomial params := sdpDistinguishedPolynomial params
  have hAg_nonneg : 0 ≤ averagedPointOperator params strategy g0 :=
    averagedPointOperator_nonneg params strategy g0
  have hAg_le_Z : averagedPointOperator params strategy g0 ≤ Z :=
    sub_nonneg.mp (by simpa [sdpDualSlackOperator] using hdual g0)
  exact hAg_nonneg.trans hAg_le_Z

/-- The complementary-slackness equation `T_g Z = T_g A_g`. -/
def sdpComplementarySlacknessEquation (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (g : Polynomial params) : Prop :=
  T.outcome g * Z =
    T.outcome g * averagedPointOperator params strategy g

/-- A point-indexed selection of outcome/polynomial pairs used in `lem:add-in-u`. -/
abbrev AddInUSelection (params : Parameters) [FieldModel params.q] (Outcome : Type*) :=
  Point params → Set (Outcome × Polynomial params)

/-- The finite set of selected outcome/polynomial pairs at a point `u`. -/
noncomputable def addInUSelectionPairs {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : AddInUSelection params Outcome) (u : Point params) :
    Finset (Outcome × Polynomial params) :=
  open Classical in
    Finset.univ.filter (fun ah : Outcome × Polynomial params => ah ∈ S u)

/-- The pointwise sandwiched operator `H^u_h = A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def sandwichedPolynomialOutcomeOperatorAt (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (h : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
  Au * (T.outcome h) * Au

/-- The sum of the pointwise sandwiched operators is bounded above by the identity. -/
private theorem sandwichedPolynomialOutcomeOperatorAt_sum_le_one (params : Parameters)
    [FieldModel params.q] (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (u : Point params) :
    ∑ h : Polynomial params, sandwichedPolynomialOutcomeOperatorAt params strategy T u h ≤ 1 := by
  let Au := strategy.pointMeasurement u
  -- Regroup by evaluation value a = h(u).
  calc
    ∑ h : Polynomial params, sandwichedPolynomialOutcomeOperatorAt params strategy T u h
      = ∑ a : Fq params,
          ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
            Au.toSubMeas.outcome a * T.outcome h * Au.toSubMeas.outcome a := by
          rw [show ∑ h : Polynomial params,
                sandwichedPolynomialOutcomeOperatorAt params strategy T u h =
              ∑ a : Fq params,
                ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                  sandwichedPolynomialOutcomeOperatorAt params strategy T u h from by
            exact polynomial_sum_fiberwise params u
              (sandwichedPolynomialOutcomeOperatorAt params strategy T u)]
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro h hh
          simp only [sandwichedPolynomialOutcomeOperatorAt,
            pointConditionedOutcomeOperatorAtPolynomial]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
          simp [Au, hh]
    _ = ∑ a : Fq params,
          Au.toSubMeas.outcome a *
            (∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
              T.outcome h) *
            Au.toSubMeas.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [← Matrix.sum_mul, ← Matrix.mul_sum]
    _ ≤ ∑ a : Fq params, Au.toSubMeas.outcome a := by
          refine Finset.sum_le_sum ?_
          intro a _
          have hfilt_le_one : ∑ h ∈ Finset.univ.filter
              (fun h : Polynomial params => h u = a), T.outcome h ≤ 1 :=
            calc
              ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a), T.outcome h
                ≤ ∑ h : Polynomial params, T.outcome h :=
                  Finset.sum_le_sum_of_subset_of_nonneg
                    (Finset.filter_subset _ _) (fun h _ _ => T.outcome_pos h)
              _ = T.total := T.sum_eq_total
              _ ≤ 1 := T.total_le_one
          simpa [Au.proj a] using
            IsSelfAdjoint.conjugate_le_conjugate
              (c := Au.toSubMeas.outcome a) hfilt_le_one (Au.outcome_hermitian a)
    _ = Au.toSubMeas.total := by
          rw [Au.toSubMeas.sum_eq_total]
    _ = 1 := by
          simpa using Au.total_eq_one

/-- The pointwise sandwiched submeasurement `H^u = {H^u_h}`. -/
noncomputable def sandwichedPolynomialSubMeasAt (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (u : Point params) :
    SubMeas (Polynomial params) ι :=
  { outcome := sandwichedPolynomialOutcomeOperatorAt params strategy T u
    total := ∑ h : Polynomial params,
      sandwichedPolynomialOutcomeOperatorAt params strategy T u h
    outcome_pos := fun h => by
      simp only [sandwichedPolynomialOutcomeOperatorAt, pointConditionedOutcomeOperatorAtPolynomial]
      exact IsSelfAdjoint.conjugate_nonneg (T.outcome_pos h)
        (SubMeas.outcome_hermitian (strategy.pointMeasurement u).toSubMeas (h u))
    sum_eq_total := rfl
    total_le_one := by
      exact sandwichedPolynomialOutcomeOperatorAt_sum_le_one params strategy T u }

/-- The average of the total pointwise sandwiched operators is bounded by the identity. -/
private theorem averagedSandwichedPolynomialSubMeas_total_le_one (params : Parameters)
    [FieldModel params.q] (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    ∑ h : Polynomial params,
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h) ≤ 1 := by
  let 𝒟 := uniformDistribution (Point params)
  calc
    ∑ h : Polynomial params,
        averageOperatorOverDistribution 𝒟
          (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
      = averageOperatorOverDistribution 𝒟
          (fun u => ∑ h : Polynomial params,
            sandwichedPolynomialOutcomeOperatorAt params strategy T u h) := by
            exact (averageOperatorOverDistribution_sum 𝒟
              (fun u h => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)).symm
    _ = averageOperatorOverDistribution 𝒟
          (fun u => (sandwichedPolynomialSubMeasAt params strategy T u).total) := by
            exact averageOperatorOverDistribution_congr 𝒟 _ _ fun u => by
              simp [sandwichedPolynomialSubMeasAt]
    _ ≤ 1 := by
          simpa [𝒟] using
            averageOperatorOverDistribution_uniform_le_one
              (fun u => (sandwichedPolynomialSubMeasAt params strategy T u).total)
              (fun u => (sandwichedPolynomialSubMeasAt params strategy T u).total_le_one)

/-- The averaged sandwiched submeasurement `H_h = E_u H^u_h`. -/
noncomputable def averagedSandwichedPolynomialSubMeas (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : SubMeas (Polynomial params) ι :=
  { outcome := fun h =>
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
    total := ∑ h : Polynomial params,
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
    outcome_pos := fun h => averageOperatorOverDistribution_nonneg
      (uniformDistribution (Point params))
      (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
      (fun u => (sandwichedPolynomialSubMeasAt params strategy T u).outcome_pos h)
    sum_eq_total := rfl
    total_le_one := by
      exact averagedSandwichedPolynomialSubMeas_total_le_one params strategy T }

/-- The variance error entering `lem:add-in-u`. -/
noncomputable def selfImprovementVarianceError (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error) : Error :=
  globalVarianceOfPointsError params eps delta

/-- The error term in `lem:add-in-u`. -/
noncomputable def addInUError (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error) : Error :=
  4 * Real.rpow (selfImprovementVarianceError params eps delta) (1 / (2 : Error))

/-- The quantitative error from `lem:self-improvement-helper`. -/
noncomputable def selfImprovementHelperError (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error) : Error :=
  100 * (params.m : Error) *
    (Real.rpow eps (1 / (2 : Error)) +
      Real.rpow delta (1 / (2 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (2 : Error)))

/-- The orthogonalization error applied to the helper output. -/
noncomputable def selfImprovementOrthogonalizationError (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error) : Error :=
  orthonormalizationError (selfImprovementHelperError params eps delta)

/-- The postprocessed error after projecting the helper output. -/
noncomputable def selfImprovementDataProcessingError (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error) : Error :=
  8 * selfImprovementHelperError params eps delta +
    8 * Real.rpow (selfImprovementOrthogonalizationError params eps delta)
      (1 / (2 : Error))

/-- The quantitative error from `thm:self-improvement`. -/
noncomputable def selfImprovementError (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error) : Error :=
  MainInductionStep.selfImprovementInInductionError params eps delta 0

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


