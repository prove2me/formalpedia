-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Algebra
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Algebra
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:17:26.997643+00:00
-- url     : https://prove2.me/theorems/a3740875-1bc4-4f0e-a428-c4704a331d56
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / AddInUStep12 / Algebra
-- statement:
--   This bundle records the operator algebra underlying the four add-in-u chain moves. It gives the pointwise reductions for the final two moves and the Cauchy-Schwarz alignment identities for ordinary and selected versions of the first three moves.
--
--   Principal definitions:
--   - `addInU_step3_pointwise_op_eq`: the pointwise operator identity for the Q2 to Q3 move.
--   - `addInU_step4_pointwise_op_eq`: the pointwise operator identity for the Q3 to Q4 move.
--   - `addInU_cs_chain_step1_diff_eq`: the Cauchy-Schwarz alignment for Q0 to Q1.
--   - `addInU_cs_chain_step2_diff_eq`: the alignment for Q1 to Q2.
--   - `addInU_cs_chain_step3_diff_eq`: the alignment for Q2 to Q3.
--   - `addInU_selected_cs_chain_step1_diff_eq`: the selected alignment for Q0 to Q1.
--   - `addInU_selected_cs_chain_step2_diff_eq`: the selected alignment for Q1 to Q2.
--   - `addInU_selected_cs_chain_step3_diff_eq`: the selected alignment for Q2 to Q3.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep12/Algebra.lean#L69-L561

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep12/Algebra.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_CommonHelpers
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Helper
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Add-in-u Cauchy--Schwarz algebraic alignment

Algebraic operator-rewrites that align the add-in-u chain differences with the
forms used in the Cauchy--Schwarz estimates from the paper.

## Contents

- **addInU_step1/step2/step3/step4_pointwise_op_eq** (private) — operator-level
  difference rewrites for the four scalar moves.
- **addInU_cs_chain_step1/step2/step3/step4_diff_eq** — algebraic alignment of
  the diagonal chain differences to commutator-times-PSD form.
- **addInU_selected_cs_chain_step1/step2/step3/step4_diff_eq** — the same
  algebraic alignments before specializing the add-in-u selection.

The contraction and raw `√(2δ)` estimates using these identities live in
`AddInUStep12.Raw`; the selected-family raw estimates live in
`AddInUStep12.Selected`.

## References

- `references/ldt-paper/self_improvement.tex` lines 255–297
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

@[expose] public section


namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Algebraic CS-alignment for the add-in-u Step 1/2 differences

This section records pure operator-algebra rewrites that bring the differences
`addInUCSChainQ1 - addInUCSChainQ0` and `addInUCSChainQ2 - addInUCSChainQ1`
into the shapes required by the paper's Cauchy--Schwarz steps
`eq:move-one-cauchy-schwarz` and `eq:move-another-cauchy-schwarz`
(`references/ldt-paper/self_improvement.tex`, lines 261--266 and 285--289).
The reverse-difference companions give the downstream orientation
`Q₀ - Q₁` and `Q₁ - Q₂` without repeating subtraction bookkeeping.

They do **not** discharge the Cauchy--Schwarz estimate itself; they reduce the
raw `|Q₁ - Q₀| ≤ √(2δ)` and `|Q₁ - Q₂| ≤ √(2δ)` bounds to (a) a
sandwich-form Cauchy--Schwarz on the resulting `D · (M^u_h ⊗ T_h) · D'`-style
expression, plus (b) the two square-root inputs available via
`addInU_pointMeasurement_snd_selfConsistency` and
`addInU_filtered_sandwiched_tensor_sum_le_one`.

Names are deliberately suffixed `_diff_eq` to keep them honest as intermediate
algebraic identities rather than as the final scalar bounds. -/

private lemma addInU_step1_pointwise_op_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M Av Th : MIPStarRE.Quantum.Op κ) :
    opTensor (Av * M) (Th * Av) - opTensor M (Av * Th * Av) =
      (leftTensor (ι₂ := κ) Av - rightTensor (ι₁ := κ) Av) *
        (opTensor M Th * rightTensor (ι₁ := κ) Av) := by
  have hLeft :
      leftTensor (ι₂ := κ) Av * (opTensor M Th * rightTensor (ι₁ := κ) Av) =
        opTensor (Av * M) (Th * Av) := by
    change opTensor Av 1 * (opTensor M Th * opTensor 1 Av) =
        opTensor (Av * M) (Th * Av)
    rw [opTensor_mul, opTensor_mul]
    simp
  have hRight :
      rightTensor (ι₁ := κ) Av * (opTensor M Th * rightTensor (ι₁ := κ) Av) =
        opTensor M (Av * Th * Av) := by
    change opTensor 1 Av * (opTensor M Th * opTensor 1 Av) =
        opTensor M (Av * Th * Av)
    rw [opTensor_mul, opTensor_mul]
    simp [Matrix.mul_assoc]
  rw [sub_mul, hLeft, hRight]

private lemma addInU_step2_pointwise_op_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M Av Th : MIPStarRE.Quantum.Op κ) :
    opTensor (Av * M * Av) Th - opTensor (Av * M) (Th * Av) =
      leftTensor (ι₂ := κ) Av *
        (opTensor M Th * (leftTensor (ι₂ := κ) Av - rightTensor (ι₁ := κ) Av)) := by
  have hLeft :
      leftTensor (ι₂ := κ) Av * (opTensor M Th * leftTensor (ι₂ := κ) Av) =
        opTensor (Av * M * Av) Th := by
    change opTensor Av 1 * (opTensor M Th * opTensor Av 1) =
        opTensor (Av * M * Av) Th
    rw [opTensor_mul, opTensor_mul]
    simp [Matrix.mul_assoc]
  have hRight :
      leftTensor (ι₂ := κ) Av * (opTensor M Th * rightTensor (ι₁ := κ) Av) =
        opTensor (Av * M) (Th * Av) := by
    change opTensor Av 1 * (opTensor M Th * opTensor 1 Av) =
        opTensor (Av * M) (Th * Av)
    rw [opTensor_mul, opTensor_mul]
    simp
  rw [mul_sub, mul_sub, hLeft, hRight]

/-- Operator algebra reduction for the `Q₂ → Q₃` add-in-`u` step.

The operator difference of the bipartite-tensor expectations of
`A^v · H^u_h · A^v` and `A^u · H^u_h · A^v` (with shared right factor `T_h`)
factors as `(A^v − A^u) · H^u_h · A^v` on the left tensor factor, leaving the
right factor `T_h` untouched. -/
private lemma addInU_step3_pointwise_op_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Au Av Mh Th : MIPStarRE.Quantum.Op κ) :
    opTensor (Av * Mh * Av) Th - opTensor (Au * Mh * Av) Th =
      opTensor ((Av - Au) * Mh * Av) Th := by
  rw [opTensor_sub_left]
  congr 1
  noncomm_ring

/-- Operator algebra reduction for the `Q₃ → Q₄` add-in-`u` step.

The operator difference of the bipartite-tensor expectations of
`A^u · H^u_h · A^v` and `A^u · H^u_h · A^u` (with shared right factor `T_h`)
factors as `A^u · H^u_h · (A^v − A^u)` on the left tensor factor, leaving the
right factor `T_h` untouched. -/
private lemma addInU_step4_pointwise_op_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Au Av Mh Th : MIPStarRE.Quantum.Op κ) :
    opTensor (Au * Mh * Av) Th - opTensor (Au * Mh * Au) Th =
      opTensor (Au * Mh * (Av - Au)) Th := by
  rw [opTensor_sub_left]
  congr 1
  rw [mul_sub]

/-- Algebraic CS-alignment for the `Q₀ → Q₁` step.

Rewrites the difference `addInUCSChainQ1 - addInUCSChainQ0` in the exact form
appearing on the LHS of `eq:move-one-cauchy-schwarz` (paper lines 261--266):
the inner-product of the commutator
`A^v_{h(v)} ⊗ I − I ⊗ A^v_{h(v)}` with `M^u_h ⊗ T_h · (I ⊗ A^v_{h(v)})`,
averaged over `(u, v)` and summed over `h`.

This identity is purely algebraic; the actual `√(2δ)` bound still requires
the operator Cauchy--Schwarz step plus
`addInU_pointMeasurement_snd_selfConsistency`. -/
lemma addInU_cs_chain_step1_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ1 params strategy T - addInUCSChainQ0 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state
            ((leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av) *
              (opTensor Mh (T.outcome h) * rightTensor (ι₁ := ι) Av))) := by
  classical
  unfold addInUCSChainQ0 addInUCSChainQ1
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
  set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
  rw [← ev_sub]
  congr 1
  exact addInU_step1_pointwise_op_eq Mh Av (T.outcome h)

/-- Algebraic CS-alignment for the `Q₁ → Q₂` step.

Rewrites the difference `addInUCSChainQ2 - addInUCSChainQ1` in the exact form
appearing on the LHS of `eq:move-another-cauchy-schwarz` (paper lines 285--289):
the inner-product of `(A^v_{h(v)} · M^u_h) ⊗ T_h` with the commutator
`A^v_{h(v)} ⊗ I − I ⊗ A^v_{h(v)}`, averaged over `(u, v)` and summed over `h`.
The Lean statement keeps the equivalent factored form
`(A^v_{h(v)} ⊗ I) · (M^u_h ⊗ T_h)` before the commutator.

This identity is purely algebraic; the actual `√(2δ)` bound still requires
the operator Cauchy--Schwarz step plus
`addInU_pointMeasurement_snd_selfConsistency` and
`addInU_filtered_sandwiched_tensor_sum_le_one`. -/
lemma addInU_cs_chain_step2_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ2 params strategy T - addInUCSChainQ1 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state
            (leftTensor (ι₂ := ι) Av *
              (opTensor Mh (T.outcome h) *
                (leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av)))) := by
  classical
  unfold addInUCSChainQ1 addInUCSChainQ2
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
  set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
  rw [← ev_sub]
  congr 1
  exact addInU_step2_pointwise_op_eq Mh Av (T.outcome h)





/-- Algebraic CS-alignment for the `Q₂ → Q₃` step.

Rewrites the difference `addInUCSChainQ2 - addInUCSChainQ3` in the exact form
appearing on the LHS of `eq:change-one-cauchy-schwarz` (paper lines 306--311):
the expectation of `((A^v_{h(v)} - A^u_{h(u)}) · H^u_h · A^v_{h(v)}) ⊗ T_h`,
averaged over `(u, v)` and summed over `h`.

The paper writes the middle factor as the fiber operator `M^u_o`; in this
formalization the preceding `o`-sum has already been collapsed along
`o = h(u)`, so the same factor appears as
`H^u_h = (sandwichedPolynomialSubMeasAt params strategy T u).outcome h`.

This identity is purely algebraic; the operator Cauchy--Schwarz estimate is
proved downstream by `add_in_u_cs_chain_q2_q3_factored_cs`. -/
lemma addInU_cs_chain_step3_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state
            (opTensor ((Av - Au) * Mh * Av) (T.outcome h))) := by
  classical
  unfold addInUCSChainQ2 addInUCSChainQ3
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _
  set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
  set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
  rw [← ev_sub]
  congr 1
  exact addInU_step3_pointwise_op_eq Au Av Mh (T.outcome h)

/-! ### Selection-parametrized Step 1/2 algebraic identities -/

/-- Algebraic CS-alignment for the selected `Q₀ → Q₁` step.

This is the selection-parametrized form of `addInU_cs_chain_step1_diff_eq`.
The identity is stated in the same orientation as the diagonal chain, namely
as `Q₁ - Q₀`.  It rewrites the scalar difference using the same commutator
`A^v_{h(v)} ⊗ I − I ⊗ A^v_{h(v)}`, but sums only over the selected pairs
`(o,h) ∈ S_u` and leaves the arbitrary outcome operator `M^u_o` in place. -/
lemma addInU_selected_cs_chain_step1_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ1 params strategy M T S -
        addInUSelectedCSChainQ0 params strategy M T S =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            ((leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av) *
              (opTensor Moh (T.outcome ah.2) * rightTensor (ι₁ := ι) Av))) := by
  classical
  unfold addInUSelectedCSChainQ0 addInUSelectedCSChainQ1
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro ah _
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
  set Moh := (M uv.1).outcome ah.1
  rw [← ev_sub]
  congr 1
  exact addInU_step1_pointwise_op_eq Moh Av (T.outcome ah.2)

/-- Algebraic CS-alignment for the selected `Q₁ → Q₂` step.

This is the selection-parametrized form of `addInU_cs_chain_step2_diff_eq`,
with the arbitrary selected outcome operator `M^u_o` in the left tensor factor. -/
lemma addInU_selected_cs_chain_step2_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ1 params strategy M T S =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (leftTensor (ι₂ := ι) Av *
              (opTensor Moh (T.outcome ah.2) *
                (leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av)))) := by
  classical
  unfold addInUSelectedCSChainQ1 addInUSelectedCSChainQ2
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro ah _
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
  set Moh := (M uv.1).outcome ah.1
  rw [← ev_sub]
  congr 1
  exact addInU_step2_pointwise_op_eq Moh Av (T.outcome ah.2)





/-- Algebraic CS-alignment for the selected `Q₂ → Q₃` step.

This rewrites the first point-replacement move for an arbitrary selected
outcome family.  The only changed factor is the left copy of the point
projector, from `A^v_{h(v)}` to `A^u_{h(u)}`. -/
lemma addInU_selected_cs_chain_step3_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (opTensor ((Av - Au) * Moh * Av) (T.outcome ah.2))) := by
  classical
  unfold addInUSelectedCSChainQ2 addInUSelectedCSChainQ3
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro ah _
  set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
  set Moh := (M uv.1).outcome ah.1
  rw [← ev_sub]
  congr 1
  exact addInU_step3_pointwise_op_eq Au Av Moh (T.outcome ah.2)

/-- Algebraic CS-alignment for the selected `Q₃ → Q₄` step.

This rewrites the second point-replacement move for an arbitrary selected
outcome family.  The only changed factor is the right copy of the point
projector, from `A^v_{h(v)}` to `A^u_{h(u)}`. -/
lemma addInU_selected_cs_chain_step4_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (opTensor (Au * Moh * (Av - Au)) (T.outcome ah.2))) := by
  classical
  unfold addInUSelectedCSChainQ3 addInUSelectedCSChainQ4
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro ah _
  set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
  set Moh := (M uv.1).outcome ah.1
  rw [← ev_sub]
  congr 1
  exact addInU_step4_pointwise_op_eq Au Av Moh (T.outcome ah.2)





/-- Algebraic CS-alignment for the `Q₃ → Q₄` step.

Rewrites the difference `addInUCSChainQ3 - addInUCSChainQ4` in the exact form
appearing on the left-hand side of `eq:change-another` (paper lines 326--332):
the expectation of `(A^u_{h(u)} · H^u_h · (A^v_{h(v)} - A^u_{h(u)})) ⊗ T_h`,
averaged over `(u, v)` and summed over `h`.

This identity is purely algebraic; the actual operator Cauchy--Schwarz step
is provided by `add_in_u_cs_chain_q3_q4_factored_cs`. -/
lemma addInU_cs_chain_step4_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state
            (opTensor (Au * Mh * (Av - Au)) (T.outcome h))) := by
  classical
  unfold addInUCSChainQ3 addInUCSChainQ4
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _
  set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
  set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
  rw [← ev_sub]
  congr 1
  exact addInU_step4_pointwise_op_eq Au Av Mh (T.outcome h)

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


