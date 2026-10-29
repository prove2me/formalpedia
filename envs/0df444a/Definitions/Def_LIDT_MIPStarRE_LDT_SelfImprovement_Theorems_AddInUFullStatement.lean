-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_AddInUFullStatement
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_AddInUFullStatement
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:36:36.622738+00:00
-- url     : https://prove2.me/theorems/be4a55d2-904f-4e07-abdd-a8df9f31cb7a
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / AddInUFullStatement
-- statement:
--   This bundle records the full add-in-u statement and its specialization under a good strategy.
--
--   Principal definitions:
--   - `AddInUFullStatement`: the structured full add-in-u hypothesis and conclusion.
--   - `addInUFullStatement_of_isGood`: specializes the structure from the strategy goodness conditions.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/AddInUFullStatement.lean#L33-L183

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/AddInUFullStatement.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_AlgebraicIdentity
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_MainTheorems
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_PolynomialSumBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransportSum
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Point
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Utilities
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_SumForm
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Saturated
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Separation
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Witness
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Raw
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Selected
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Factored
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Selected
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Transfer
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Variance
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_CommonHelpers
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Bracketed
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_FiberBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_InputSdp
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Linearized
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SdpMatrixBridge
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Helper
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteConicDuality
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
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 7 — Selection-dependent transfer inequality for `lem:add-in-u`

This file proves the full selection-dependent transfer inequality of
`lem:add-in-u` (`references/ldt-paper/self_improvement.tex` lines 238–246).
The existing `addInU` lemma in
`MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/Bracketed.lean:584`
formalizes only the variance-bound specialization used in subsequent arguments.

The theorem below combines the already formalized selected Cauchy--Schwarz
chain with the six-step cardinality-free local-variance transport bound to
establish the paper's fully quantified transfer inequality.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.GlobalVariance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper-faithful full statement of `lem:add-in-u`.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 238–246
(`\label{lem:add-in-u}`). The proof spans lines 247–343.

The paper's statement: for every auxiliary sub-measurement family
`M = {M^u_o}` indexed by points `u ∈ F_q^m` with outcomes in some set `O`,
and every selection rule `S : Point → Set (O × Polynomial)`, the two indexed
expectations

```
  E_{u} ∑_{(o, h) ∈ S(u)} ⟨ψ| M^u_o ⊗ H_h |ψ⟩
```

and

```
  E_{u} ∑_{(o, h) ∈ S(u)} ⟨ψ| (A^u_{h(u)} M^u_o A^u_{h(u)}) ⊗ T_h |ψ⟩
```

agree to within `4 √ζ_variance = addInUError params eps delta`. Here `H` is
**not** an arbitrary sub-measurement: per the paper's construction and the
existing `SelfImprovementHelperConclusion.averagedConstruction` field, `H` is
the averaged sandwiched family `H_h = E_u (A^u · T_h · A^u)` derived from the
SDP measurement `T` supplied by `lem:sdp`. We substitute that derivation
directly into the inequality rather than taking `H` as an extra parameter,
so the structure records exactly the paper's transfer inequality.

The reduced `AddInUStatement` (`Statements.lean:293`) only records the
variance-bound consequence used in subsequent arguments; this structure
records the universally-quantified transfer inequality itself.

The Lean parameter `T` is kept as a `Measurement`, matching the paper's fixed
SDP-optimal family. The operators appearing in the transfer inequality depend
only on `T.toSubMeas`, and the proof below passes to that submeasurement layer
internally for the selected Cauchy--Schwarz chain and global-variance bounds. -/
structure AddInUFullStatement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (eps delta : Error) : Prop where
  /-- The selection-dependent transfer inequality from `lem:add-in-u`, with
  the paper's `4 √ζ_variance` bound. Universally quantified over the
  auxiliary outcome set `Outcome`, the auxiliary `M`-family, and the
  selection rule `S`, matching the paper's "for any sub-measurement and any
  selection" framing. The averaged family `H` is the canonical
  `averagedSandwichedPolynomialSubMeas params strategy T`, matching
  `SelfImprovementHelperConclusion.averagedConstruction`. -/
  selectionDependentTransfer :
    ∀ {Outcome : Type*} [Fintype Outcome]
      (M : IdxSubMeas (Point params) Outcome ι)
      (S : AddInUSelection params Outcome),
    |addInULeftQuantity params strategy M
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas) S
        - addInURightQuantity params strategy M T.toSubMeas S|
      ≤ addInUError params eps delta

-- The paper-facing add-in-u statement combines the selected scalar chain, the
-- local-variance transport theorem, and the global-variance sum transfer.
/-- Proves the selection-dependent transfer inequality of `lem:add-in-u`:
for any auxiliary sub-measurement family `M = {M^u_o}` and selection rule
`S : Point → Set (Outcome × Polynomial)`, the two indexed expectations agree
to within `4 √ζ_variance` (the bound `addInUError params eps delta`), given
strategy self-consistency in the `IsGood eps delta gamma` standing context.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 247–343
(proof of `\label{lem:add-in-u}`). The paper's proof is a Cauchy–Schwarz
chain through the four intermediate quantities `Q_0, Q_1, Q_2, Q_3, Q_4`
(formalized as `addInUCSChainQ0` … `addInUCSChainQ4` in
`MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/`),
combining the self-consistency of `A` (giving `√(2δ)` bounds on the
"insertion" steps) with the global-variance bound (giving
`√globalVarianceDeviationSum` bounds on the "averaging" steps).

The reduced `addInU` lemma in `Bracketed.lean:584` records the specialization
of this chain to the variance-bound consequence used later.  The theorem below
formalizes the full universally quantified inequality.

The `gamma` parameter and `hgood : IsGood eps delta gamma` hypothesis carry
the paper's standing "good strategy" context; `gamma` does not appear in
`AddInUFullStatement`'s bound (which is `addInUError params eps delta`),
matching the paper's framing where `lem:add-in-u` is invoked inside a
`good`-strategy section. -/
theorem addInUFullStatement_of_isGood
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (T : Measurement (Polynomial params) ι) :
    AddInUFullStatement params strategy T eps delta := by
  refine ⟨?_⟩
  intro Outcome _instOutcome M S
  have heps : 0 ≤ eps := eps_nonneg_of_isGood params strategy hgood
  have hdelta : 0 ≤ delta := delta_nonneg_of_isGood params strategy hgood
  have hssc :
      BipartiteSSCRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta := by
    constructor
    simpa [SymStrat.selfConsistencyFailureProbability] using
      hgood.selfConsistencyTest
  have hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta :=
    localVarianceDeviation_sum_le_localVarianceOfPointsError
      params strategy eps delta gamma hgood T.toSubMeas
  have hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        selfImprovementVarianceError params eps delta := by
    simpa [selfImprovementVarianceError] using
      globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
        params strategy eps delta T.toSubMeas hlocal
  let ηsc : Error := Real.sqrt (2 * delta)
  let ηgv : Error := Real.sqrt (selfImprovementVarianceError params eps delta)
  have h01 :
      |addInUSelectedCSChainQ0 params strategy M T.toSubMeas S -
        addInUSelectedCSChainQ1 params strategy M T.toSubMeas S| ≤ ηsc := by
    simpa [ηsc] using
      addInU_selected_cs_chain_step1_abs_le_sqrt_two_delta
        (params := params) (strategy := strategy) (M := M) (T := T.toSubMeas) (S := S)
        (delta := delta) hssc
  have h12 :
      |addInUSelectedCSChainQ1 params strategy M T.toSubMeas S -
        addInUSelectedCSChainQ2 params strategy M T.toSubMeas S| ≤ ηsc := by
    simpa [ηsc] using
      addInU_selected_cs_chain_step2_abs_le_sqrt_two_delta
        (params := params) (strategy := strategy) (M := M) (T := T.toSubMeas) (S := S)
        (delta := delta) hssc
  obtain ⟨hsteps3, hsteps4⟩ :=
    addInU_selected_cs_chain_step34_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      (params := params) (strategy := strategy) (M := M) (T := T.toSubMeas) (S := S) hglobal
  have h23 :
      |addInUSelectedCSChainQ2 params strategy M T.toSubMeas S -
        addInUSelectedCSChainQ3 params strategy M T.toSubMeas S| ≤ ηgv := by
    simpa [ηgv] using hsteps3
  have h34 :
      |addInUSelectedCSChainQ3 params strategy M T.toSubMeas S -
        addInUSelectedCSChainQ4 params strategy M T.toSubMeas S| ≤ ηgv := by
    simpa [ηgv] using hsteps4
  have hsum : ηsc + ηsc + ηgv + ηgv ≤ addInUError params eps delta := by
    have h :=
      two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError
        params eps delta heps hdelta
    dsimp [ηsc, ηgv] at h ⊢
    linarith
  exact add_in_u_selected_transfer_of_cs_chain
    (params := params) (strategy := strategy) (eps := eps) (delta := delta)
    (M := M) (T := T.toSubMeas) (S := S)
    (η01 := ηsc) (η12 := ηsc) (η23 := ηgv) (η34 := ηgv)
    h01 h12 h23 h34 hsum

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


