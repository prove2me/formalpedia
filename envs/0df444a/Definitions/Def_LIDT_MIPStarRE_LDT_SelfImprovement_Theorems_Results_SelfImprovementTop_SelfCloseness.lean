-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_SelfCloseness
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_SelfCloseness
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:38:45.94631+00:00
-- url     : https://prove2.me/theorems/51227466-d892-4610-a350-dae9699f9980
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / SelfImprovementTop / SelfCloseness
-- statement:
--   This bundle transports self-closeness through the helper and orthonormalization stages of self-improvement. It provides the generic transport estimate and the final-fields constructions in both unrestricted and small-error forms.
--
--   Principal definitions:
--   - `self_closeness_transport_through_orthonormalization`: transports self-closeness through helper SSC and orthonormalization.
--   - `final_fields_self_closeness`: constructs final-fields self-closeness.
--   - `final_fields_self_closeness_of_small_errors`: gives the literal-threshold small-error construction.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/SelfCloseness.lean#L60-L241

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/SelfCloseness.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_ProjectivizationChain_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_AlmostProjective
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_TruncationCombinatorics
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Helper
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimp
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimpAttr
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_LIDT_MIPStarRE_Quantum_ProjectorONB
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.Attr.Register

namespace LIDT

namespace MIPStarRE.LDT.MakingMeasurementsProjective
end MIPStarRE.LDT.MakingMeasurementsProjective
namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Final-fields self-closeness construction

This module contains the self-closeness transport used to fill the `selfCloseness`
field of `SelfImprovementFinalFields`.  The statements formalize the triangle
transport through helper self-consistency and the orthonormalization SDD step in
`references/ldt-paper/self_improvement.tex`, lines 727--741.
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Final-fields self-closeness construction

Same playbook as `final_fields_completeness_of_helper_completeness`, but for
the `selfCloseness` field. Unlike completeness, this field is closed
**without any new analytic obligation**: the helper-stage strong
self-consistency `hssc` and the orthonormalization SDD bound `horth` already
supplied to `selfImprovement` together suffice, by combining the bipartite-SSC
left↔right transport (`twoNotionsOfSelfConsistency`), the perm-inv
left↔right SDD reflection
(`MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv`), and the
three-step SDD triangle inequality
(`Preliminaries.stateDependentDistanceRel_triangle_three`).

Concretely the chain is `H.liftLeft → Hhat.liftLeft → Hhat.liftRight →
H.liftRight`, with edges of error `ε`, `2δ`, `ε` and the triangle constant `3`,
giving the final `3 * (ε + 2δ + ε)` bound. The remaining gap to the literal
`selfImprovementError` threshold used inside `SelfImprovementFinalFields` is a
separate numerical comparison on the explicit error definitions.

This is **not** an additional residual hypothesis: this construction derives the entire
`selfCloseness` field from data already present in the `selfImprovement`
proof. It does not assume the projective self-closeness it produces and does
not restate a combined final-fields hypothesis block.

Paper anchors:
* `references/ldt-paper/self_improvement.tex` lines 727--741 — projective
  self-closeness `Hhat ⊗ I ≈ I ⊗ Hhat → H ⊗ I ≈ I ⊗ H` via the
  triangle. The corresponding blueprint paragraph is
  `blueprint/src/chapter/ch07_self_improvement.tex` `\emph{Proof of
  \ref{item:self-improvement-self-closeness}}`.
-/

/-- Generic self-closeness transport through helper-stage strong
self-consistency and the orthonormalization SDD step, for the `Unit`-indexed
constant-family setting used by the self-improvement pipeline.

Given:
* `hssc` — bipartite strong self-consistency of the helper submeasurement `A`
  (helper SSC).
* `horth` — orthonormalization SDD bound between the left lifts of `A` and
  the projective replacement `B`.

Conclusion: SDD between the left and right placements of `B`, with the natural
three-step paper sum `3 * (ε + 2δ + ε)`.

Proof: `twoNotionsOfSelfConsistency` gives `A.liftLeft ≃_{2δ} A.liftRight`;
`sddRel_liftRight_of_liftLeft_permInv` reflects `horth` to a right-lift bound;
the triangle `B.liftLeft ↔ A.liftLeft ↔ A.liftRight ↔ B.liftRight` then
applies `stateDependentDistanceRel_triangle_three`. -/
theorem self_closeness_transport_through_orthonormalization
    {α : Type*} [Fintype α]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (A B : SubMeas α ι)
    (δ ε : Error)
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily A) δ)
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily A))
        (IdxSubMeas.liftLeft (constSubMeasFamily B)) ε) :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily B.liftLeft)
      (constSubMeasFamily B.liftRight)
      (3 * (ε + 2 * δ + ε)) := by
  -- Step 1 — helper bipartite SSC + perm inv ⇒ A.liftLeft ≃_{2δ} A.liftRight.
  have hA_lr :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily A))
        (IdxSubMeas.liftRight (constSubMeasFamily A)) (2 * δ) :=
    Preliminaries.twoNotionsOfSelfConsistency strategy.state
      (uniformDistribution Unit) (constSubMeasFamily A) δ
      ⟨strategy.permInvState, hssc⟩
  -- Step 2 — orthonormalization SDD reflected to right lifts.
  have horth_right :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftRight (constSubMeasFamily A))
        (IdxSubMeas.liftRight (constSubMeasFamily B)) ε :=
    MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv
      strategy.permInvState (uniformDistribution Unit)
      (constSubMeasFamily A) (constSubMeasFamily B) ε horth
  -- Step 3 — symmetrize the orthonormalization SDD on the left lifts.
  have horth_left_swap :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily B))
        (IdxSubMeas.liftLeft (constSubMeasFamily A)) ε :=
    Preliminaries.sddRel_symm strategy.state (uniformDistribution Unit)
      (IdxSubMeas.liftLeft (constSubMeasFamily A))
      (IdxSubMeas.liftLeft (constSubMeasFamily B)) ε horth
  -- Step 4 — three-step triangle B.liftLeft → A.liftLeft → A.liftRight → B.liftRight.
  have htri :=
    Preliminaries.stateDependentDistanceRel_triangle_three (Question := Unit)
      (Outcome := α) strategy.state (uniformDistribution Unit)
      (IdxSubMeas.liftLeft (constSubMeasFamily B))
      (IdxSubMeas.liftLeft (constSubMeasFamily A))
      (IdxSubMeas.liftRight (constSubMeasFamily A))
      (IdxSubMeas.liftRight (constSubMeasFamily B))
      ε (2 * δ) ε horth_left_swap hA_lr horth_right
  -- Reshape the IdxSubMeas.liftLeft/liftRight wrappers back to constSubMeasFamily form.
  change SDDRel strategy.state (uniformDistribution Unit)
    (IdxSubMeas.liftLeft (constSubMeasFamily B))
    (IdxSubMeas.liftRight (constSubMeasFamily B)) (3 * (ε + 2 * δ + ε))
  exact htri

/-- Final-fields self-closeness construction.

Specializes `self_closeness_transport_through_orthonormalization` to the
self-improvement parameters. Given the helper-stage bipartite SSC of `Hhat`
and the orthonormalization SDD bound between `Hhat.liftLeft` and
`H.toSubMeas.liftLeft` (both already produced inside `selfImprovement`), this
checked theorem derives the `selfCloseness` field of
`SelfImprovementFinalFields` with the natural paper sum-of-errors
`3 * (selfImprovementOrthogonalizationError +
      2 * selfImprovementHelperError +
      selfImprovementOrthogonalizationError)`.

Crucially, this construction adds **no** new analytic hypothesis: both `hssc` and
`horth` are already supplied to `selfImprovement`, so the `selfCloseness`
field of `SelfImprovementFinalFields` is now fully derivable up to a numerical
threshold comparison. -/
theorem final_fields_self_closeness
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta)) :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
      (constSubMeasFamily
        (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
      (3 * (selfImprovementOrthogonalizationError params eps delta
        + 2 * selfImprovementHelperError params eps delta
        + selfImprovementOrthogonalizationError params eps delta)) := by
  -- Reshape `horth` into the `IdxSubMeas.liftLeft` form expected by the
  -- generic transport theorem.
  have horthIdx :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily Hhat))
        (IdxSubMeas.liftLeft (constSubMeasFamily H.toSubMeas))
        (selfImprovementOrthogonalizationError params eps delta) := by
    change SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Hhat.liftLeft)
      (constSubMeasFamily H.toSubMeas.liftLeft)
      (selfImprovementOrthogonalizationError params eps delta)
    exact horth
  -- Apply the generic transport theorem.
  have hresult :=
    self_closeness_transport_through_orthonormalization params strategy
      Hhat H.toSubMeas
      (selfImprovementHelperError params eps delta)
      (selfImprovementOrthogonalizationError params eps delta)
      hssc horthIdx
  -- Reshape `B.liftLeft / B.liftRight` into the `leftPlacedSubMeas /
  -- rightPlacedSubMeas` form used by the `selfCloseness` field.
  change SDDRel strategy.state (uniformDistribution Unit)
    (constSubMeasFamily H.toSubMeas.liftLeft)
    (constSubMeasFamily H.toSubMeas.liftRight)
    (3 * (selfImprovementOrthogonalizationError params eps delta
      + 2 * selfImprovementHelperError params eps delta
      + selfImprovementOrthogonalizationError params eps delta))
  exact hresult

/-- Literal-threshold self-closeness construction under the standard
unit-interval hypotheses.

This wraps `final_fields_self_closeness` with the numerical absorption
`final_fields_self_closeness_error_le_selfImprovementError`, giving exactly
the `selfCloseness` threshold used in `SelfImprovementFinalFields`. -/
theorem final_fields_self_closeness_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta)) :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
      (constSubMeasFamily
        (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
      (selfImprovementError params eps delta) :=
  Preliminaries.stateDependentDistanceRel_mono strategy.state
    (uniformDistribution Unit)
    (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
    (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
    (3 * (selfImprovementOrthogonalizationError params eps delta
      + 2 * selfImprovementHelperError params eps delta
      + selfImprovementOrthogonalizationError params eps delta))
    (selfImprovementError params eps delta)
    (final_fields_self_closeness_error_le_selfImprovementError params eps delta
      heps heps_le_one hdelta hdelta_le_one hd_le_q)
    (final_fields_self_closeness params strategy eps delta Hhat H hssc horth)



end MIPStarRE.LDT.SelfImprovement

end

end LIDT


