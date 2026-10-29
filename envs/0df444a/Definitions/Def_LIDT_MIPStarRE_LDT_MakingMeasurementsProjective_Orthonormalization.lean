-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:36:39.63824+00:00
-- url     : https://prove2.me/theorems/61b2cefc-aa65-40dd-8130-079ffbba077b
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / Orthonormalization
-- statement:
--   This bundle states the key orthonormalization bridge for projectivizing measurements. It identifies self-consistency with consistency for a complete measurement, converts a rounded-projective witness into a local lifted estimate, and packages the main orthonormalization theorem.
--
--   Principal definitions:
--   - `bipartiteSSCRel_self_of_measurement`: identifies self-consistency with self-consistency of a complete measurement against itself.
--   - `leftLiftedRoundedProjMeasStatement_to_local`: converts a left-lifted rounded-projective witness to a local estimate.
--   - `orthonormalization`: the theorem statement for completing an approximately projective family.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean#L62-L487

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_LocalityPreservingRepair
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_ErrorBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_RestrictSome
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_Conversion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimp
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimpAttr
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
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
# Section 5 — Orthonormalization

The orthonormalization theorem and scalar bookkeeping lemmas from Section 5.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT



/-- For a complete measurement, bipartite SSC is exactly bipartite
consistency of `A` with itself. -/
private lemma bipartiteSSCRel_self_of_measurement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A : Measurement Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ →
      ConsRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily A.toSubMeas)
        ζ := by
  intro hssc
  rcases hssc with ⟨hssc⟩
  refine ⟨?_⟩
  have heq :
      bipartiteSSCError ψ (uniformDistribution Unit)
          (constSubMeasFamily A.toSubMeas) =
        bipartiteConsError ψ (uniformDistribution Unit)
          (constSubMeasFamily A.toSubMeas) (constSubMeasFamily A.toSubMeas) := by
    unfold bipartiteSSCError bipartiteConsError
    refine congrArg (avgOver _) ?_
    funext x
    cases x
    simp [constSubMeasFamily, qBipartiteSSCDefect, qBipartiteConsDefect,
      qBipartiteMatchMass, A.total_eq_one, leftTensor, opTensor]
  exact heq ▸ hssc

/-- A rounded-projective witness for `leftLiftedMeasurement A` coming from a
left-lifted local projective submeasurement immediately yields the local lifted
`≈`-statement. -/
private lemma leftLiftedRoundedProjMeasStatement_to_local {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)} {A : Measurement Outcome ι}
    {P : ProjSubMeas Outcome ι} {ζ : Error}
    (h : RoundedProjMeasStatement ψ (leftLiftedMeasurement (ιB := ι) A)
      (ProjSubMeas.liftLeft P) ζ) :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftLeft)
      (constSubMeasFamily P.toSubMeas.liftLeft)
      ζ := by
  simpa [leftLiftedMeasurement, leftPlacedSubMeas, SubMeas.liftLeft,
    ProjSubMeas.liftLeft] using h.closeness













/-- `thm:orthonormalization`.

A strongly self-consistent submeasurement on a permutation-invariant normalized
state admits a close projective submeasurement with the paper's
`100 * ζ^(1/4)` error envelope.

Paper origin: `references/ldt-paper/orthonormalization.tex:67-76`
(`\label{thm:orthonormalization}`).  The earlier proved completion-route
construction remains available as `orthonormalizationCompletionRoute`, but its
`120 * ζ^(1/4)` conclusion is weaker than this source theorem.  The proof below
follows the paper's completion-to-measurement reduction and then feeds the
completed measurement's `2ζ` self-consistency estimate into the sharp
locality-preserving Section 5 repair route, recovering the paper's scalar
constant. -/
theorem orthonormalization {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (A : SubMeas Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A) ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationError ζ) := by
  classical
  let : DecidableEq Outcome := Classical.decEq Outcome
  intro hssc
  have hζ_nonneg : 0 ≤ ζ :=
    le_trans
      (bipartiteSSCError_nonneg ψ (uniformDistribution Unit)
        (constSubMeasFamily A))
      hssc.overlapBound
  let Ahat : Measurement (Option Outcome) ι := optionCompletion A
  have hAhatssc :
      BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily Ahat.toSubMeas)
        (2 * ζ) := by
    simpa [Ahat] using
      Orthonormalization.Completion.optionCompletion_bipartiteSSCRel
        (ψ := ψ) (hperm := hperm) (hψ := hψ) (A := A) (ζ := ζ) hssc
  have hCons :
      ConsRel ψ (uniformDistribution Unit)
        (constSubMeasFamily Ahat.toSubMeas)
        (constSubMeasFamily Ahat.toSubMeas)
        (2 * ζ) :=
    bipartiteSSCRel_self_of_measurement (ψ := ψ) Ahat (2 * ζ) hAhatssc
  have hAlmost :
      MIPStarRE.LDT.MakingMeasurementsProjective.AlmostProjMeasStatement
        ψ (leftLiftedMeasurement (ιB := ι) Ahat)
        (consistencyToAlmostProjectiveError (2 * ζ)) := by
    exact MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjective
      (ψ := ψ) (A := Ahat) (B := Ahat) (ζ := 2 * ζ) hCons
  obtain ⟨P, hRounded⟩ :=
    leftLiftedProjectivizationRepair_of_sourceAlmostProjective_two_mul
      ψ hψ Ahat (2 * ζ) (by nlinarith [hζ_nonneg]) <| by
        simpa [consistencyToAlmostProjectiveError] using
          hAlmost.sourceAlmostProjective
  have hP_local :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily Ahat.toSubMeas.liftLeft)
        (constSubMeasFamily P.toSubMeas.liftLeft)
        (orthonormalizationMainLemmaError (2 * ζ)) :=
    leftLiftedRoundedProjMeasStatement_to_local hRounded
  have hPq :
      qSDD ψ Ahat.toSubMeas.liftLeft P.toSubMeas.liftLeft ≤
        orthonormalizationMainLemmaError (2 * ζ) := by
    simpa [ldt_simp] using hP_local.squaredDistanceBound
  let Psome : ProjSubMeas Outcome ι := restrictSomeProjSubMeas P
  have hPsomeq :
      qSDD ψ A.liftLeft Psome.toSubMeas.liftLeft ≤
        orthonormalizationMainLemmaError (2 * ζ) := by
    exact le_trans
      (Orthonormalization.Completion.qSDD_liftLeft_restrictSomeProjSubMeas_le
        (ψ := ψ) (A := A) (P := P))
      hPq
  have hcoeff :
      orthonormalizationMainLemmaError (2 * ζ) ≤ orthonormalizationError ζ := by
    open Orthonormalization.ErrorBounds in
    exact
      orthonormalizationMainLemmaError_two_mul_le_orthonormalizationError ζ
        hζ_nonneg
  refine ⟨Psome, ?_⟩
  constructor
  simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using
    (le_trans hPsomeq hcoeff)

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


