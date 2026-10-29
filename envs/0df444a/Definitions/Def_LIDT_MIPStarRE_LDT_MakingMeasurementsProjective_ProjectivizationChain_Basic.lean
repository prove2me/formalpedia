-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_ProjectivizationChain_Basic
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_ProjectivizationChain_Basic
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:32:18.993322+00:00
-- url     : https://prove2.me/theorems/dad8bdd9-1549-4bda-ae7d-309fc4feb36d
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / ProjectivizationChain / Basic
-- statement:
--   This bundle supplies the error combination and permutation-invariance handoffs used by the projectivization chain.
--
--   Principal definitions:
--   - `orthonormalizeAndCompleteError`: combines the orthonormalization and completion losses.
--   - `qSDD_liftRight_eq_liftLeft_of_permInv`: identifies right and left lifts on a permutation-invariant state.
--   - `sddRel_liftRight_of_liftLeft_permInv`: transfers an SDD relation from left lifts to right lifts.
--   - `ProjectivizationSelfConsistencyHandoff`: packages the estimates handed to projectivization.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain/Basic.lean#L76-L222

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain/Basic.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
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
# Section 5 — basic projectivization data

This module contains the scalar estimates and elementary transport lemmas used
by the orthonormalization projectivization chain.  The mathematical source is the
orthonormalization-and-completion argument in `inductive_step.tex`, lines
130--149, together with the orthonormalization theorem and the completion
proposition cited there.

The declarations here are deliberately prior to the construction of the final
projective measurements.  They record the literal scalar obtained by composing
orthonormalization with completion, its absorbed form in the unit-error regime,
the right-register transport available under permutation invariance, and the
residual hypotheses passed to the self-consistency handoff theorem.  The actual
projective-measurement output theorem is in `ProjectivizationChain.Output`.

The scalar computation is

    ζ₂ = 2 · (100·ζ^{1/4}) + 4 · √(100·ζ^{1/4}) + 2·ζ
       = 200·ζ^{1/4} + 40·ζ^{1/8} + 2·ζ.

The paper prints the closed form `ζ₂ = 200·ζ^{1/4} + 40·ζ^{1/8}`.  The Lean
cascade uses the slightly widened absorbed scalar
`200·ζ^{1/4} + 42·ζ^{1/8}` downstream, since in the non-vacuous regime
`0 ≤ ζ ≤ 1` gives `2·ζ ≤ 2·ζ^{1/8}`.

## Status

- The orthonormalization step uses the source theorem `orthonormalization`.
  The theorem has a tracked proof gap for the sharp paper constant; this file
  no longer exposes its proof-stage construction data as a hypothesis of the
  orthonormalization projectivization output statement.
- The completion step uses the **fully-formalized** `completingToMeasurement`
  (`\leanok` in `blueprint/src/chapter/ch03_preliminaries.tex`), so no new
  bridge is introduced here.
- The output `Q` is now a `ProjMeas`. This uses the generic helper
  `Preliminaries.completeAtOutcomeProj`, whose proof relies only on the
  existing facts that `P.total` is a projection and that each `P_a` is
  absorbed by `P.total`.

## References

- Paper: `references/ldt-paper/inductive_step.tex` lines 130–149
  (application of `lem:orthonormalization-main-lemma` +
  `prop:completing-to-measurement`).
- Paper: `references/ldt-paper/orthonormalization.tex` lines 67–77
  (`thm:orthonormalization`).
- Paper: `references/ldt-paper/preliminaries.tex` lines 1101–1170
  (`prop:completing-to-measurement`).
- Blueprint: `blueprint/src/chapter/ch10_induction.tex` lines 350–360
  (`eq:G-with-Q-A`).
- Blueprint: `blueprint/src/chapter/ch04_projective.tex`
  (orthonormalization theorem).
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Error functions -/

/-- The combined error of the orthonormalization and completion chain.

Substituting `δ := orthonormalizationError ζ = 100·ζ^{1/4}` into the
closeness conclusion of `prop:completing-to-measurement`
(`2·δ + 4·√δ + 2·ζ`) gives

    `2 · (100·ζ^{1/4}) + 4 · √(100·ζ^{1/4}) + 2·ζ
       = 200·ζ^{1/4} + 40·ζ^{1/8} + 2·ζ`.

This is the literal error returned by composing the two existing lemmas.
The paper's printed `ζ₂ = 200·ζ^{1/4} + 40·ζ^{1/8}` (`inductive_step.tex`,
line 149) drops the residual `2·ζ` term; the formal cascade absorbs it into
the widened scalar `200·ζ^{1/4} + 42·ζ^{1/8}`. -/
noncomputable def orthonormalizeAndCompleteError (ζ : Error) : Error :=
  2 * orthonormalizationError ζ +
    4 * Real.sqrt (orthonormalizationError ζ) +
    2 * ζ





/-! ### Permutation-invariant right-register transport -/

/-- On a permutation-invariant bipartite state, the state-dependent distance between
right-lifted local submeasurements equals the distance between their left lifts.

This is the bookkeeping needed for the Bob-side completion estimate in
`inductive_step.tex` lines 140--147: `orthonormalizeAndComplete` naturally
returns a left-register bound, and the paper also uses the corresponding
right-register bound for $I \otimes G^{\mathrm B}$ and $I \otimes Q^{\mathrm B}$.
This is the submeasurement specialization of
`Preliminaries.qSDDCore_rightTensor_eq_leftTensor_of_permInv`. -/
lemma qSDD_liftRight_eq_liftLeft_of_permInv
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    (A B : SubMeas Outcome ι) :
    qSDD ψ A.liftRight B.liftRight = qSDD ψ A.liftLeft B.liftLeft := by
  simpa [qSDD, qSDDCore, SubMeas.liftRight, SubMeas.liftLeft,
    mkRightPlacedSubMeas_outcome, mkLeftPlacedSubMeas_outcome] using
    MIPStarRE.LDT.Preliminaries.qSDDCore_rightTensor_eq_leftTensor_of_permInv
      (ψ := ψ) hperm A.outcome B.outcome

/-- Transport an `SDDRel` bound from left lifts to right lifts on a
permutation-invariant bipartite state. -/
lemma sddRel_liftRight_of_liftLeft_permInv
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) :
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B) δ →
      SDDRel ψ 𝒟 (IdxSubMeas.liftRight A) (IdxSubMeas.liftRight B) δ := by
  intro h
  have hsddeq :
      sddError ψ 𝒟 (IdxSubMeas.liftRight A) (IdxSubMeas.liftRight B) =
        sddError ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B) := by
    unfold sddError avgOver
    refine Finset.sum_congr rfl ?_
    intro q _
    change 𝒟.weight q * qSDD ψ (A q).liftRight (B q).liftRight =
      𝒟.weight q * qSDD ψ (A q).liftLeft (B q).liftLeft
    rw [qSDD_liftRight_eq_liftLeft_of_permInv (ψ := ψ) hperm (A q) (B q)]
  constructor
  rw [hsddeq]
  exact h.squaredDistanceBound

/-! ### Projective self-consistency handoff -/

/-- Handoff data for the projective-measurement part of the orthonormalization proof.

**Faithful encoding:** The three fields record the paper's pre-projective
consistency and the two completion-closeness estimates from
`references/ldt-paper/inductive_step.tex:130-149`.  This is not a bridge or
residual assumption on a source theorem: `ProjectivizationChain.Output`
constructs the record from the orthonormalization and completion outputs before
`ProjectivizationChain.Handoff` uses it.

The fields are exactly the hypotheses needed after the orthonormalization and
completion constructions have produced projective measurements `Q_A,Q_B` close to
the pre-projective measurements `G_A,G_B`.  The theorem
`ProjectivizationSelfConsistencyHandoff.fullPolynomialConsistency` in
`ProjectivizationChain.Handoff` turns this data into the paper's
projective-measurement consistency estimate. -/
structure ProjectivizationSelfConsistencyHandoff
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (G_A G_B : Measurement Outcome ι) (Q_A Q_B : ProjMeas Outcome ι)
    (ζ₁ ζ₂ : Error) : Prop where
  /-- Paper line 131, obtained before the projective measurements are produced. -/
  preProjectiveConsistency :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ₁
  /-- Left-register completion closeness, paper line 146 (`eq:G-with-Q-A`). -/
  leftCompletionCloseness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas.liftLeft)
      (constSubMeasFamily Q_A.toSubMeas.liftLeft) ζ₂
  /-- Right-register completion closeness, paper line 147. -/
  rightCompletionCloseness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas.liftRight)
      (constSubMeasFamily Q_B.toSubMeas.liftRight) ζ₂

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


