-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_Conversion
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_Conversion
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:07:00.200027+00:00
-- url     : https://prove2.me/theorems/a4484037-8667-4760-95c4-3f1d6d9a2088
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / SpectralTruncation / Conversion
-- statement:
--   This bundle converts between the spectral-truncation formulation and the rounding and rank-reduction interfaces of projective measurement construction. It turns a rounding witness into a truncation statement, reconstructs such a witness, and feeds the result into the QXP rank-reduction layer.
--
--   Principal definitions:
--   - `spectralTruncationStatement_of_witness`: converts a rounding witness into a spectral-truncation statement.
--   - `toRoundingToProjectorsWitness`: constructs the rounding witness with its closeness and total bounds.
--   - `projectiveLowRankSum_of_spectralTruncationStatement`: passes truncation data into projective low-rank reduction.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/Conversion.lean#L35-L102

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/Conversion.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_TruncationCombinatorics
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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Spectral truncation statement conversions

This file contains the structural conversions between the rounded-projector
witness used by the QXP rank-reduction layer and the
`SpectralTruncationStatement` interface used by orthonormalization.

The conversions are field-for-field copies.  The constructive spectral
truncation theorem, which produces such a rounded projective family from the
paper's almost-projective hypothesis, is proved in the sibling proof-layer
module `SpectralTruncation.ProjectiveNonMeasurement`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

/-! ### Spectral truncation statement conversion

Convert a `RoundingToProjectorsWitness` to a `SpectralTruncationStatement`.
The two types are field-for-field identical after `SpectralTruncationStatement.closeness`
was weakened to `2√ζ`. -/

/-- Convert a `RoundingToProjectorsWitness` to a `SpectralTruncationStatement`.

This is a structural field-for-field copy: both types carry the same data
(rounded family, projectivity, `2√ζ` closeness, total bound `1 + 2√ζ`).

The mathematical content of `lem:projective-non-measurement` — constructing
the rounded family — is the caller's responsibility when building a
`RoundingToProjectorsWitness`. -/
noncomputable def spectralTruncationStatement_of_witness {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (R : OpFamily Outcome ι)
    (hwitness : RoundingToProjectorsWitness ψ A ζ R) :
    SpectralTruncationStatement ψ A ζ :=
  ⟨R, hwitness.projective, hwitness.closeness, hwitness.sum_eq_total,
    hwitness.total_le⟩

namespace SpectralTruncationStatement

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:414-531`
(`\label{lem:projective-non-measurement}`; rounding-to-projectors lemma
with `2√ζ` closeness and `(1+2√ζ)·I` total bound).

Convert a spectral-truncation statement back to the rounded-projector
witness consumed by the QXP rank-reduction layer.

**Source:** This is a source-faithful structural conversion of the rounded-family
conclusion of the cited lemma. It does not recover the source almost-projective
estimate, because that estimate is not a field of `SpectralTruncationStatement`;
rank-reduction constructors which need it therefore keep it as a separate
hypothesis. -/
theorem toRoundingToProjectorsWitness {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    (h : SpectralTruncationStatement ψ A ζ) :
    RoundingToProjectorsWitness ψ A ζ h.roundedFamily where
  projective := h.projective
  closeness := h.closeness
  sum_eq_total := h.sum_eq_total
  total_le := h.total_le

end SpectralTruncationStatement

/-! ### Rank-reduction from spectral truncation -/

/-- Feed a spectral-truncation statement into the QXP rank-reduction layer.

The statement `SpectralTruncationStatement` remembers the rounded projectors
and their distance from the source measurement.  The rank-reduction witness also
records the source almost-projectivity estimate, so that estimate remains an
explicit hypothesis here.  This is the precise interface needed when the
orthonormalization spectral input is followed by the paper's
`Q -> X -> Xhat -> P` repair layer. -/
lemma projectiveLowRankSum_of_spectralTruncationStatement
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_le : ζ ≤ 1 / 4)
    (hSpectral : SpectralTruncationStatement ψ A ζ)
    (hsource :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data :=
  projectiveLowRankSum_of_roundingWitness ψ A ζ hψ hζ hζ_le hSpectral.roundedFamily
    hSpectral.toRoundingToProjectorsWitness hsource



end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


