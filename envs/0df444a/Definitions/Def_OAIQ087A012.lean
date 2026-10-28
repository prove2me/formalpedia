-- Prove2me | Definitions.Def_OAIQ087A012
-- name    : OAIQ087A012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:25:51.795751+00:00
-- url     : https://prove2.me/theorems/fce5e270-6e5f-430a-b4ba-a474ddfc1716
-- title:
--   Definitions bundle OAIQ087A012 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 425 declarations of OpenAI's Lean: 210 definitions, 1 inductive type or structure, 16 instances and 198 theorems. The definitions and types are `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Addresses.eval`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.RuntimeModel.Tape.enumList`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.RuntimeModel.headPorts`, `OAI.MaxCutGames.Foundations.PCP.CloudRounding.minorityCutEmbedding`, `OAI.MaxCutGames.Foundations.PCP.CloudRounding.minorityEquiv`, `OAI.MaxCutGames.Foundations.PCP.InitialGraph.variableLabel`, `OAI.MaxCutGames.Foundations.PCP.PoweringWalks.headTailEquiv`, `OAI.MaxCutGames.Foundations.PCP.PoweringWalks.leftFromPivot`, `OAI.MaxCutGames.Foundations.PCP.PoweringWalks.pivotEquiv`, `OAI.MaxCutGames.Foundations.PCP.PoweringWalks.rightFromPivot`, `OAI.MaxCutGames.Foundations.PCP.SpectralReturn.correlation`, `OAI.MaxCutGames.Foundations.PCP.SpectralReturn.edgeDensity`, `OAI.MaxCutGames.Foundations.PCP.SpectralReturn.iterateOperator`, `OAI.MaxCutGames.Foundations.PCP.SpectralReturn.markedStep`, `OAI.MaxCutGames.Foundations.PCP.SpectralReturn.returnMass`, `OAI.MaxCutGames.Foundations.PCP.ZigzagSpectral.centered`, `OAI.MaxCutGames.Foundations.PCP.ZigzagSpectral.cloudMean`, `OAI.MaxCutGames.Foundations.PCP.ZigzagSpectral.projection`, `OAI.MaxCutGames.Fourier.MatrixEnergy.labelingCoeff`, `OAI.MaxCutGames.Fourier.MatrixProducts.coefficientConvolution`, `OAI.MaxCutGames.Fourier.MatrixRestrictions.quotientKernelEquiv`, `OAI.MaxCutGames.Gadget.FreshGenericity.bad`, `OAI.MaxCutGames.Gadget.FreshGenericity.rankSpaceFintype`, `OAI.MaxCutGames.Gadget.LeafDetection.detectionProbability`, `OAI.MaxCutGames.Gadget.LeafDetection.survivalProbability`, `OAI.MaxCutGames.Gadget.Lift.restrict`, `OAI.MaxCutGames.Gadget.Orientation.dualOrientationEquiv`, `OAI.MaxCutGames.Gadget.Orientation.orientationEquiv`, `OAI.MaxCutGames.Gadget.OrientedBlockKernel.orientedBlockChange`, `OAI.MaxCutGames.Gadget.OrientedBlockKernel.orientedBlockLinear`, `OAI.MaxCutGames.Gadget.OutgoingHarmonic.instFintypeLinearEquivZModOfNatNatIdVec`, `OAI.MaxCutGames.Gadget.OutgoingHarmonic.outgoingLoss`, `OAI.MaxCutGames.Gadget.Parameters.genericityError`, `OAI.MaxCutGames.Gadget.QuadraticStageNoise.automorphismFintype`, `OAI.MaxCutGames.Gadget.QuadraticStageNoise.indexDecidableEq`, `OAI.MaxCutGames.Gadget.QuadraticStageNoise.quotientStage`, `OAI.MaxCutGames.Gadget.QuadraticStageNoise.stage`, `OAI.MaxCutGames.Gadget.Quotient.fiberMap`, `OAI.MaxCutGames.Gadget.QuotientDetection.pullbackFullLift`, `OAI.MaxCutGames.Gadget.StageNoiseRecurrence.error` and 171 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Encoding_BitCube`, `MaxCut_Encoding_BitValue`, `MaxCut_Estimates_CorrectSum`, `MaxCut_Estimates_Degree`, `MaxCut_Estimates_Density`, `MaxCut_Estimates_Divides`, `MaxCut_Estimates_ListSum`, `MaxCut_Estimates_Rename`, `MaxCut_Games_AdviceImageLaw`, `MaxCut_Games_AnswerBridge`, `MaxCut_Games_BaseDetection`, `MaxCut_Games_BlockRestriction`, `MaxCut_Games_Clone100Counting`, `MaxCut_Games_Concatenation`, `MaxCut_Games_Deletion`, `MaxCut_Games_Derivatives`, `MaxCut_Games_FinishBounds`, `MaxCut_Games_HarmonicLoss`, `MaxCut_Games_IncidenceExtraction`, `MaxCut_Games_Information`, `MaxCut_Games_KMSAnalyticFrequencyShift`, `MaxCut_Games_KMSAnalyticHybridEnergyImageSplit`, `MaxCut_Games_KMSAnalyticHybridEnergyImageTransportCore`, `MaxCut_Games_KMSAnalyticRestrictionTransport`, `MaxCut_Games_KMSAnalyticSmallInvariant`, `MaxCut_Games_KMSBasisComparisonNeighborsFiberFunctional`, `MaxCut_Games_KMSBasisComparisonPseudorandomTupleMap`, `MaxCut_Games_KMSBasisInvariant`, `MaxCut_Games_KMSFourthMomentMixedRestriction`, `MaxCut_Games_KMSFourthMomentPointShuffle`, `MaxCut_Games_KMSFourthMomentZoomInvariant`, `MaxCut_Games_KMSInjectionCountBounds`, `MaxCut_Games_KMSMomentTheorem`, `MaxCut_Games_MatrixChartKMSNeighbors`, `MaxCut_Games_MatrixChartShortcode`, `MaxCut_Games_OrientationVectors`, `MaxCut_Games_OrientedBlockKernel`, `MaxCut_Games_RankAdditivity`, `MaxCut_Games_RowErasure`, `MaxCut_Games_RowErasureConcentration`, `MaxCut_Games_RowErasureSelection`, `MaxCut_Games_SeparationCertificate`, `MaxCut_Games_ShortcodeFiberSampling`, `MaxCut_Games_StageNoiseRecurrence`, `MaxCut_Games_SubmoduleInterval`, `MaxCut_Machines_CompareLoop`, `MaxCut_Machines_EmitRows`, `MaxCut_Machines_FramedLen`, `MaxCut_Machines_Lookup`, `MaxCut_Machines_Printer`, `MaxCut_PCP_CayleySampling`, `MaxCut_PCP_CayleySpectral`, `MaxCut_PCP_ExpanderFamily`, `MaxCut_PCP_Generator`, `MaxCut_PCP_GraphGap`, `MaxCut_PCP_InitialGraph`, `MaxCut_PCP_Overlay`, `MaxCut_PCP_PortTables`, `MaxCut_PCP_PoweringDecoding`, `MaxCut_PCP_PoweringOpinionTables`, `MaxCut_PCP_PoweringTableSemantics`, `MaxCut_PCP_PreprocessingRegularSoundness`, `MaxCut_PCP_RawInitialTables`, `MaxCut_PCP_SpectralCut`.
--
--   **Imports.** It imports the bundles `OAIQ087A000`, `OAIQ087A001`, `OAIQ087A002`, `OAIQ087A003`, `OAIQ087A004`, `OAIQ087A005` and `OAIQ087A006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ087A019`; the statements `OAI.MaxCutGames.Decoder.MatrixGapChoice.exists_inverse_parameters`, `OAI.MaxCutGames.Gadget.BaseConstruction.exists_base`, `OAI.MaxCutGames.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound`, `OAI.MaxCutGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid`, `OAI.MaxCutGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound` and `OAI.MaxCutGames.Inverse.ShortcodeTheorem.inversePrinciple`; the proofs of `OAI.MaxCutGames.Appendix.A13Reduction.degree_reduction_truncated`, `OAI.MaxCutGames.Gadget.BaseConstruction.exists_base`, `OAI.MaxCutGames.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound`, `OAI.MaxCutGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid` and `OAI.MaxCutGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A000
import Definitions.Def_OAIQ087A001
import Definitions.Def_OAIQ087A002
import Definitions.Def_OAIQ087A003
import Definitions.Def_OAIQ087A004
import Definitions.Def_OAIQ087A005
import Definitions.Def_OAIQ087A006

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Deletion
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Fourier.MatrixRestrictions

open MaxCutGames.Integration.BinaryLinear
open scoped BigOperators

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup C] [Module F2 C]

/-- A dual map killed by the quotient has a unique factor with values in `W`.
This is the exact finite object counted in the parity argument of Lemma 5.3. -/
def quotientKernelEquiv (W : Submodule F2 E) :
    {T : C →ₗ[F2] E // W.mkQ.comp T = 0} ≃ (C →ₗ[F2] W) where
  toFun T := T.val.codRestrict W (fun x => by
    apply (Submodule.Quotient.mk_eq_zero W).mp
    exact congrArg (fun f : C →ₗ[F2] (E ⧸ W) => f x) T.property)
  invFun T := ⟨W.subtype.comp T, by
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero W).mpr (T x).property⟩
  left_inv T := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    rfl
  right_inv T := by
    apply LinearMap.ext
    intro x
    rfl

end MaxCutGames.Fourier.MatrixRestrictions

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RankAdditivity
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rank-additive pairs of linear maps

The rank-additive selector in Appendix A.1 has a concrete geometric meaning:
the two image spaces are disjoint and the two kernels span the domain. These
lemmas apply over any field and arbitrary finite dimensions, in particular
over `ZMod 2` with the second map equal to `Y + X`.
-/

/-! Actual subspace cardinality bounds used in (5.12)--(5.13).

Every subspace is the image of a projection endomorphism. Thus the set of all
subspaces is a quotient of the endomorphism space. The exact finite-field
linear-map count is reused from `Appendix.CompressionCount`.
-/

namespace MaxCutGames.Fourier.MatrixEnergy

open scoped BigOperators

variable {Q : Type*} {I : Q → Type*} [Fintype Q] [∀ q, Fintype (I q)]

section LinearMaps

open MatrixCharacters MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Fourier coefficient array for a family of labelings, including color as
part of the component index. -/
noncomputable def labelingCoeff {Y : Type*}
    (label : Q → (E →ₗ[F2] F) → Y) (qy : Q × Y) (S : F →ₗ[F2] E) : ℝ :=
  linearCoeff (colorIndicator (label qy.1) qy.2) S

end LinearMaps

open MatrixCharacters

end MaxCutGames.Fourier.MatrixEnergy

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Density
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.GaussianBellman

open scoped Real Topology NNReal ContDiff
open Set Filter MeasureTheory
open ProbabilityTheory

@[simp] theorem cdf_zero : cdf 0 = 1 / 2 := by simp [cdf]

noncomputable def quantile : ℝ → ℝ := Function.invFun cdf

noncomputable def plackett (t u v : ℝ) : ℝ :=
  density u * density (conditionalArg t u v) / sigma t

noncomputable def flux (t u v : ℝ) : ℝ :=
  density (conditionalArg t u v) * (t * v - u) / sigma t ^ 3

noncomputable def kernelX (t x y : ℝ) : ℝ := cdf (conditionalArg t (quantile x) (quantile y))

end OptimalMaxCut.GaussianBellman

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BitCube
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.GaussianBellman
open scoped BigOperators
open Set Finset

noncomputable def midpointSection {n : ℕ} (f : BitCube (n + 1) → ℝ) (x : BitCube n) : ℝ :=
  (f (Fin.cons false x) + f (Fin.cons true x)) / 2

end OptimalMaxCut.GaussianBellman

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Degree
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Walsh analysis on finite Boolean cubes. The basis and inversion
identities are proved from the explicit coordinate characters. -/

noncomputable section

namespace OptimalMaxCut.Analytic

open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad

/-- Frequency degree: cardinality of the set of selected Boolean coordinates. -/
def degree {I : Type*} [Fintype I] (s : Cube I) : ℕ :=
  (Finset.univ.filter fun i => s i = true).card

section NoiseIdentities

variable {I : Type*} [Fintype I] [DecidableEq I]

@[simp] theorem walsh_zero (x : Cube I) : walsh (fun _ => false) x = 1 := by
  simp [walsh, bitSign]

omit [DecidableEq I] in
@[simp] theorem degree_zero : degree (fun _ : I => false) = 0 := by
  simp [degree]

end NoiseIdentities

end OptimalMaxCut.Analytic

end -- noncomputable Walsh/analytic section

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Derivatives
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Actual Hybrid derivative energy in product coordinates

Parseval and affine restriction merge the selected Fourier coefficients over
each actual compressed frequency. For a product splitting, explicit linear
equivalences identify the quotient by the first factor with the second factor,
and the first-factor subspace with its original space. Reindexing the frequency
sum therefore introduces no multiplicity or normalization factor.
-/

/-!
# Actual Fourier components for the KMS analytic argument

All coefficients use normalized expectation on the primal matrix space; sums
over frequencies are unnormalized. These identities use only the common
trace-character Fourier identities.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters (linearTraceCharacter)
open MaxCutGames.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Fourier synthesis in the actual trace-character orthonormal basis. -/
def synthesis (a : (F →ₗ[F2] E) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  ∑ S, a S • (fun X => (linearTraceCharacter S X).re)

/-- The component formed by retaining precisely the actual frequencies in P. -/
def component (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F) → ℝ :=
  synthesis fun T => if P T then linearCoeff f T else 0

/-- The rank-level component uses actual image dimension. -/
def rankComponent (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  component (fun T => Module.finrank F2 T.range = i) f

end MaxCutGames.Inverse.KMSAnalytic

/-!
# Exact rank support of actual hybrid derivatives

The actual Hybrid selector loses exactly `dim A + codim B` in rank.
Consequently a pure rank component has derivative coefficients supported at
that exact remaining rank. Orders above the original rank give zero.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_SubmoduleInterval
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual reindexing of Appendix A.4 geometric witnesses by their raw triples.
The original nonzero weak-pair condition is equivalent to positive total
restriction order plus frequency rank. -/

/-! Products and the fourth moment for the actual binary trace Fourier model. -/

noncomputable section

namespace MaxCutGames.Fourier.MatrixProducts

open scoped BigOperators
open MatrixCharacters MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

variable [Fintype (E →ₗ[F2] F)]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (F →ₗ[F2] E)]

/-- Frequency convolution, with counting measure on the frequency space. -/
def coefficientConvolution (f g : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) : ℝ :=
  ∑ T : F →ₗ[F2] E, linearCoeff f T * linearCoeff g (S + T)

end MaxCutGames.Fourier.MatrixProducts

/-! The actual F1 witness bound in Lemma A.1. Coefficients remain signed;
absolute values occur only in the majorant. The two predecessor counts and
Cauchy–Schwarz give the factor `2^(6*d^2)`. -/
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSBasisInvariant
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Inverse.KMSBasisInvariant
noncomputable section
open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

/-- The invertible change of the ordered domain basis. -/
def primalChange (g : E ≃ₗ[F2] E) : (E →ₗ[F2] F) ≃ (E →ₗ[F2] F) where
  toFun X := X.comp g.toLinearMap
  invFun X := X.comp g.symm.toLinearMap
  left_inv X := by ext x; simp
  right_inv X := by ext x; simp

def IsBasisInvariant (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (g : E ≃ₗ[F2] E) X, f (X.comp g.toLinearMap) = f X

end
end MaxCutGames.Inverse.KMSBasisInvariant

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSAnalyticHybridEnergyImageSplit
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Partition frequencies by their actual image

A map with image `W` is uniquely a surjection onto `W`, followed by the
subspace inclusion. Consequently a sum over rank-`q` frequencies splits
exactly over dimension-`q` image subspaces and surjections onto each image.
The identities hold for arbitrary real weights and use no analytic estimate.
-/

/-!
# The actual hybrid selector in compressed-fiber coordinates

When the prescribed compression is onto `W`, the hybrid image and preimage
conditions are equivalent to injectivity of the complementary target map
and surjectivity of the remaining coordinate map. These are conditions on
the actual assembled linear map, with no rank or analytic hypothesis.
-/

/-! The exact injection/surjection factorization of the adapted coordinates. -/

/-! The actual hybrid compressed fiber, with no coordinate multiplicity. -/

/-!
# The actual small-space Fourier component

An injection from the small domain into the large domain lifts dual
frequencies by composition. Only surjective small-space frequencies are
retained. The identities below use the actual trace-character coefficients
and normalized primal expectation; no fourth-moment estimate is assumed.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

/-- The Fourier array of the small full-rank component. -/
def smallCoeff (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ)
    (T : F →ₗ[F2] I) : ℝ :=
  if Function.Surjective T then linearCoeff f (ι.comp T) else 0

/-- A genuine function on the small primal matrix space, synthesized in its
own orthonormal trace-character basis. -/
def smallComponent (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (I →ₗ[F2] F) → ℝ := synthesis (smallCoeff ι f)

end
end MaxCutGames.Inverse.KMSAnalytic

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSAnalyticSmallInvariant
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The small-space Fourier component inherits the original function's actual
basis invariance. Kernel-orbit transitivity supplies coefficient independence
of the embedding; finite character reindexing supplies function invariance.
There is no additional Fourier-invariance or analytic estimate hypothesis.
-/

/-! Exact coefficient arrays in an adapted hybrid fiber. -/

/-!
Exact trace-character identities for the adapted Hybrid coordinates. The
three coordinate blocks contribute multiplicatively to the actual character,
and assembling through the last-block embedding preserves the small phase.
These identities require neither rank assumptions nor analytic estimates.
-/

/-!
The frequency dichotomy behind the KMS point-restriction recursion.
A row appended to a surjective frequency is either independent, or is the
unique pullback of a functional on the smaller frequency space.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped Classical
open MaxCutGames.Fourier.MatrixCharacters

variable {E F J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup J] [Module F2 J]

/-- Append the primal value at the last coordinate. -/
def pointAppend (X : E →ₗ[F2] F) (a : F) : (E × F2) →ₗ[F2] F :=
  X.coprod (LinearMap.toSpanSingleton F2 F a)

@[simp] theorem pointAppend_apply (X : E →ₗ[F2] F) (a : F) (x : E) (c : F2) :
    pointAppend X a (x, c) = X x + c • a := rfl

/-- Fix one primal column, with no averaging or normalization. -/
def pointRestrict (f : ((E × F2) →ₗ[F2] F) → ℝ) (a : F) :
    (E →ₗ[F2] F) → ℝ := fun X => f (pointAppend X a)

/-- Extend an injection while retaining the newly fixed coordinate. -/
def pointLift (ι : J →ₗ[F2] E) : (J × F2) →ₗ[F2] (E × F2) :=
  ι.prodMap LinearMap.id

/-- The lower-dimensional embedding into the old coordinates. -/
def pointPad (ι : J →ₗ[F2] E) : J →ₗ[F2] (E × F2) :=
  ι.prod 0

/-- A non-surjective appended row vanishes on the kernel of a surjective
base frequency; the proof explicitly constructs a preimage otherwise. -/
theorem ker_le_of_not_surjective_prod (T : F →ₗ[F2] J)
    (hT : Function.Surjective T) (ell : F →ₗ[F2] F2)
    (h : ¬ Function.Surjective (T.prod ell)) : T.ker ≤ ell.ker := by
  intro w hw
  change ell w = 0
  by_contra hn
  have hwT : T w = 0 := hw
  have hwell : ell w = 1 :=
    (MaxCutGames.Integration.BinaryLinear.scalar_cases (ell w)).resolve_left hn
  apply h
  rintro ⟨y, c⟩
  obtain ⟨x, hx⟩ := hT y
  refine ⟨x + (c - ell x) • w, ?_⟩
  apply Prod.ext
  · change T (x + (c - ell x) • w) = y
    simp [hx, hwT]
  · change ell (x + (c - ell x) • w) = c
    simp [hwell]

/-- Exact factorization, including uniqueness, of every dependent row. -/
theorem not_surjective_prod_iff (T : F →ₗ[F2] J)
    (hT : Function.Surjective T) (ell : F →ₗ[F2] F2) :
    ¬ Function.Surjective (T.prod ell) ↔
      ∃! φ : J →ₗ[F2] F2, φ.comp T = ell := by
  constructor
  · intro h
    let φ := (T.ker.liftQ ell (ker_le_of_not_surjective_prod T hT ell h)).comp
      (T.quotKerEquivOfSurjective hT).symm.toLinearMap
    have hφ : φ.comp T = ell := by
      ext x
      simp [φ]
    refine ⟨φ, hφ, ?_⟩
    intro ψ hψ
    ext y
    obtain ⟨x, rfl⟩ := hT y
    exact (congrArg (fun L : F →ₗ[F2] F2 => L x) hψ).trans
      (congrArg (fun L : F →ₗ[F2] F2 => L x) hφ).symm
  · rintro ⟨φ, hφ, _⟩ hsurj
    obtain ⟨x, hx⟩ := hsurj (0, 1)
    have hTx : T x = 0 := congrArg Prod.fst hx
    have hellx : ell x = 1 := congrArg Prod.snd hx
    have he := congrArg (fun L : F →ₗ[F2] F2 => L x) hφ
    simp only [LinearMap.comp_apply, hTx, map_zero, hellx] at he
    exact zero_ne_one he

/-- Pullback along a surjection parametrizes the dependent rows exactly. -/
def dependentRowEquiv (T : F →ₗ[F2] J) (hT : Function.Surjective T) :
    (J →ₗ[F2] F2) ≃ {ell : F →ₗ[F2] F2 // ¬ Function.Surjective (T.prod ell)} where
  toFun φ := ⟨φ.comp T, (not_surjective_prod_iff T hT _).mpr
    ⟨φ, rfl, fun ψ hψ => by
      ext y
      obtain ⟨x, rfl⟩ := hT y
      exact congrArg (fun L : F →ₗ[F2] F2 => L x) hψ⟩⟩
  invFun ell := Classical.choose ((not_surjective_prod_iff T hT ell.val).mp ell.property)
  left_inv φ := by
    exact (Classical.choose_spec ((not_surjective_prod_iff T hT (φ.comp T)).mp
      ((not_surjective_prod_iff T hT _).mpr
        ⟨φ, rfl, fun ψ hψ => by
          ext y
          obtain ⟨x, rfl⟩ := hT y
          exact congrArg (fun L : F →ₗ[F2] F2 => L x) hψ⟩))).2 φ rfl |>.symm
  right_inv ell := by
    apply Subtype.ext
    exact (Classical.choose_spec
      ((not_surjective_prod_iff T hT ell.val).mp ell.property)).1

end

/-!
Exact Fourier merging when one primal column is fixed. All frequency sums
are unnormalized; the primal Fourier coefficient uses normalized expectation.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

/-- Splitting the last frequency row is an exact bijection. -/
def frequencyProdEquiv : ((F →ₗ[F2] E) × (F →ₗ[F2] F2)) ≃
    (F →ₗ[F2] (E × F2)) where
  toFun p := p.1.prod p.2
  invFun S := ((LinearMap.fst F2 E F2).comp S,
    (LinearMap.snd F2 E F2).comp S)
  left_inv _ := rfl
  right_inv _ := rfl

end

/-!
KMS Lemma 3.8 in coordinates with the newly fixed column last. The correction
sum runs over the dual of the smaller coordinate space. This is exactly one
representative of each graph subspace, so there is no basis-counting factor.
-/

end MaxCutGames.Inverse.KMSAnalytic

/-!
Exact Fourier slice energies and their one-point KMS recurrence. The energy
is an unnormalized sum of actual squared coefficients. Translation changes
only a unit sign, so the dependent graph terms in the point recursion have
identical slice energies, without an ambient-cardinality loss.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSAnalytic

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- An arbitrary actual Fourier slice; in the mixed estimate P fixes selected
frequency coordinates. -/
def sliceEnergy (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ T with P T, linearCoeff f T ^ 2

end
end MaxCutGames.Inverse.KMSFourthMoment

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSFourthMomentMixedRestriction
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact partial restrictions in product coordinates. Translating the full map
shifts both the fixed and free coordinates. The latter shift preserves every
actual Fourier slice energy, so finite differences of translated functions
cost only the finite Cauchy factor already present before restriction.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters

variable {A I F : Type*}
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

/-- Fix the first product block, leaving the second block free. -/
def partialRestrict (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    (I →ₗ[F2] F) → ℝ := fun X => f (a.coprod X)

@[simp] theorem partialRestrict_apply
    (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (X : I →ₗ[F2] F) : partialRestrict f a X = f (a.coprod X) := rfl

end
end MaxCutGames.Inverse.KMSFourthMoment

/-!
Exact Fourier merging after fixing a primal product block. The coefficient
uses normalized expectation, while the merged frequency sum is unnormalized.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSAnalytic
open MaxCutGames.Inverse.KMSFourthMoment

variable {A I F : Type*}
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

/-- Splitting the fixed and free frequency blocks is an exact bijection. -/
def frequencyBlockEquiv : ((F →ₗ[F2] A) × (F →ₗ[F2] I)) ≃
    (F →ₗ[F2] (A × I)) where
  toFun p := p.1.prod p.2
  invFun S := ((LinearMap.fst F2 A I).comp S,
    (LinearMap.snd F2 A I).comp S)
  left_inv _ := rfl
  right_inv _ := rfl

end

/-! The actual Fourier coefficient of an adapted hybrid fiber factors into
the complementary-block phase and a mixed partial-restriction coefficient. -/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates
open KMSFourthMoment

variable {A W D B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup W] [Module F2 W]
  [AddCommGroup D] [Module F2 D] [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C]

def coordinateOfData (z : B →ₗ[F2] W) (α : (B × C) →ₗ[F2] A)
    (ψ : Extension (C := C) z) (v : C →ₗ[F2] D) :
    Coordinates (A := A) (D := D) (C := C) z :=
  ⟨α, ψ.val, ψ.property, v⟩

def primalA (T : (A × (W × D)) →ₗ[F2] (B × C)) : A →ₗ[F2] (B × C) :=
  T.comp (LinearMap.inl F2 A (W × D))

def primalW (T : (A × (W × D)) →ₗ[F2] (B × C)) : W →ₗ[F2] (B × C) :=
  (T.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inl F2 W D)

def primalD (T : (A × (W × D)) →ₗ[F2] (B × C)) : D →ₗ[F2] (B × C) :=
  (T.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inr F2 W D)

end

/-!
# Cauchy--Schwarz for the hybrid coefficient fibers

The complementary-vector phase sum contributes the square of its number
of terms. Merging extensions with the same restriction contributes their
largest fiber size. Both factors come from finite Cauchy--Schwarz; summing
the disjoint fibers preserves the unnormalized coefficient energy.
-/

/-!
# Cardinality budgets for hybrid coefficient fibers

Extensions are counted by an exact equivalence with linear maps on the
complement. Injective complementary maps are bounded by all linear maps.
Images of fixed dimension are counted using the proved basis encoding of
subspaces. Their combined exponent fits the mixed Fourier denominator.
-/

/-!
Exact sums on fixed Fourier slices and compressed-frequency extension fibers.
Fixing the last frequency block leaves each first block exactly once, and
passing between an extension subtype and a filtered sum changes no weights.
-/

/-! A single compressed-image contribution is controlled by an actual mixed
slice energy. The only losses are the explicit finite coordinate counts. -/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates KMSFourthMoment

variable {A W D B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup W] [Module F2 W]
  [AddCommGroup D] [Module F2 D] [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 W]
  [FiniteDimensional F2 D] [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((B × C) →ₗ[F2] A)] [Fintype ((B × C) →ₗ[F2] W)]
  [Fintype ((B × C) →ₗ[F2] C)]
  [Fintype (C →ₗ[F2] D)] [Fintype (C →ₗ[F2] W)] [Fintype (B →ₗ[F2] W)]
  [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
  [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
  [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))]
  [Fintype ((W × C) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (W × C))]

def adaptedFiberCoefficient (z : B →ₗ[F2] W)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × (W × D)) →ₗ[F2] (B × C)) : ℝ :=
  ∑ S : {S : (B × C) →ₗ[F2] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[F2] D)},
    (if LinearIdentities.Hybrid S.val
        (LinearMap.range (LinearMap.inl F2 A (W × D)))
        (LinearMap.range (LinearMap.inl F2 B C)) then
      linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) S.val else 0) *
      (linearTraceCharacter S.val T).re

end
end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSAnalyticHybridEnergyImageTransportCore
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transport of a prescribed compressed image to adapted coordinates

The complement is an arbitrary actual complement to the image subspace.
The resulting coordinate change carries each original Fourier fiber to the
adapted fiber, preserving coefficients, phases, and the actual selector.
-/

noncomputable section
namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters (linearTraceCharacter linearTraceCharacter_apply linearTracePair)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]

/-- Keep the selected first factor and split the remaining space along its
prescribed compressed image. -/
def imageAmbientEquiv (W D : Submodule F2 U) (h : IsCompl W D) :
    (A × (W × D)) ≃ₗ[F2] (A × U) :=
  (LinearEquiv.refl F2 A).prodCongr (imageCoordinates W D h).symm

/-- The original function expressed in the adapted primal coordinates. -/
def imagePullback (W D : Submodule F2 U) (h : IsCompl W D)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (X : (A × (W × D)) →ₗ[F2] (B × C)) : ℝ :=
  f (X.comp (imageAmbientEquiv (A := A) W D h).symm.toLinearMap)

/-- The same affine translate expressed in adapted coordinates. -/
def imageTranslate (W D : Submodule F2 U) (h : IsCompl W D)
    (T : (A × U) →ₗ[F2] (B × C)) :
    (A × (W × D)) →ₗ[F2] (B × C) :=
  T.comp (imageAmbientEquiv W D h).toLinearMap

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-! The exact transport into the actual adapted fiber used by the mixed bound. -/

/-!
# Small-component pullback under ambient coordinate equivalences

The small domain stays fixed while the ambient embedding and primal codomain
are transported together. These are exact identities for the actual Fourier
coefficients and synthesized functions; they require no analytic estimate.
-/

end

/-!
Transport of actual small components when the ambient domain changes by a
linear equivalence. The coefficient and component identities hold for every
real function; basis invariance is separately transported when available.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

variable {E E' F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [AddCommGroup F] [Module F2 F] [AddCommGroup I] [Module F2 I]

/-- Reindex primal matrices by changing the ambient domain. -/
def ambientPrimalEquiv (h : E ≃ₗ[F2] E') :
    (E' →ₗ[F2] F) ≃ (E →ₗ[F2] F) where
  toFun X := X.comp h.toLinearMap
  invFun X := X.comp h.symm.toLinearMap
  left_inv X := by ext x; simp
  right_inv X := by ext x; simp

end
end MaxCutGames.Inverse.KMSAnalytic

/-!
# Product Hybrid energy from actual mixed slices

The derivative's exact rank support is partitioned by its actual compressed
image. Each image is put in complement coordinates, and the proved coefficient
factorization bounds that contribution by an actual mixed slice. The finite
image, extension, and complementary-map counts fit the mixed denominator.
The sole analytic premise is the displayed uniform bound on actual slices.
-/

noncomputable section

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters (linearTraceCharacter)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix MaxCutGames.Appendix.Derivatives
open KMSAnalytic KMSFourthMoment

local instance (priority := 2000) classicalSurjective_rfd0b6a_1 {X Y : Type*} :
    DecidablePred (Function.Surjective : (X → Y) → Prop) :=
  fun g => Classical.propDecidable (Function.Surjective g)
local instance mapFintype {V W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

local instance submoduleFintype {V : Type*}
    [AddCommGroup V] [Module F2 V] [Fintype V] : Fintype (Submodule F2 V) :=
  Fintype.ofInjective (fun W : Submodule F2 V => (W : Set V)) SetLike.coe_injective

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype A] [Fintype U] [Fintype B] [Fintype C]

/-- The actual mixed-slice hypothesis in all coordinates adapted to the
compressed image. It is a bound on `smallComponent`, with the original
function and translate transported by the explicit product equivalence. -/
def ProductMixedSliceBound (i : ℕ)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) (L : ℝ) : Prop :=
  ∀ (W D : Submodule F2 U),
    Module.finrank F2 W = i - (Module.finrank F2 A + Module.finrank F2 C) →
    ∀ (hD : IsCompl W D)
      (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))),
      Function.Injective κ →
      sliceEnergy (fun V : (B × C) →ₗ[F2] (W × C) =>
        (LinearMap.snd F2 W C).comp V = LinearMap.snd F2 B C)
        (partialRestrict (smallComponent κ (imagePullback W D hD f))
          (primalA (imageTranslate W D hD T))) ≤
        L / (2 : ℝ) ^ ((2 * Module.finrank F2 C +
          (i - (Module.finrank F2 A + Module.finrank F2 C))) *
            Module.finrank F2 (A × U))

/-- The selected coefficient at one ordinary product-compressed frequency. -/
def productFiberCoefficient (i : ℕ)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) (Z : B →ₗ[F2] U) : ℝ :=
  ∑ S : (B × C) →ₗ[F2] (A × U),
    if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A U))
        (LinearMap.range (LinearMap.inl F2 B C)) ∧
        (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) = Z
    then linearCoeff (rankComponent i f) S * (linearTraceCharacter S T).re else 0

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-!
# Exact transport of mixed small-component slices

A codomain equivalence transports the fixed primal coordinates and the
prescribed partial frequency together. The frequency reindexing is bijective,
so the actual slice energy has no multiplicity or normalization factor.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSFourthMomentPointShuffle
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Move one fixed coordinate to the last position while preserving the free
block. These are identities of actual linear maps and restricted functions;
no Fourier support or analytic estimate is assumed.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment

noncomputable section
open scoped Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Inverse.KMSAnalytic

variable {A0 A I F : Type*}
  [AddCommGroup A0] [Module F2 A0]
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

/-- Put the last coordinate into the fixed block through `e`, keeping the
free block unchanged. -/
def pointShuffle (e : (A0 × F2) ≃ₗ[F2] A) :
    ((A0 × I) × F2) ≃ₗ[F2] (A × I) where
  toFun p := (e (p.1.1, p.2), p.1.2)
  invFun p := (((e.symm p.1).1, p.2), (e.symm p.1).2)
  left_inv p := by
    rcases p with ⟨⟨u, v⟩, c⟩
    simp
  right_inv p := by
    rcases p with ⟨u, v⟩
    simp
  map_add' p q := by
    apply Prod.ext
    · change e (p.1.1 + q.1.1, p.2 + q.2) =
        e (p.1.1, p.2) + e (q.1.1, q.2)
      exact map_add e (p.1.1, p.2) (q.1.1, q.2)
    · rfl
  map_smul' c p := by
    apply Prod.ext
    · change e (c • p.1.1, c • p.2) = c • e (p.1.1, p.2)
      exact map_smul e c (p.1.1, p.2)
    · rfl

@[simp] theorem pointShuffle_apply (e : (A0 × F2) ≃ₗ[F2] A)
    (u : A0) (v : I) (c : F2) :
    pointShuffle (I := I) e ((u, v), c) = (e (u, c), v) := rfl

@[simp] theorem pointShuffle_symm_apply (e : (A0 × F2) ≃ₗ[F2] A)
    (u : A) (v : I) :
    (pointShuffle (I := I) e).symm (u, v) =
      (((e.symm u).1, v), (e.symm u).2) := rfl

/-- Express a function in the shuffled coordinates. -/
def pointShuffleTransport (e : (A0 × F2) ≃ₗ[F2] A)
    (f : ((A × I) →ₗ[F2] F) → ℝ) :
    (((A0 × I) × F2) →ₗ[F2] F) → ℝ :=
  fun Y => f (Y.comp (pointShuffle e).symm.toLinearMap)

end
end MaxCutGames.Inverse.KMSFourthMoment

/-!
# Restricted Fourier sums on the small space

A prescribed partial frequency is encoded by an actual linear projection of
the small codomain. This gives a coordinate-free index for the fixed-character
induction in KMS Lemma 3.19. The statements below establish its exact base
normalization and remove impossible partial frequencies.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSBasisInvariant

variable {E F I J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

/-- Squared small Fourier coefficients whose image under a prescribed linear
projection is the fixed partial frequency. -/
def fixedFrequencyEnergy (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ)
    (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) : ℝ :=
  ∑ T with π.comp T = A, smallCoeff ι f T ^ 2

end

/-!
# Transport of the small component between equivalent coordinate spaces

The embedding and partial projection are transported together. Thus the
lifted frequency and its prescribed partial value remain literally the same.
Finite reindexing proves exact coefficient, function, and restricted-energy
identities without requiring basis invariance of the original function.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters
  (linearTraceCharacter linearTraceCharacter_apply linearTracePair)

variable {E F I I' J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup I'] [Module F2 I']
  [AddCommGroup J] [Module F2 J]

/-- Reindex the actual dual frequency maps by an equivalence of their targets. -/
def smallFrequencyEquiv (e : I ≃ₗ[F2] I') : (F →ₗ[F2] I) ≃ (F →ₗ[F2] I') where
  toFun T := e.toLinearMap.comp T
  invFun T := e.symm.toLinearMap.comp T
  left_inv T := by ext x; simp
  right_inv T := by ext x; simp

@[simp] theorem smallFrequencyEquiv_apply (e : I ≃ₗ[F2] I') (T : F →ₗ[F2] I) :
    smallFrequencyEquiv e T = e.toLinearMap.comp T := rfl

end
end MaxCutGames.Inverse.KMSAnalytic

/-!
Coordinates adapted to an injected distinguished point. The complementary
subspace contains all old injected directions, so that the original injection
becomes exactly `pointLift` in the constructed coordinates.
-/

namespace MaxCutGames.Inverse.KMSPointComplement

noncomputable section
open MaxCutGames.Integration.BinaryLinear (F2)
open KMSAnalytic (pointLift)

variable {E I : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]

/-- The coordinates supplied by a complement to a nonzero point. -/
def pointEquivOfIsCompl (U : Submodule F2 E) (v : E) (hv : v ≠ 0)
    (hc : IsCompl U (Submodule.span F2 {v})) : (U × F2) ≃ₗ[F2] E :=
  ((LinearEquiv.refl F2 U).prodCongr
    (LinearEquiv.toSpanNonzeroSingleton F2 E v hv)).trans
      (Submodule.prodEquivOfIsCompl U (Submodule.span F2 {v}) hc)

@[simp] theorem pointEquivOfIsCompl_apply (U : Submodule F2 E) (v : E) (hv : v ≠ 0)
    (hc : IsCompl U (Submodule.span F2 {v})) (x : U) (c : F2) :
    pointEquivOfIsCompl U v hv hc (x, c) = (x : E) + c • v := rfl

end
end MaxCutGames.Inverse.KMSPointComplement

/-!
Exact coordinate alignment for the mixed-norm induction. A chosen fixed point
is moved to the last small coordinate, and an actual ambient complement makes
its injection a pointLift. Small-component transport identifies the resulting
functions exactly, so the next recursive estimate concerns the same law.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment

/-!
With no fixed points, the mixed energy is exactly the fixed-character energy
of the actual small component. This is the base interface between the two
KMS inductions; no norm estimate is assumed or altered by the identification.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSAnalytic

variable {A I : Type*} [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I] [Subsingleton A]

/-- The free block is the entire product when the fixed block is zero. -/
def zeroFixedEquiv : I ≃ₗ[F2] (A × I) :=
  { LinearMap.inr F2 A I with
    invFun := Prod.snd
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨a, x⟩
      exact Prod.ext (Subsingleton.elim _ _) rfl }

@[simp] theorem zeroFixedEquiv_apply (x : I) :
    zeroFixedEquiv (A := A) x = (0, x) := rfl

@[simp] theorem zeroFixedEquiv_symm_apply (a : A) (x : I) :
    (zeroFixedEquiv (A := A) (I := I)).symm (a, x) = x := rfl

end

/-!
The actual mixed-energy induction step of KMS Lemma 3.20. Previously fixed
points form A, the remaining Fourier coordinates form I, and the new fixed
point is last. The dependent graphs translate the old fixed points, which
is why the inductive bound must hold uniformly over those prescribed values.
-/

/-!
Scalar accounting for the genuine point-restriction induction. All ambient
weights remain explicit. A global rank cap R gives a dimension-independent
factor per fixed point; the proof does not assume any mixed-norm estimate.
-/

end MaxCutGames.Inverse.KMSFourthMoment

/-!
# Homogeneous restriction bounds for the KMS character induction

The restriction below samples linear maps into an actual subspace of the
output. Quantifying over injective presentations makes the bound invariant
under a choice of coordinates. This is a transparent squared-density
hypothesis, not a Fourier, inverse, or fourth-moment estimate.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSBasisInvariant

universe u v
variable {E : Type u} {F B : Type v}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup B] [Module F2 B]

/-- Every homogeneous output restriction of codimension at most `r` has the
stated actual normalized squared norm. The dimension inequality avoids
truncated subtraction in the restriction-composition step. -/
def HomogeneousRestrictionBound (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (C : Type v) [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
    [Fintype (E →ₗ[F2] C)],
    ∀ J : C →ₗ[F2] F, Function.Injective J →
      Module.finrank F2 F ≤ Module.finrank F2 C + r →
        (𝔼 X : E →ₗ[F2] C, f (J.comp X) ^ 2) ≤ ε

end
end MaxCutGames.Inverse.KMSAnalytic

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSFourthMomentZoomInvariant
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Point restrictions inherit basis invariance in the remaining coordinates.
Translations split into a shift of the fixed point and a translation of the
remaining matrix; both identities are exact, with no probability loss.
-/

/-!
A transparent local squared-density hypothesis for the new KMS point and
character inductions. The sampled maps are actual affine restrictions,
presented by a surjective domain quotient and an injective codomain map.
No Fourier, hybrid-derivative, rank-level, or inverse estimate is included.
The Grassmann application discharges this predicate from its actual local
density bounds; the analytic induction must still be proved separately.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSAnalytic

universe u v
variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

/-- All affine restrictions with at most r prescribed input/output dimensions
have normalized squared density at most ε. The dimension sum avoids any
truncated-subtraction ambiguity. -/
def AffineDensityBound (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (D : Type u) [AddCommGroup D] [Module F2 D] [FiniteDimensional F2 D]
    (C : Type v) [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
    [Fintype (D →ₗ[F2] C)],
    ∀ L : E →ₗ[F2] D, Function.Surjective L →
    ∀ J : C →ₗ[F2] F, Function.Injective J →
    ∀ T : E →ₗ[F2] F,
      Module.finrank F2 E + Module.finrank F2 F ≤
        Module.finrank F2 D + Module.finrank F2 C + r →
      (𝔼 X : D →ₗ[F2] C, f (T + J.comp (X.comp L)) ^ 2) ≤ ε

end

/-!
The local-density predicate is invariant under an ambient basis presentation
and consumes exactly the output codimension under a homogeneous restriction.
These are changes of the actual sampled affine maps, without an estimate loss.
-/

/-!
The complete fixed-point induction from the fixed-character base estimate.
The base is kept as a named mathematical input here so its separate character
induction can be assembled independently. This intermediate theorem is not
the final KMS endpoint: its base must be discharged by the proved homogeneous
character estimate. All point-recursion, basis transport and local-density
steps are established within this theorem's proof.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Inverse.KMSAnalytic

universe u v

local instance mapFintype {V : Type*} {W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

end
end MaxCutGames.Inverse.KMSFourthMoment

/-!
# Exact orbit grouping for KMS Fourier norms

The frequency fibers are finite sets with their real cardinality as the
multiplicity. No probability normalization or orbit-size estimate is assumed
by the grouping identity. The later kernel-orbit count supplies these sizes
for the actual binary linear maps.
-/

/-!
The common kernel index for binary maps of fixed rank and for surjective maps
to a fixed comparison space. Both maps below send an actual linear map to its
literal kernel; quotient dimensions follow from the first isomorphism theorem.
-/

/-!
# Fixed kernels and injective quotient maps

Linear maps with a prescribed kernel are in explicit bijection with injective
maps from the corresponding quotient. This elementary counting foundation
works over any ring, and in particular over the binary field used by KMS.
No expansion or rank-level estimate is assumed.
-/

/-!
Every kernel class is realized by both families of maps. The witnesses are
constructed from a linear equivalence of the quotient with the comparison
space, followed (for the rank family) by an injection into the ambient space.
No uniformity or fiber-count assertion is assumed.
-/

/-! Exact counts of injective binary linear maps. Evaluating a map on a
chosen domain basis is a bijection with linearly independent image families.
The count uses the proved finite-field independent-family enumeration. -/

/-!
Exact kernel-fiber cardinalities. Factoring through the actual quotient turns
the fixed-kernel fiber into injections, and a quotient equivalence identifies
these with the binary injection count. Restricting to the prescribed rank or
to surjections does not remove any member of the corresponding fiber.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSInjectionCountBounds
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary dimension bounds for the actual injection count. The lower
bound is intentionally loose; its exponent suffices for the KMS norm ratio. -/

/-!
# Exact small-component energy ratio

The small full-rank component and the large rank component have the same
Fourier value on each kernel class. Their actual multiplicities are the
numbers of injective maps into the two domain spaces. This is the counting
identity underlying the zero-fixed-character case of KMS Lemma 3.19.
-/

/-! Dimension-only real bounds for actual binary injection counts. Multiplying
by the square-dimension factor removes truncated natural subtraction from the
ambient-dimension exponent. -/

/-! The zero-fixed-character base of KMS's restricted Fourier induction,
with the actual injection-count ratio and homogeneous squared-density bound.
-/

/-!
The exact Fourier coefficient merging law for a codomain restriction. This
is the Fourier step of KMS's zoom-out recursion: the subsequent orbit argument
groups the genuine extension fiber using basis invariance. Neither an inverse
nor a rank-level estimate is a premise.
-/

/-!
# Extension fibers for a dual hyperplane

Extending a linear frequency from `B` to `B × F2` amounts to choosing one
vector. Outside the old range every extension has the same kernel. Actual
basis invariance therefore makes all these Fourier coefficients equal.
The resulting exact counting identity is the algebraic part of the
hyperplane recursion; no analytic estimate is assumed here.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier

variable {E B : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup B] [Module F2 B]

/-- Extend a frequency by specifying its value on the new coordinate. -/
def hyperplaneExtend (z : B →ₗ[F2] E) (v : E) : (B × F2) →ₗ[F2] E :=
  z.coprod (LinearMap.toSpanSingleton F2 E v)

@[simp] theorem hyperplaneExtend_apply (z : B →ₗ[F2] E) (v : E) (b : B) (c : F2) :
    hyperplaneExtend z v (b, c) = z b + c • v := rfl

@[simp] theorem hyperplaneExtend_comp_inl (z : B →ₗ[F2] E) (v : E) :
    (hyperplaneExtend z v).comp (LinearMap.inl F2 B F2) = z :=
  LinearMap.coprod_inl _ _

@[simp] theorem hyperplaneExtend_new_coordinate (z : B →ₗ[F2] E) (v : E) :
    hyperplaneExtend z v (0, 1) = v := by simp

/-- Recover a linear map from its old coordinates and its new-coordinate value. -/
theorem hyperplaneExtend_recover (S : (B × F2) →ₗ[F2] E) :
    hyperplaneExtend (S.comp (LinearMap.inl F2 B F2)) (S (0, 1)) = S := by
  have h : LinearMap.toSpanSingleton F2 E (S (0, 1)) =
      S.comp (LinearMap.inr F2 B F2) := by
    ext
    simp
  rw [hyperplaneExtend, h, LinearMap.coprod_comp_inl_inr]

/-- Exact parametrization of a restriction fiber, including dependent extensions. -/
def hyperplaneExtensionEquiv (z : B →ₗ[F2] E) :
    E ≃ {S : (B × F2) →ₗ[F2] E // S.comp (LinearMap.inl F2 B F2) = z} where
  toFun v := ⟨hyperplaneExtend z v, hyperplaneExtend_comp_inl z v⟩
  invFun S := S.1 (0, 1)
  left_inv v := hyperplaneExtend_new_coordinate z v
  right_inv S := by
    apply Subtype.ext
    change hyperplaneExtend z (S.1 (0, 1)) = S.1
    simpa only [S.2] using hyperplaneExtend_recover S.1

end
end MaxCutGames.Inverse.KMSAnalytic

/-!
The exact basis-invariant KMS zoom-out recursion. The restricted coefficient
is an actual Fourier coefficient of the homogeneous codomain restriction.
The full extension fiber is split into dependent vectors and one common
coefficient on all independent vectors; neither term is replaced by an
assumed estimate.
-/

/-! The actual squared-coefficient inequality from the KMS zoom-out recursion.
Only a finite Cauchy--Schwarz inequality is applied to the exact restriction
identity. No restricted Fourier bound is taken as a premise. -/

namespace MaxCutGames.Inverse.KMSAnalytic

/-! Exact images and dependent-extension sums after embedding a smaller
frequency space. These identities align the genuine zoom-out recurrence with
the small-component Fourier coefficients. -/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)

variable {E B J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J]

def leftEmbedding (ι : (J × F2) →ₗ[F2] E) : J →ₗ[F2] E :=
  ι.comp (LinearMap.inl F2 J F2)

theorem leftEmbedding_injective (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) : Function.Injective (leftEmbedding ι) := by
  intro x y h
  have hxy : (x, (0 : F2)) = (y, 0) := hι h
  exact congrArg Prod.fst hxy

theorem range_left_comp_of_surjective (ι : (J × F2) →ₗ[F2] E)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    ((leftEmbedding ι).comp z).range = (leftEmbedding ι).range := by
  ext v
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨z b, rfl⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨b, rfl⟩ := hz j
    exact ⟨b, rfl⟩

/-- The dependent extensions are enumerated exactly once by the small space. -/
def liftedRangeEquiv (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    J ≃ ((leftEmbedding ι).comp z).range :=
  Equiv.ofBijective
    (fun j => ⟨leftEmbedding ι j, by
      rw [range_left_comp_of_surjective ι z hz]
      exact ⟨j, rfl⟩⟩)
    ⟨by
      intro x y h
      exact leftEmbedding_injective ι hι (congrArg Subtype.val h),
      by
      rintro ⟨v, b, rfl⟩
      exact ⟨z b, rfl⟩⟩

@[simp] theorem liftedRangeEquiv_val (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) (z : B →ₗ[F2] J) (hz : Function.Surjective z) (j : J) :
    (liftedRangeEquiv ι hι z hz j).val = leftEmbedding ι j := rfl

end
end MaxCutGames.Inverse.KMSAnalytic

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSAnalyticFrequencyShift
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The dependent branches in the KMS fixed-character recursion inject into the
lower-rank restricted Fourier sum. The new coordinate value is kept fixed,
so no multiplicity or ambient-dimension loss is introduced here.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

/-! A denominator-cleared fixed-character induction step. Its right side
contains only the actual smaller restricted Fourier energies, obtained from
the exact zoom-out identity and injective reindexing of each dependent branch.
-/

/-!
# Compatible block frequencies

A compatible surjection on `B × F2` has a unique old surjection and a new
vector in the kernel of the partial projection. The new vector does not
change its kernel. Consequently actual basis-invariant Fourier coefficients
are constant along this fiber, yielding its exact energy multiplicity.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier

variable {B J K E : Type*}
  [AddCommGroup B] [Module F2 B] [AddCommGroup J] [Module F2 J]
  [AddCommGroup K] [Module F2 K] [AddCommGroup E] [Module F2 E]

/-- Adjoin a new identity coordinate and an arbitrary off-diagonal vector. -/
def blockFrequency (z : B →ₗ[F2] J) (w : J) : (B × F2) →ₗ[F2] (J × F2) :=
  (hyperplaneExtend z w).prod (LinearMap.snd F2 B F2)

@[simp] theorem blockFrequency_apply (z : B →ₗ[F2] J) (w : J) (b : B) (c : F2) :
    blockFrequency z w (b, c) = (z b + c • w, c) := rfl

theorem blockFrequency_surjective_iff (z : B →ₗ[F2] J) (w : J) :
    Function.Surjective (blockFrequency z w) ↔ Function.Surjective z := by
  constructor
  · intro h y
    obtain ⟨⟨b, c⟩, hx⟩ := h (y, 0)
    have hc : c = 0 := congrArg Prod.snd hx
    refine ⟨b, ?_⟩
    simpa only [blockFrequency_apply, hc, zero_smul, add_zero] using congrArg Prod.fst hx
  · intro h x
    obtain ⟨b, hb⟩ := h (x.1 - x.2 • w)
    refine ⟨(b, x.2), ?_⟩
    simp only [blockFrequency_apply, hb, sub_add_cancel, Prod.eta]

theorem blockFrequency_compatible_iff (π : J →ₗ[F2] K) (A : B →ₗ[F2] K)
    (z : B →ₗ[F2] J) (w : J) :
    (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp (blockFrequency z w) =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2) ↔ π.comp z = A ∧ π w = 0 := by
  constructor
  · intro h
    constructor
    · apply LinearMap.ext
      intro b
      simpa using congrArg (fun T : (B × F2) →ₗ[F2] (K × F2) => (T (b, 0)).1) h
    · simpa using congrArg (fun T : (B × F2) →ₗ[F2] (K × F2) => (T (0, 1)).1) h
  · rintro ⟨hz, hw⟩
    apply LinearMap.ext
    rintro ⟨b, c⟩
    have hb : π (z b) = A b := congrArg (fun T : B →ₗ[F2] K => T b) hz
    simp [hb, hw]

def blockOld (T : (B × F2) →ₗ[F2] (J × F2)) : B →ₗ[F2] J :=
  ((LinearMap.fst F2 J F2).comp T).comp (LinearMap.inl F2 B F2)

def blockNew (T : (B × F2) →ₗ[F2] (J × F2)) : J := (T (0, 1)).1

@[simp] theorem blockOld_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    blockOld (blockFrequency z w) = z := by
  ext b
  simp [blockOld]

@[simp] theorem blockNew_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    blockNew (blockFrequency z w) = w := by simp [blockNew]

theorem blockFrequency_recover (π : J →ₗ[F2] K) (A : B →ₗ[F2] K)
    (T : (B × F2) →ₗ[F2] (J × F2))
    (hT : (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) :
    blockFrequency (blockOld T) (blockNew T) = T := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun R : (B × F2) →ₗ[F2] J => R x)
      (hyperplaneExtend_recover ((LinearMap.fst F2 J F2).comp T))
  · have h := congrArg (fun R : (B × F2) →ₗ[F2] (K × F2) => (R x).2) hT
    exact h.symm

abbrev CompatibleBlockFrequency (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :=
  {T : (B × F2) →ₗ[F2] (J × F2) // Function.Surjective T ∧
    (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)}

abbrev CompatibleOldFrequency (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :=
  {z : B →ₗ[F2] J // Function.Surjective z ∧ π.comp z = A}

/-- The actual compatible frequency fiber, with its exact kernel-vector parameter. -/
def compatibleBlockFrequencyEquiv (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    CompatibleBlockFrequency π A ≃ CompatibleOldFrequency π A × π.ker where
  toFun T := by
    have hr := blockFrequency_recover π A T.val T.property.2
    have hc : π.comp (blockOld T.val) = A ∧ π (blockNew T.val) = 0 :=
      (blockFrequency_compatible_iff π A _ _).mp (by rw [hr]; exact T.property.2)
    refine (⟨blockOld T.val, ?_, hc.1⟩, ⟨blockNew T.val, hc.2⟩)
    apply (blockFrequency_surjective_iff (blockOld T.val) (blockNew T.val)).mp
    rw [hr]
    exact T.property.1
  invFun p := ⟨blockFrequency p.1.val p.2.val,
    (blockFrequency_surjective_iff _ _).mpr p.1.property.1,
    (blockFrequency_compatible_iff π A _ _).mpr ⟨p.1.property.2, p.2.property⟩⟩
  left_inv T := by
    apply Subtype.ext
    exact blockFrequency_recover π A T.val T.property.2
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact blockOld_blockFrequency _ _
    · apply Subtype.ext
      exact blockNew_blockFrequency _ _

end

/-! The complete product-coordinate fixed-character recurrence, with the
actual new-coordinate multiplicity. This joins the block-frequency bijection
to the genuine Fourier zoom-out energy inequality. -/

/-! Scalar closure of the genuine KMS fixed-character induction. The three
combinatorial losses are absorbed by the explicit quadratic exponent; no
Fourier estimate is asserted or assumed in this arithmetic lemma. -/

end MaxCutGames.Inverse.KMSAnalytic

/-! Quantitative closure of the genuine fixed-character product recurrence.
The hypotheses are the actual two smaller restricted energies. The proof
accounts for the kernel multiplicity and all dependent extensions explicitly.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

/-!
# Transport of the primal codomain

An equivalence of primal codomains gives a unique frequency in the Fourier
pullback fiber. The resulting exact coefficient identity transports both
the small component and its prescribed-frequency energy. No invariance or
analytic estimate is needed for these identities.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier

variable {E F F' I J : Type*}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [AddCommGroup F'] [Module F2 F']
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]

def codomainTransport (e : F ≃ₗ[F2] F') (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F') → ℝ := fun X => f (e.symm.toLinearMap.comp X)

/-- Actual dual frequencies are reindexed by precomposition with the inverse. -/
def codomainFrequencyEquiv (e : F ≃ₗ[F2] F') : (F →ₗ[F2] I) ≃ (F' →ₗ[F2] I) where
  toFun T := T.comp e.symm.toLinearMap
  invFun T := T.comp e.toLinearMap
  left_inv T := by ext x; simp
  right_inv T := by ext x; simp

@[simp] theorem codomainFrequencyEquiv_apply (e : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    codomainFrequencyEquiv e T = T.comp e.symm.toLinearMap := rfl

@[simp] theorem codomainFrequency_cancel (e : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    (T.comp e.symm.toLinearMap).comp e.toLinearMap = T := by ext x; simp

end
end MaxCutGames.Inverse.KMSAnalytic

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSAnalyticRestrictionTransport
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate and budget transport for the genuine homogeneous character
induction. These statements only change presentations of the actual local
squared-density hypothesis and prescribed Fourier sums. -/

/-!
An explicit splitting of a linear functional with a chosen unit preimage.
Both directions retain the chosen vector, permitting compatible splittings of
nested spaces and subspaces in the KMS argument.
-/

/-!
Compatible one-coordinate splittings of two surjections with a common target.
A single target coordinate is lifted through both maps. The three resulting
linear equivalences put both surjections into the product of their kernel
restriction with the identity on the binary field.
-/

/-! The full fixed-character induction for the actual KMS small component.
The only local hypothesis bounds squared norms of homogeneous restrictions;
all Fourier recursions, multiplicities and coordinate changes are proved.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSBasisInvariant

universe u v w x

local instance mapFintype {V : Type*} {W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

end
end MaxCutGames.Inverse.KMSAnalytic

/-!
The closed KMS mixed restriction estimate. The fixed-character base in the
point induction is discharged by the actual homogeneous character theorem.
Only basis invariance and the transparent local affine squared-density bound
remain; no Fourier-energy or missing-estimate premise occurs here.
-/

/-!
A uniform formulation of the genuine KMS mixed estimate. Every instance is
the actual Fourier slice of a partially restricted small component. The
property is preserved by coordinate pullback and follows from the proved
mixed estimate under the affine squared-density hypothesis.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSAnalytic
open MaxCutGames.Inverse.KMSFourthMoment

universe u v w

/-- A consistent finite enumeration of actual binary linear maps, built from
the finite vertex spaces. This is the enumeration used by the mixed theorem. -/
@[instance_reducible]
def mixedMapFintype {V W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

attribute [local instance] mixedMapFintype

variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F]

/-- All mixed small-component slices of total degree at most `r`, with their
exact ambient normalization weight. No Hybrid derivative bound is included
in this property. Fixed primal points and prescribed frequencies are arbitrary. -/
def UniformMixedBound (r : ℕ) (L : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (A I J : Type u)
    [AddCommGroup A] [Module F2 A] [FiniteDimensional F2 A] [Fintype A]
    [AddCommGroup I] [Module F2 I] [FiniteDimensional F2 I] [Fintype I]
    [AddCommGroup J] [Module F2 J] [FiniteDimensional F2 J] [Fintype J],
    ∀ (ι : (A × I) →ₗ[F2] E), Function.Injective ι →
    ∀ (a : A →ₗ[F2] F) (π : I →ₗ[F2] J), Function.Surjective π →
    ∀ (ν : F →ₗ[F2] J), Module.finrank F2 A + Module.finrank F2 I ≤ r →
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        sliceEnergy (fun T => π.comp T = ν)
          (partialRestrict (smallComponent ι f) a) ≤ L

end
end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-! The actual arbitrary-subspace hybrid energy estimate. The proof changes
both ambient spaces to complement coordinates, invokes the proved image
decomposition, and obtains every mixed slice from the actual KMS mixed
restriction theorem. No derivative or moment estimate is assumed. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSBasisComparisonPseudorandomTupleMap
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restricted tuple law is the actual linear-map lift law in coordinates,
with all singular tuples still present in the uniform denominator. -/

/-!
The KMS restricted-tuple bound in any adapted basis, followed by an exact
uniform affine translation of the free coordinates. No generic rank-level
inequality is used: this is a change of coordinates for the actual lift.
-/

/-!
Complements adapted to an affine restriction. The prescribed directions are
contained in a small summand, and the complementary directions are mapped into
the prescribed target subspace. This is ordinary finite-dimensional geometry;
no Fourier inequality or pseudorandomness hypothesis is used.
-/

/-!
The actual parameter space of an affine matrix restriction splits along a
complementary domain decomposition. The constrained coordinate is a map out of
`U / D`, while the complementary coordinate is an unrestricted map into `W`.
The equivalence transports the full uniform law to independent uniform factors.
-/

namespace MaxCutGames.Inverse.KMSAffineRestrictionSplit

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Fourier.MatrixRestrictions
open scoped BigOperators

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

/-- The original vanishing subspace viewed inside the chosen large summand. -/
abbrev localVanishing (D U : Submodule F2 E) : Submodule F2 U :=
  D.comap U.subtype

/-- The constrained component of an actual quotient parameter. -/
def splitLeft (D U : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) : Parameter (localVanishing D U) W :=
  (localVanishing D U).liftQ (A.comp (D.mkQ.comp U.subtype)) (by
    intro x hx
    change A (D.mkQ (x : E)) = 0
    have hz : D.mkQ (x : E) = 0 :=
      (Submodule.Quotient.mk_eq_zero D).mpr hx
    rw [hz, map_zero])

@[simp] theorem splitLeft_apply (D U : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) (x : U) :
    splitLeft D U W A ((localVanishing D U).mkQ x) =
      A (D.mkQ (x : E)) := rfl

/-- The free component of an actual quotient parameter. -/
def splitRight (D E₀ : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) : E₀ →ₗ[F2] W :=
  A.comp (D.mkQ.comp E₀.subtype)

@[simp] theorem splitRight_apply (D E₀ : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) (x : E₀) :
    splitRight D E₀ W A x = A (D.mkQ (x : E)) := rfl

/-- Assemble the two components before quotienting by `D`. -/
def joinMap (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hc : IsCompl U E₀) (B : Parameter (localVanishing D U) W)
    (C : E₀ →ₗ[F2] W) : E →ₗ[F2] W :=
  B.comp ((localVanishing D U).mkQ.comp (U.projectionOnto E₀ hc)) +
    C.comp (E₀.projectionOnto U hc.symm)

@[simp] theorem joinMap_apply_left (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : U) :
    joinMap D U E₀ W hc B C (x : E) = B ((localVanishing D U).mkQ x) := by
  simp [joinMap]

@[simp] theorem joinMap_apply_right (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : E₀) :
    joinMap D U E₀ W hc B C (x : E) = C x := by
  simp [joinMap]

theorem joinMap_vanishes (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    D ≤ (joinMap D U E₀ W hc B C).ker := by
  intro x hx
  let u : U := ⟨x, hDU hx⟩
  change joinMap D U E₀ W hc B C (u : E) = 0
  rw [joinMap_apply_left]
  have hz : (localVanishing D U).mkQ u = 0 :=
    (Submodule.Quotient.mk_eq_zero (localVanishing D U)).mpr hx
  rw [hz, map_zero]

/-- The actual quotient parameter reconstructed from both independent pieces. -/
def join (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) : Parameter D W :=
  D.liftQ (joinMap D U E₀ W hc B C) (joinMap_vanishes D U E₀ W hDU hc B C)

@[simp] theorem join_apply (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : E) :
    join D U E₀ W hDU hc B C (D.mkQ x) = joinMap D U E₀ W hc B C x := rfl

@[simp] theorem join_embed_apply_left (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : U) :
    embed D W (join D U E₀ W hDU hc B C) (x : E) =
      (B ((localVanishing D U).mkQ x) : F) := by
  rw [embed_apply, join_apply, joinMap_apply_left]

@[simp] theorem join_embed_apply_right (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : E₀) :
    embed D W (join D U E₀ W hDU hc B C) (x : E) = (C x : F) := by
  rw [embed_apply, join_apply, joinMap_apply_right]

theorem splitLeft_join (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    splitLeft D U W (join D U E₀ W hDU hc B C) = B := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (localVanishing D U).mkQ_surjective q
  rw [splitLeft_apply, join_apply, joinMap_apply_left]

theorem splitRight_join (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    splitRight D E₀ W (join D U E₀ W hDU hc B C) = C := by
  apply LinearMap.ext
  intro x
  rw [splitRight_apply, join_apply, joinMap_apply_right]

theorem join_split (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) (A : Parameter D W) :
    join D U E₀ W hDU hc (splitLeft D U W A) (splitRight D E₀ W A) = A := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := D.mkQ_surjective q
  obtain ⟨⟨u, v⟩, hx⟩ := (Submodule.prodEquivOfIsCompl U E₀ hc).surjective x
  change (u : E) + (v : E) = x at hx
  rw [← hx]
  simp only [map_add, join_apply, joinMap_apply_left, joinMap_apply_right,
    splitLeft_apply, splitRight_apply]

/-- Linear equivalence of the full restriction domain with the constrained
component and the free complementary component. -/
def splitEquiv (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) :
    Parameter D W ≃ₗ[F2]
      (Parameter (localVanishing D U) W × (E₀ →ₗ[F2] W)) where
  toFun A := (splitLeft D U W A, splitRight D E₀ W A)
  invFun P := join D U E₀ W hDU hc P.1 P.2
  left_inv := join_split D U E₀ W hDU hc
  right_inv P := Prod.ext (splitLeft_join D U E₀ W hDU hc P.1 P.2)
    (splitRight_join D U E₀ W hDU hc P.1 P.2)
  map_add' A B := by
    apply Prod.ext
    · apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := (localVanishing D U).mkQ_surjective q
      rfl
    · rfl
  map_smul' a A := by
    apply Prod.ext
    · apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := (localVanishing D U).mkQ_surjective q
      rfl
    · rfl

@[simp] theorem splitEquiv_symm_apply (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    (splitEquiv D U E₀ W hDU hc).symm (B, C) = join D U E₀ W hDU hc B C := rfl

instance freeFintype [Finite E] [Finite F] (E₀ : Submodule F2 E)
    (W : Submodule F2 F) : Fintype (E₀ →ₗ[F2] W) := by
  classical
  letI : Fintype E₀ := Fintype.ofFinite E₀
  letI : Fintype W := Fintype.ofFinite W
  exact Fintype.ofInjective (fun C : E₀ →ₗ[F2] W => (C : E₀ → W))
    DFunLike.coe_injective

end
end MaxCutGames.Inverse.KMSAffineRestrictionSplit

/-!
Grassmann interval pseudorandomness controls actual arbitrary affine matrix
restrictions, at twice the restriction order. The proof chooses a bounded
prefix containing the vanishing subspace and all nonhomogeneous directions,
splits the exact quotient-map parameter law, and applies the tuple estimate.
-/

namespace MaxCutGames.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open MaxCutGames.Fourier.MatrixRestrictions
open KMSAffineRestrictionSplit

variable {n ell q t : ℕ}

@[simp] theorem complementBasis_inl (U E0 : Submodule F2 (Ambient ell))
    (hc : IsCompl U E0) (bU : Module.Basis (Fin q) F2 U)
    (b0 : Module.Basis (Fin t) F2 E0) (i : Fin q) :
    complementBasis U E0 hc bU b0 (Sum.inl i) = (bU i : Ambient ell) := by
  simp [complementBasis, Module.Basis.prod_apply]

@[simp] theorem complementBasis_inr (U E0 : Submodule F2 (Ambient ell))
    (hc : IsCompl U E0) (bU : Module.Basis (Fin q) F2 U)
    (b0 : Module.Basis (Fin t) F2 E0) (i : Fin t) :
    complementBasis U E0 hc bU b0 (Sum.inr i) = (b0 i : Ambient ell) := by
  simp [complementBasis, Module.Basis.prod_apply]

/-- The affine center restricted to directions whose images already lie in W. -/
def freeCenter (E0 : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (T : BasisMap n ell) (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T)) : E0 →ₗ[F2] W :=
  (T.comp E0.subtype).codRestrict W fun x =>
    (Submodule.Quotient.mk_eq_zero W).mp (hE0 x.property)

@[simp] theorem freeCenter_coe (E0 : Submodule F2 (Ambient ell))
    (W : Submodule F2 (Ambient n)) (T : BasisMap n ell)
    (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T)) (x : E0) :
    (freeCenter E0 W T hE0 x : Ambient n) = T x := rfl

end
end MaxCutGames.Inverse.KMSAffineRestriction

/-!
An affine map family presented by a surjective input map and an injective
output map is precisely the quotient-parameter family with vanishing subspace
the input kernel and target subspace the output range. Both its uniform law
and its dimension budget agree exactly with the intrinsic restriction data.
-/

namespace MaxCutGames.Inverse.KMSAffineRestrictionPresentation

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Fourier.MatrixRestrictions
open scoped BigOperators

noncomputable section

variable {E F D C : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]

/-- Change from surjective/injective presentation coordinates to the actual
quotient-domain and subspace-target parameter. -/
def parameterEquiv (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J) :
    (D →ₗ[F2] C) ≃ₗ[F2] Parameter L.ker J.range :=
  LinearEquiv.arrowCongr (L.quotKerEquivOfSurjective hL).symm
    (LinearEquiv.ofInjective J hJ)

@[simp] theorem parameterEquiv_apply_mk (L : E →ₗ[F2] D)
    (hL : Function.Surjective L) (J : C →ₗ[F2] F)
    (hJ : Function.Injective J) (X : D →ₗ[F2] C) (x : E) :
    ((parameterEquiv L hL J hJ X) (L.ker.mkQ x) : F) = J (X (L x)) := rfl

/-- The embedded quotient parameter is the original two-sided composition. -/
@[simp] theorem embed_parameterEquiv (L : E →ₗ[F2] D)
    (hL : Function.Surjective L) (J : C →ₗ[F2] F)
    (hJ : Function.Injective J) (X : D →ₗ[F2] C) :
    embed L.ker J.range (parameterEquiv L hL J hJ X) = J.comp (X.comp L) := by
  apply LinearMap.ext
  intro x
  rfl

@[simp] theorem translate_parameterEquiv (L : E →ₗ[F2] D)
    (hL : Function.Surjective L) (J : C →ₗ[F2] F)
    (hJ : Function.Injective J) (T : E →ₗ[F2] F) (X : D →ₗ[F2] C) :
    MaxCutGames.Fourier.MatrixRestrictions.translate L.ker J.range T (parameterEquiv L hL J hJ X) =
      T + J.comp (X.comp L) := by
  rw [MaxCutGames.Fourier.MatrixRestrictions.translate, embed_parameterEquiv]

end
end MaxCutGames.Inverse.KMSAffineRestrictionPresentation

/-! The actual Grassmann local-density hypothesis discharges the affine
squared-density predicate used by the new KMS point/character inductions. -/

/-!
# Tuple pseudorandomness controls the actual affine squared density

This is the input conversion needed by the ordered-basis expansion theorem.
It starts directly from its tuple pseudorandomness assumption. All affine
intercepts and the full uniform parameter law are preserved by the checked
adapted-complement, split, and presentation equivalences.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSMomentTheorem
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual upper fourth-moment theorem for the full-rank lift of a
Grassmann set. Its hypotheses are literal tuple probabilities. The affine
sampling law, mixed estimate and hybrid derivative estimate are all discharged
by proved lemmas; there is no analytic estimate among the hypotheses. -/

/-!
The spectral cutoff step of KMS on the actual full uniform rank-one noise.
The low-level fourth-moment estimate remains an explicit input to the last
combining lemma; none of these statements asserts that estimate or expansion.
The multiplier is reused from the proved uniform-subspace kernel count.
-/

/-!
The KMS scalar and spectral conclusion with an arbitrary dimension-independent
upper-moment constant. This accommodates quantitative proofs with coarser
constants without changing the order of any dimension choices.
-/

/-! Exact finite conditioning error for bounded functions. These identities
keep the rejected mass visible when comparing all maps with independent bases.
-/

/-!
The good event for an ordered-basis rank-one update is that its functional
is nonzero and its direction lies outside the starting range. Its exact
finite cardinality gives the exceptional-mass bound without conditioning
either factor of the original uniform experiment.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

abbrev Functional (ell : ℕ) := KMS.Ambient ell →ₗ[KMS.F2] KMS.F2

instance functionalFinite (ell : ℕ) : Finite (Functional ell) :=
  Finite.of_injective (fun a : Functional ell => (a : KMS.Ambient ell → KMS.F2))
    DFunLike.coe_injective

instance functionalFintype (ell : ℕ) : Fintype (Functional ell) := Fintype.ofFinite _

/-- Actual good pairs in the unconditioned product sample space. -/
def goodParameters {n ell : ℕ} (X : BasisMap n ell) :
    Finset (Functional ell × KMS.Ambient n) :=
  (Finset.univ.filter (fun a : Functional ell => a ≠ 0)) ×ˢ
    (Finset.univ.filter (fun y : KMS.Ambient n => y ∉ X.range))

@[simp] theorem mem_goodParameters {n ell : ℕ} (X : BasisMap n ell)
    (p : Functional ell × KMS.Ambient n) :
    p ∈ goodParameters X ↔ p.1 ≠ 0 ∧ p.2 ∉ X.range := by
  simp [goodParameters]

end
end MaxCutGames.Inverse.KMSBasisComparison

/-!
Exact finite counts for the Grassmann graph comparison in Section 4.
The quotient-line parametrization is independent of any expansion theorem.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Rename
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset

@[simp] theorem equal_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (equal a b).eval input args = if a.eval input args = b.eval input args then 1 else 0 := by
  by_cases h : a.eval input args = b.eval input args
  · simp only [equal, eval, h, Nat.sub_self, Nat.zero_add, ↓reduceIte]
  · have hn : a.eval input args-b.eval input args+(b.eval input args-a.eval input args) ≠ 0 := by omega
    simp only [equal, eval, ite_eq_right h]
    exact ite_eq_right hn

@[simp] theorem le_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (le a b).eval input args = if a.eval input args ≤ b.eval input args then 1 else 0 := by
  simp [le, eval, Nat.sub_eq_zero_iff_le]

@[simp] theorem lt_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (lt a b).eval input args = if a.eval input args < b.eval input args then 1 else 0 := by
  simp [lt, eval]

def cond (c a b : Expr) : Expr := .add (.mul (positive c) a) (.mul (.zero c) b)
@[simp] theorem cond_eval (c a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (cond c a b).eval input args = if c.eval input args ≠ 0 then a.eval input args else b.eval input args := by
  simp only [cond, eval, positive_eval]; split_ifs <;> simp_all

def quotient (a b : Expr) : Expr :=
  .mul (positive b) (.sum a (le (.mul (.add (.arg 0) (.const 1)) (b.rename Nat.succ)) (a.rename Nat.succ)))

def remainder (a b : Expr) : Expr := .sub a (.mul (quotient a b) b)

def power (a : Expr) : ℕ → Expr
  | 0 => .const 1
  | n+1 => .mul (power a n) a
@[simp] theorem power_eval (a : Expr) (n : ℕ) (input : List Bool) (args : ℕ → ℕ) :
    (power a n).eval input args = (a.eval input args)^n := by
  induction n <;> simp [power, eval, pow_succ, *]

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BitValue
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset

def prefixZeros (i : Expr) : Expr := .sum i (.zero (.bit (.arg 0)))
def word (k : Expr) : Expr := .sum .length
  (.mul (.bit (.arg 0)) (equal (prefixZeros (.arg 0)) (k.rename Nat.succ)))

@[simp] theorem prefixZeros_eval (i : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (prefixZeros i).eval input args = zeroPrefix input (i.eval input args) := by
  simp only [prefixZeros, eval, bind, zeroPrefix, bitValue]
  apply sum_congr rfl
  intro j hj
  by_cases h : (input[j]?).getD false = true <;> simp [h]

@[simp] theorem word_eval (k : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (word k).eval input args = wordValue input (k.eval input args) := by
  simp [word, eval, prefixZeros_eval, equal_eval, wordValue, bitValue, bind]
  rfl

@[simp] theorem zeroPrefix_zero (input : List Bool) : zeroPrefix input 0 = 0 := by simp [zeroPrefix]
@[simp] theorem zeroPrefix_cons_succ (a : Bool) (s : List Bool) (i : ℕ) :
    zeroPrefix (a::s) (i+1) = (if a then 0 else 1)+zeroPrefix s i := by
  rw [zeroPrefix, sum_range_succ']
  simp only [bitValue_cons_zero, bitValue_cons_succ, zeroPrefix]
  cases a <;> simp [add_comm]

@[simp] theorem wordValue_nil (k : ℕ) : wordValue [] k = 0 := by simp [wordValue]

@[simp] theorem wordValue_false_zero (s : List Bool) : wordValue (false::s) 0 = 0 := by
  rw [wordValue, List.length_cons, sum_range_succ']
  simp

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_CorrectSum
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace OptimalMaxCut.CounterMachine

open scoped BigOperators
open Command

 theorem print_evaluates (len bit : Expr) (input : List Bool) :
    Within (print len bit) (initial input)
      {initial input with output := table len bit input}
      (len.timeBudget input.length+len.valueBudget input.length*
        (bit.timeBudget (input.length+len.valueBudget input.length)+
          2*bit.valueBudget (input.length+len.valueBudget input.length)+4)+1) := by
  let d : Data ℕ := initial input
  let L := len.eval input (fun _ => 0)
  let V := len.valueBudget input.length
  let M := input.length+V
  let T := bit.timeBudget M
  let W := bit.valueBudget M
  let out := table len bit input
  have hL : L ≤ V := len.eval_le input _ _ le_rfl (by simp)
  have holen : out.length = L := by simp [out, table, L]
  let state : ℕ → Data ℕ := fun i => {d.set 1 i with output := out.drop i}
  have hlen := len.correct (fun _ => 0) 1 d input.length (by omega)
    (by intro r hr; rfl) rfl le_rfl (by simp [d, initial])
  have hstart : state L = d.set 1 L := by
    simp [state, ← holen, d, initial, Data.set]
  have hloop : Within (.loop 1 (.seq (bit.compile (fun _ => 1) 2) (emit 2)))
      (state L) (state 0) (L*(T+2*W+4)+1) := by
    apply Within.loop 1 _ state L (T+2*W+3)
    · intro i hi; simp [state]
    · intro i hi
      let e := decData (state (i+1)) 1
      have heReg : e.reg = Function.update (fun _ => 0) 1 i := by
        simp [e, state, decData, Data.set, d, initial]
      have heClean : e.Clean 2 := by
        intro r hr
        rw [heReg]
        simp [show r ≠ 1 by omega]
      have heAt : e.reg 1 = i := by simp [heReg]
      have heArg : (fun u : ℕ => e.reg ((fun _ => 1) u)) = (fun _ => i) := by
        funext u; simp [heReg]
      have hc := bit.correct (fun _ => 1) 2 e M (by omega) heClean rfl
        (by change input.length ≤ M; dsimp [M]; omega)
        (by intro u; rw [heAt]; dsimp [M]; omega)
      rw [heArg] at hc
      let B := bit.eval input (fun _ => i)
      change Within _ e (e.set 2 B) T at hc
      have hemit := emit_evaluates (e.set 2 B) 2
      have hd : (e.set 2 B).set 2 0 = e := by
        rw [Data.set_set, Data.set_clean_zero heClean le_rfl]
      simp only [hd, Data.set_reg_same] at hemit
      have hh := hc.seq hemit
      have hdrop : decide (B ≠ 0) :: out.drop (i+1) = out.drop i := by
        have hi' : i < out.length := by omega
        rw [← List.getElem_cons_drop hi']
        congr 1
        simp [out, table, B]
      have hout : writeData e (decide (B ≠ 0)) = state i := by
        apply Data.ext
        · simp [writeData, heReg, state, d, initial, Data.set]
        · rfl
        · rfl
        · exact hdrop
      rw [hout] at hh
      apply hh.mono
      have hB : B ≤ W := bit.eval_le input _ M (by dsimp [M]; omega) (by intro u; dsimp [M]; omega)
      omega
  rw [hstart] at hloop
  have zend : state 0 = {initial input with output := table len bit input} := by
    simp [state, d, Data.set, initial, out]
  rw [zend] at hloop
  exact (hlen.seq hloop).mono (by

    change _ ≤ len.timeBudget input.length+V*(T+2*W+4)+1
    have := Nat.mul_le_mul_right (T+2*W+4) hL
    omega)

 theorem eraseInput_evaluates (d : Data ℕ) (hz : d.Clean 0) (hb : d.backup = []) :
    Within eraseInput d {d with input := []} (7*d.input.length+7) := by
  have hl := inputLength_evaluates d 1 0 (by omega) (hz 1 (by omega)) (hz 0 le_rfl) hb
  let state : ℕ → Data ℕ := fun i => {d.set 0 i with input := d.input.drop (d.input.length-i)}
  have hs : state d.input.length = d.set 0 d.input.length := by simp [state, Data.set]
  have hf : state 0 = {d with input := []} := by
    simp [state, Data.set_clean_zero hz le_rfl]
  have hloop : Within (.loop 0 .discard) (state d.input.length) (state 0) (2*d.input.length+1) := by
    have h := Within.loop 0 (.discard : Command ℕ) state d.input.length 1
    have heq : 2*d.input.length+1 = d.input.length*(1+1)+1 := by omega
    rw [heq]
    apply h
    · intro i hi; simp [state]
    · intro i hi
      have he : discardData (decData (state (i+1)) 0) = state i := by
        apply Data.ext
        · simp [state, discardData, decData, Data.set]
        · simp only [discardData, decData, state, Data.set]
          rw [List.tail_drop]
          congr 1
          omega
        all_goals rfl
      exact ⟨1,le_rfl, by rw [← he]; exact Evaluates.discard _⟩
  rw [hs, hf] at hloop
  exact (hl.seq hloop).mono (by omega)

end OptimalMaxCut.CounterMachine

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Divides
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

def divides (a b : Expr) : Expr := .zero (remainder b a)

def prime (n : Expr) : Expr := .mul (le (.const 2) n)
  (.zero (.sum n (.mul (le (.const 2) (.arg 0)) (divides (.arg 0) (n.rename Nat.succ)))))

def powTwo (n : Expr) : Expr := .mul (positive n)
  (.zero (.sum (.add n (.const 1))
    (.mul (prime (.arg 0)) (.mul (divides (.arg 0) (n.rename Nat.succ))
      (.zero (equal (.arg 0) (.const 2)))))))

/-- Cardinality of powers of two not exceeding an integer, hence its bit length. -/
def size (n : Expr) : Expr := .sum (.add n (.const 1)) (powTwo (.arg 0))

/-- Locate the unique power of two having the requested binary digit index.
Search is bounded by n+1; no exponentially large unary number is ever built. -/
def digitPower (n i : Expr) : Expr := .sum (.add n (.const 1))
  (.mul (.arg 0) (.mul (powTwo (.arg 0))
    (equal (size (.arg 0)) (.add (i.rename Nat.succ) (.const 1)))))

def digit (n i : Expr) : Expr := remainder (quotient n (digitPower n i)) (.const 2)

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_ListSum
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

def listSum {I : Type} (l : List I) (f : I → Expr) : Expr :=
  l.foldr (fun i s => .add (f i) s) (.const 0)
@[simp] theorem listSum_eval {I : Type} (l : List I) (f : I → Expr)
    (input : List Bool) (args : ℕ → ℕ) :
    (listSum l f).eval input args = (l.map (fun i => (f i).eval input args)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (f i).eval input args + (listSum l f).eval input args = _
    simp [ih]

noncomputable def finiteSum {I : Type} [Fintype I] (f : I → Expr) : Expr :=
  listSum Finset.univ.toList f
@[simp] theorem finiteSum_eval {I : Type} [Fintype I] (f : I → Expr)
    (input : List Bool) (args : ℕ → ℕ) :
    (finiteSum f).eval input args = ∑ i, (f i).eval input args := by
  simp [finiteSum]

/-- First successful bounded index. All searches are expanded into finite
counter loops, so the certificate does not postulate a search operation. -/
def least (bound predicate : Expr) : Expr :=
  .sum bound (.mul (.arg 0) (.mul (positive predicate)
    (.zero (.sum (.arg 0) (positive (predicate.rename (fun
      | 0 => 0
      | j+1 => j+2)))))))

end OptimalMaxCut.CounterMachine.Expr

namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

def Represented (f : List Bool → (ℕ → ℕ) → ℕ) : Prop :=
  ∃ e : Expr, ∀ input args, e.eval input args = f input args

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Information
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.ConditionalSimulation.firstInputFintype _root_.OAI.MaxCutGames.Soundness.ConditionalSimulation.secondInputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Soundness.ZeroInformation

/-! ## The observation fibre is a Cartesian product -/

/-! ## Exact weighted finite counting -/

/-! ## Position-indexed row maps -/

/-! ## Complete private-input reconstruction -/

/-- The first reconstruction receives only fixed outside occurrence/name data,
the fixed raw coefficients, and the inside occurrence draw. -/
noncomputable def reconstructFirst {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (name : O → Fin 3 → N) (insideOccurrences outsideOccurrences : P → O)
    (outsideNames : P → N) : FirstInput P R O :=
  firstInput positions single zeta0 zeta1 zeta2 omega
    (reconstructQuestion hidden insideOccurrences outsideOccurrences)
    (fun j => decodeIndex name (outsideOccurrences j) (outsideNames j))

/-- The second reconstruction receives no inside occurrence: only inside names. -/
def reconstructSecond {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (outsideOccurrences : P → O) (insideNames outsideNames : P → N) : SecondInput P R O N :=
  secondInput positions single zeta0 zeta1 zeta2 omega outsideOccurrences
    (reconstructQuestion hidden insideNames outsideNames)

end MaxCutGames.Soundness.ZeroInformation

section

open scoped BigOperators

namespace MaxCutGames.Soundness.ConditionalIncidences

def outsideRecord {P O N : Type} (K : Finset P) (name : O → Fin 3 → N)
    (sample : Draw P O) : PositionOutside K → O × N :=
  fun j => incidence name (sample j.val)

def zeroSet {P D : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (gamma : RawCoefficients J D) : Finset P :=
  J.attach.filter (fun j => gamma (some (.inr j)) = 0) |>.map ⟨Subtype.val, Subtype.val_injective⟩

theorem mem_zeroSet {P D : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (gamma : RawCoefficients J D) (j : P) :
    j ∈ zeroSet J gamma ↔ ∃ hj : j ∈ J, gamma (some (.inr ⟨j, hj⟩)) = 0 := by
  simp [zeroSet]

abbrev RawSample {P : Type} (J : Finset P) (D O : Type) :=
  RawCoefficients J D × Draw P O

/-- H fixes gamma and the outside incidence pairs. K is a deterministic function
of gamma, so including K explicitly in H gives precisely this same event. -/
abbrev RawObservationFibre {P D O N : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N) :=
  {sample : RawSample J D O // sample.1 = gamma ∧
    outsideRecord (zeroSet J gamma) name sample.2 = observed}

instance rawObservationFibreFintype {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D] [Fintype O]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N) :
    Fintype (RawObservationFibre J name gamma observed) := Fintype.ofFinite _

end MaxCutGames.Soundness.ConditionalIncidences
end

/-!
# Every partner linear map has independent raw coefficient coordinates

The coefficient index is exactly `ConditionalIncidences.RawSlot`: one global
coefficient, two coefficients at every full position, and one at every single
position.  The coordinate bijection below is for every actual partner linear
map, and its finite-uniform-law theorem has no distributional hypothesis.
-/

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_IncidenceExtraction
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Soundness.IncidenceExtraction

/-!
The next definitions separate local strategies from arbitrary joint strategies.
Each question reconstruction and each answer extraction has access to only one
player's question. A value conditioned on by an analysis may occur as a fixed
parameter of a `LocalSimulation`; it cannot become an additional random input.
-/

structure LocalSimulation
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    (inner : Game InnerQA InnerQB InnerA InnerB)
    (outer : Game OuterQA OuterQB OuterA OuterB) where
  questionA : InnerQA → OuterQA
  questionB : InnerQB → OuterQB
  answerA : InnerQA → OuterA → InnerA
  answerB : InnerQB → OuterB → InnerB
  sound : ∀ qa qb a b,
    outer.accepts (questionA qa) (questionB qb) a b →
    inner.accepts qa qb (answerA qa a) (answerB qb b)

def LocalSimulation.induced
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (s : Strategies OuterQA OuterQB OuterA OuterB) :
    Strategies InnerQA InnerQB InnerA InnerB where
  first qa := r.answerA qa (s.first (r.questionA qa))
  second qb := r.answerB qb (s.second (r.questionB qb))

end MaxCutGames.Soundness.IncidenceExtraction

/-!
This bridge connects the concrete partner projection to the actual equation/name
predicate of the incidence game. It uses no probabilistic or analytic hypotheses.
-/

/-! Canonical-row descent for every actual partner linear map. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AdviceImageLaw
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalSimulation.firstInputFintype _root_.OAI.MaxCutGames.Soundness.ConditionalSimulation.secondInputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# The exact visible-advice law for a fixed latent map

For every fixed binary-linear map `A`, including rank-deficient maps, a uniform
latent column has a uniform image in `range A`.  An explicit range/kernel
bijection proves the assertion simultaneously for every intercept and slope.
The final theorem starts with the actual pair of independently uniform linear
maps on the partner answer space and pushes it to independent uniform visible
coefficients in `W × range A`.  No full-rank or independence premise is assumed.
-/

/-!
# Concrete finite averaging for the projection upper bound

The coefficient samples here are actual functions `Fin t → (Fin m → ZMod 2)`.
Their law is the normalized finite uniform sum over all such functions. The
binomial moment formula is proved from this sum, without an independence or
binomial-distribution premise.
-/

namespace MaxCutGames.Soundness.RepeatedGameBounds

open scoped BigOperators

/-! ## Actual weighted winning probabilities under a local simulation -/

open Foundations.Games

namespace Simulation

abbrev PredicateStrategies := IncidenceExtraction.Strategies

variable {QA QB A B OA OB X Y : Type}
  [Fintype QA] [Fintype QB] [Fintype A] [Fintype B]
  [Fintype OA] [Fintype OB] [Fintype X] [Fintype Y]

/-- Pass a Boolean verifier predicate to the already checked deterministic
local-reconstruction and incidence-extraction interface. -/
def predicateGame (G : Game QA QB A B) : PredicateGame QA QB A B :=
  ⟨fun qa qb a b => G.accepts qa qb a b = true⟩

def strategyPair (s : PredicateStrategies QA QB A B) : Strategy QA QB A B :=
  (s.first, s.second)

end Simulation

/-! ## The actual named projection predicate -/

namespace ActualProjection

open IncidenceExtraction

/-- At a single coordinate, actual projection acceptance supplies an accepted
named-incidence answer with no access to the retained index. -/
theorem accepts_implies_named_incidence
    {P R O N : Type} (g : Incidence O N) (single : P → Bool)
    (qa : ZeroInformation.FirstInput P R O)
    (qb : ZeroInformation.SecondInput P R O N)
    (answerA : FirstAnswer P) (answerB : SecondAnswer P)
    (h : accepts g single qa qb answerA answerB)
    (j : P) (hj : single j = true) (name : N)
    (hname : qb.question j = Sum.inr name) :
    g.namedAccepts (qa.question j) name (answerA.2 j) (answerB.2.2 j) := by
  obtain ⟨hvalid, hone, indices, hquestions, hproject⟩ := h
  refine ⟨indices j, ?_, ?_, ?_⟩
  · have hq := congrFun hquestions j
    simp [ZeroInformation.partnerQuestion, hj, hname] at hq
    exact hq.symm
  · simpa [hone] using hvalid j
  · subst answerB
    simp [project, ZeroInformation.projectSingles, hj]

end ActualProjection

end MaxCutGames.Soundness.RepeatedGameBounds

/-! Conversion of actual binary linear points to the named projection answers. -/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AnswerBridge
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit hidden-coordinate enumeration in the actual conditional law. -/

/-!
# Weighted conditional product law for the clean coordinates

The equation distribution is arbitrary.  All identities below are identities
of finite sums of its actual weights, rather than a reduction to uniform
occurrence sampling.  The clean set is fixed by independently sampled advice;
the only subsequently exposed question data lie outside that set.  Conditioning
on such data preserves the entire joint law of the clean questions.
-/

/-!
Weighted total probability for the public clean-coordinate observation.
The observation may have zero-probability fibres. Only its positive fibres
require a conditional bound; the identity itself is proved from finite sums.
-/

/-!
The actual local simulation in Lemma 6.8 after fixing H. These reconstruction
maps consume only the first player's occurrence tuple or the second player's
name tuple. Its winning-event containment is proved from the concrete equation
and named-projection predicates.
-/

namespace MaxCutGames.Soundness.ConditionalSimulation

open Foundations.Games ConditionalIncidences IncidenceExtraction
open RepeatedGameBounds

noncomputable section

def incidenceGame {O N : Type} [Fintype O] [Fintype N]
    (g : Incidence O N) (mu : FiniteDistribution (O × N)) :
    Foundations.Games.Game O N Triple Bool :=
  Simulation.weightedGame ⟨g.namedAccepts⟩ mu

end
end MaxCutGames.Soundness.ConditionalSimulation

/-! The genuine conditional experiment is the reconstructed repeated-game law. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Concatenation
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.DescentProbability.noiseFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Gadget

section

universe u v

attribute [instance] Stage.inputAdd Stage.inputModule Stage.shiftAdd Stage.shiftModule
  Stage.inputFinite Stage.shiftFinite Stage.noiseFinite Stage.noiseNonempty

end

/-!
# Common-parent factorization before fresh orientation

This is the linear algebra in the lift-factorization lemma of v2 Section 2.
The map `gamma` is obtained from the whole parent family and the first
aggregate coordinate. It is chosen once, before any child is selected.
No rank, genericity, or independence assumption is needed for this step.
-/

/-!
# Every parent lift has one common map before the child is selected

This specializes the kernel factorization to the actual product construction.
It derives the child logical characters from a parent lift; it does not assume
independence of the lift and an incoming orientation.
-/

/-!
# Actual lifts and their descendant restrictions

Every descendant lift is constructed by a linear section of the child image.
Its detection on the child noise implies detection by the parent family on
the actual embedded noise. The common parent family is chosen before the
child index; only the image section is chosen after that index is known.
-/

universe u v

variable {k : Type u} {B : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B]

/-- Restricting a lift preserves its prescribed logical characters. -/
def Lift.restrict {s : Stage k B} {S T : Submodule k (B →ₗ[k] k)}
    (L : Lift s T) (hST : S ≤ T) : Lift s S where
  family := L.family.comp (Submodule.inclusion hST)
  agrees := by intro z h; exact L.agrees _ h

end MaxCutGames.Gadget

/-!
# Fresh finite orientations

The rank is fixed before the fresh isomorphism is sampled.  The finite
counting identities below do not require the subsequent lift to be independent
of that isomorphism.  In particular, an event concerning the oriented subspace
may be tested after arbitrary earlier choices have been fixed.
-/

noncomputable section

open scoped BigOperators
open Module

namespace MaxCutGames.Gadget.Orientation

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

instance rankSpaceAction (r : ℕ) : MulAction (V ≃ₗ[K] V) (RankSpace K V r) where
  smul a E := ⟨E.val.map a.toLinearMap, (a.finrank_map_eq E.val).trans E.property⟩
  one_smul E := by
    apply Subtype.ext
    exact E.val.map_id
  mul_smul a b E := by
    apply Subtype.ext
    exact E.val.map_comp b.toLinearMap a.toLinearMap

variable {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U]

/-- Choosing a reference isomorphism identifies all orientations with the
automorphism group of the target. -/
def orientationEquiv (J₀ : B ≃ₗ[K] U) : (B ≃ₗ[K] U) ≃ (U ≃ₗ[K] U) where
  toFun J := J₀.symm.trans J
  invFun a := J₀.trans a
  left_inv J := by ext x; simp
  right_inv a := by ext x; simp

/-- Dualization is a bijection on finite-dimensional isomorphisms.  This
connects uniform primal orientations to uniform character-space orientations. -/
def dualOrientationEquiv [FiniteDimensional K B] [FiniteDimensional K U] :
    (B ≃ₗ[K] U) ≃ (Module.Dual K U ≃ₗ[K] Module.Dual K B) where
  toFun J := J.dualMap
  invFun e := ((Module.evalEquiv K B).trans e.dualMap).trans (Module.evalEquiv K U).symm
  left_inv J := by
    ext b
    apply (Module.evalEquiv K U).injective
    ext φ
    simp
  right_inv e := by
    ext φ b
    simp

end MaxCutGames.Gadget.Orientation
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_OrientationVectors
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Fresh orientations of nonzero perturbations

This is the nonzero-symbol uniformity step in the latent-noise recurrence.
The perturbation is fixed before the orientation, and zero is excluded from
both sample spaces explicitly.
-/

namespace MaxCutGames.Quadratic

section

variable {F : Type*} [Field F]

theorem dot_smul_left (v y : Vec F) (t : F) : dot (t • v) y = t * dot v y := by
  simp [dot, smul_eq_mul]
  ring

variable [CharP F 2]

/-- Every cross-term arising from a shift along `Fv` is perpendicular to `v`. -/
theorem dot_D_smul (v x : Vec F) (t : F) : dot v (D x (t • v)) = 0 := by
  change v 0 * (x 1 * (t * v 2) + (t * v 1) * x 2) +
      v 1 * (x 0 * (t * v 2) + (t * v 0) * x 2) +
      v 2 * (x 0 * (t * v 1) + (t * v 0) * x 1) = 0
  calc
    _ = (t * (v 0 * v 2 * x 1 + v 0 * v 1 * x 2 + v 1 * v 2 * x 0)) +
        (t * (v 0 * v 2 * x 1 + v 0 * v 1 * x 2 + v 1 * v 2 * x 0)) := by ring
    _ = 0 := CharTwo.add_self_eq_zero _

theorem D_mem_hyperplane (v x a : Vec F) (ha : a ∈ line v) :
    D x a ∈ hyperplane v := by
  obtain ⟨t, rfl⟩ := (mem_line_iff v a).mp ha
  exact dot_D_smul v x t

variable [Algebra (ZMod 2) F]

theorem pair_mem_U (v a w : Vec F) (ha : a ∈ line v) (hw : w ∈ hyperplane v) :
    (a, Q a + w) ∈ U v := by
  refine ⟨ha, ?_⟩
  change dot v (Q a + w + Q a) = 0
  have h : Q a + w + Q a = w + (Q a + Q a) := by ac_rfl
  simpa [h] using hw

end

/-! Exact field-line count for the quadratic block's erasure probability. -/

section

variable {F : Type*} [Field F]

theorem lineGenerator_ne_zero (A : FieldLine F) : lineGenerator A ≠ 0 :=
  A.rep_nonzero

theorem line_lineGenerator (A : FieldLine F) : line (lineGenerator A) = A.submodule :=
  A.submodule_eq.symm

variable [Finite F]

/-- The denominator of the block erasure probability is exactly `q²+q+1`. -/
theorem card_FieldLine : Nat.card (FieldLine F) = Nat.card F ^ 2 + Nat.card F + 1 := by
  have h := Projectivization.card_of_finrank F (Vec F) (n := 3)
    (Module.finrank_fin_fun (R := F))
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, add_comm, add_left_comm, add_assoc] using h

theorem card_FieldLine_pos : 0 < Nat.card (FieldLine F) := by
  rw [card_FieldLine]
  exact Nat.succ_pos _

end

/-! The binary-linear parametrization and dimension of the quadratic block. -/

section

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev lineBinary (v : Vec F) : Submodule (ZMod 2) (Vec F) :=
  (line v).restrictScalars (ZMod 2)

abbrev hyperplaneBinary (v : Vec F) : Submodule (ZMod 2) (Vec F) :=
  (hyperplane v).restrictScalars (ZMod 2)

omit [Algebra (ZMod 2) F] in
theorem Q_cancel_inline_BlockDimension (a w : Vec F) : Q a + (w + Q a) = w := by
  calc
    _ = w + (Q a + Q a) := by ac_rfl
    _ = w := by rw [vec_add_self, add_zero]

/-- The parametrization `(a,w) ↦ (a,Q(a)+w)` is a binary-linear bijection.
It is not asserted to be field-linear: squaring along a field line is only
binary-linear. -/
def blockParametrization (v : Vec F) :
    (lineBinary v × hyperplaneBinary v) ≃ₗ[ZMod 2] U v where
  toFun p := ⟨((p.1 : Vec F), Q (p.1 : Vec F) + (p.2 : Vec F)),
    pair_mem_U v p.1 p.2 p.1.2 p.2.2⟩
  invFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2 + Q p.1.1, p.2.2⟩)
  left_inv := by
    intro p
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change Q (p.1 : Vec F) + (p.2 : Vec F) + Q (p.1 : Vec F) = p.2
      have h : Q (p.1 : Vec F) + (p.2 : Vec F) + Q (p.1 : Vec F) =
          Q (p.1 : Vec F) + ((p.2 : Vec F) + Q (p.1 : Vec F)) := by rw [add_assoc]
      rw [h, Q_cancel_inline_BlockDimension]
  right_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Q_cancel_inline_BlockDimension p.1.1 p.1.2
  map_add' := by
    intro p q
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Q ((p.1 : Vec F) + (q.1 : Vec F)) + ((p.2 : Vec F) + (q.2 : Vec F)) =
        (Q (p.1 : Vec F) + (p.2 : Vec F)) + (Q (q.1 : Vec F) + (q.2 : Vec F))
      rw [Q_add_of_mem_line v p.1 q.1 p.1.2 q.1.2]
      ac_rfl
  map_smul' := by
    intro c p
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · apply Subtype.ext
      apply Prod.ext <;> simp [Q_zero]
    · simp

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem dotLinear_ker (v : Vec F) : LinearMap.ker (dotLinear v) = hyperplane v := rfl

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem dotLinear_surjective (v : Vec F) (hv : v ≠ 0) :
    Function.Surjective (dotLinear v) := by
  classical
  have hi : ∃ i : Fin 3, v i ≠ 0 := by
    by_cases h : ∀ i, v i = 0
    · exact False.elim (hv (funext h))
    · exact not_forall.mp h
  obtain ⟨i, hi⟩ := hi
  intro z
  refine ⟨Pi.single i (z / v i), ?_⟩
  have hsingle (j : Fin 3) (a : F) : dot v (Pi.single j a) = v j * a := by
    fin_cases j <;> simp [dot]
  change dot v (Pi.single i (z / v i)) = z
  rw [hsingle]
  calc
    v i * (z / v i) = (v i * (v i)⁻¹) * z := by ring
    _ = z := by rw [mul_inv_cancel₀ hi, one_mul]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem finrank_hyperplane (v : Vec F) (hv : v ≠ 0) :
    Module.finrank F (hyperplane v) = 2 := by
  have h := (dotLinear v).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (dotLinear_surjective v hv),
    finrank_top, Module.finrank_self, dotLinear_ker,
    Module.finrank_fin_fun] at h
  omega

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem finrank_line (v : Vec F) (hv : v ≠ 0) :
    Module.finrank F (line v) = 1 :=
  finrank_span_singleton hv

variable [FiniteDimensional (ZMod 2) F]

omit [CharP F 2] in
theorem finrank_lineBinary (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (lineBinary v) = Module.finrank (ZMod 2) F := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F (lineBinary v),
    ((line v).restrictScalarsEquiv (ZMod 2)).finrank_eq, finrank_line v hv, mul_one]

omit [CharP F 2] in
theorem finrank_hyperplaneBinary (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (hyperplaneBinary v) = 2 * Module.finrank (ZMod 2) F := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F (hyperplaneBinary v),
    ((hyperplane v).restrictScalarsEquiv (ZMod 2)).finrank_eq, finrank_hyperplane v hv,
    mul_comm]

/-- If the field has binary dimension `d`, every nonzero-generator block has
binary dimension `3d`, the dimension of its input/output alphabet. -/
theorem finrank_U (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (U v) = 3 * Module.finrank (ZMod 2) F := by
  rw [← (blockParametrization v).finrank_eq, Module.finrank_prod,
    finrank_lineBinary v hv, finrank_hyperplaneBinary v hv]
  omega

theorem finrank_U_eq_finrank_vec (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (U v) = Module.finrank (ZMod 2) (Vec F) := by
  rw [finrank_U v hv, ← Module.finrank_mul_finrank (ZMod 2) F (Vec F),
    Module.finrank_fin_fun, mul_comm]

end

section

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

noncomputable instance fieldLineFintype : Fintype (FieldLine F) := Fintype.ofFinite _

instance finiteBlockOrientation (A : FieldLine F) : Finite (BlockOrientation A) :=
  DFunLike.finite _

noncomputable instance blockOrientationFintype (A : FieldLine F) :
    Fintype (BlockOrientation A) := Fintype.ofFinite _

/-- Existence uses the proved dimension of the actual quadratic block. -/
noncomputable def chosenBlockOrientation (A : FieldLine F) : BlockOrientation A :=
  LinearEquiv.ofFinrankEq (Vec F) (U (lineGenerator A))
    (finrank_U_eq_finrank_vec (lineGenerator A) (lineGenerator_ne_zero A)).symm

/-- Composing with one fixed orientation identifies all orientations with
automorphisms of the common binary alphabet. -/
noncomputable def blockOrientationEquiv (A : FieldLine F) :
    BlockOrientation A ≃ (Vec F ≃ₗ[ZMod 2] Vec F) where
  toFun J := J.trans (chosenBlockOrientation A).symm
  invFun J := J.trans (chosenBlockOrientation A)
  left_inv J := by
    apply LinearEquiv.ext
    intro x
    exact (chosenBlockOrientation A).apply_symm_apply (J x)
  right_inv J := by
    apply LinearEquiv.ext
    intro x
    exact (chosenBlockOrientation A).symm_apply_apply (J x)

noncomputable def blockOrientationIndexEquiv :
    BlockOrientationIndex F ≃ FieldLine F × (Vec F ≃ₗ[ZMod 2] Vec F) where
  toFun p := (p.1, blockOrientationEquiv p.1 p.2)
  invFun p := ⟨p.1, (blockOrientationEquiv p.1).symm p.2⟩
  left_inv := by
    rintro ⟨A, J⟩
    simp
  right_inv := by
    rintro ⟨A, J⟩
    simp

end

/-!
# Exact nonlinear change count for a quadratic block

For every fixed input, a shear of the line/hyperplane parametrization makes
the output difference the hyperplane coordinate. This proves the uniform
change count before any recursion or random orientation is introduced.
-/

section

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The block's nonlinear observable. -/
def blockObservable (p : Vec F × Vec F) : Vec F := p.2 + Q p.1

omit [Algebra (ZMod 2) F] in
theorem blockObservable_difference (p u : Vec F × Vec F) :
    blockObservable (p + u) + blockObservable p =
      u.2 + Q u.1 + D p.1 u.1 := by
  change (p.2 + u.2) + Q (p.1 + u.1) + (p.2 + Q p.1) = _
  rw [Q_add]
  calc
    _ = u.2 + Q u.1 + D p.1 u.1 + (p.2 + p.2) + (Q p.1 + Q p.1) := by
      ac_rfl
    _ = _ := by rw [vec_add_self, vec_add_self, add_zero, add_zero]

/-- Translation by the polar term permutes the vertical hyperplane. -/
def hyperplaneNoiseShift (v x a : Vec F) (ha : a ∈ line v) :
    hyperplane v ≃ hyperplane v where
  toFun w := ⟨(w : Vec F) + D x a,
    (hyperplane v).add_mem w.property (D_mem_hyperplane v x a ha)⟩
  invFun w := ⟨(w : Vec F) + D x a,
    (hyperplane v).add_mem w.property (D_mem_hyperplane v x a ha)⟩
  left_inv w := by
    apply Subtype.ext
    change ((w : Vec F) + D x a) + D x a = w
    rw [add_assoc, vec_add_self, add_zero]
  right_inv w := by
    apply Subtype.ext
    change ((w : Vec F) + D x a) + D x a = w
    rw [add_assoc, vec_add_self, add_zero]

/-- The polar shear preserves the first coordinate and is its own inverse. -/
def noiseParameterShift (v x : Vec F) :
    (lineBinary v × hyperplaneBinary v) ≃ (lineBinary v × hyperplaneBinary v) where
  toFun p := (p.1, hyperplaneNoiseShift v x p.1 p.1.property p.2)
  invFun p := (p.1, hyperplaneNoiseShift v x p.1 p.1.property p.2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change ((p.2 : Vec F) + D x p.1) + D x p.1 = p.2
      rw [add_assoc, vec_add_self, add_zero]
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change ((p.2 : Vec F) + D x p.1) + D x p.1 = p.2
      rw [add_assoc, vec_add_self, add_zero]

/-- Coordinates in which the nonlinear output difference is just the second
coordinate, for every fixed input `x`. -/
def blockNoiseCoordinates (v x : Vec F) : U v ≃ (lineBinary v × hyperplaneBinary v) :=
  (blockParametrization v).toEquiv.symm.trans (noiseParameterShift v x)

theorem blockObservable_difference_eq_noiseCoordinate
    (v : Vec F) (p : Vec F × Vec F) (u : U v) :
    blockObservable (p + (u : Vec F × Vec F)) + blockObservable p =
      ((blockNoiseCoordinates v p.1 u).2 : Vec F) :=
  blockObservable_difference p u

omit [Algebra (ZMod 2) F] in
theorem vec_add_eq_zero_iff_inline_BlockNoise (x y : Vec F) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg (fun z : Vec F => z + y) h
    simpa only [add_assoc, vec_add_self, add_zero, zero_add] using h'
  · rintro rfl
    exact vec_add_self _

theorem blockObservable_changes_iff (v : Vec F) (p : Vec F × Vec F) (u : U v) :
    blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p ↔
      (blockNoiseCoordinates v p.1 u).2 ≠ 0 := by
  apply not_congr
  rw [← vec_add_eq_zero_iff_inline_BlockNoise, blockObservable_difference_eq_noiseCoordinate]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg (fun w : hyperplaneBinary v => (w : Vec F)) h

theorem blockObservable_change_ne_zero (v : Vec F) (p : Vec F × Vec F) (u : U v)
    (h : blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p) : u ≠ 0 := by
  intro hu
  subst u
  exact h (by simp)

/-- Changed perturbations correspond exactly to an arbitrary line coordinate
and a nonzero hyperplane coordinate. In particular this is uniform in `p`. -/
def changedCoordinatesEquiv (v : Vec F) (p : Vec F × Vec F) :
    {u : U v // blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} ≃
      (lineBinary v × {w : hyperplaneBinary v // w ≠ 0}) :=
  ((blockNoiseCoordinates v p.1).subtypeEquiv
    (p := fun u : U v =>
      blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p)
    (q := fun u : lineBinary v × hyperplaneBinary v => u.2 ≠ 0)
    (fun u => blockObservable_changes_iff v p u)).trans
    { toFun := fun u => (u.1.1, ⟨u.1.2, u.2⟩)
      invFun := fun u => ⟨(u.1, u.2.1), u.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end

/-! Exact rational expectation for the quadratic block's conditioned noise. -/

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The uniform noise space after conditioning the perturbation to be nonzero. -/
abbrev NonzeroBlock (v : Vec F) := {u : U v // u ≠ 0}

/-- Exact uniform expectation of the nonlinear-change indicator. -/
def nonzeroBlockChangeProbability (v : Vec F) (p : Vec F × Vec F) : ℚ := by
  classical
  exact Finset.univ.expect fun u : NonzeroBlock v =>
    if blockObservable (p + (u.val : Vec F × Vec F)) ≠ blockObservable p then 1 else 0

/-- The zero perturbation is never a changed perturbation, so conditioning
does not remove any element from the change event. -/
def conditionedChangedEquiv (v : Vec F) (p : Vec F × Vec F) :
    {u : NonzeroBlock v //
      blockObservable (p + (u.val : Vec F × Vec F)) ≠ blockObservable p} ≃
    {u : U v // blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} where
  toFun u := ⟨u.val.val, u.property⟩
  invFun u := ⟨⟨u.val, blockObservable_change_ne_zero v p u.val u.property⟩, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MaxCutGames.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_OrientedBlockKernel
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators

namespace MaxCutGames.Gadget.OrientedBlockKernel

open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The actual binary-linear embedding belonging to an oriented child. -/
def orientedBlockLinear (i : BlockOrientationIndex F) :
    Vec F →ₗ[ZMod 2] Vec F × Vec F :=
  (U (lineGenerator i.1)).subtype.comp i.2.toLinearMap

/-- The nonlinear-change indicator for the actual oriented quadratic block. -/
def orientedBlockChange (i : BlockOrientationIndex F) (p : Vec F × Vec F)
    (d : Vec F) : ℚ := by
  classical
  exact if blockObservable (p + orientedBlockLinear i d) ≠ blockObservable p then 1 else 0

end MaxCutGames.Gadget.OrientedBlockKernel
end

namespace MaxCutGames.Quadratic

/-!
# Trace coordinates for families of binary characters

The trace pairing identifies the binary dual of `F³` with `F³` itself.  Its
inverse is linear, so a common-parent family of binary functionals produces
one binary-linear lift `g`, as required by the all-lifts genericity theorem.
-/

/-!
# The binary trace annihilator of a quadratic-block hyperplane

The trace annihilator of the field hyperplane perpendicular to a nonzero
vector is exactly its field line.  Scaling test vectors first upgrades binary
trace orthogonality to field-valued orthogonality; explicit coordinate test
vectors then identify the annihilator.  No earlier gadget result is used.
-/

/-!
# Character kernels on quadratic blocks

The character with horizontal coefficient `g` and vertical coefficient `z`
annihilates the block attached to `Fz` precisely when the alignment
equation holds.  The predicate below is annihilation of the actual binary
submodule, rather than an abstract replacement for that condition.
-/

section

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Literal annihilation of every vector in the block attached to `v`. -/
def BlockAnnihilates (g z v : Vec F) : Prop :=
  ∀ p ∈ U v, blockCharacter g z p = 0

omit [Finite F] in
/-- The binary block is independent of the nonzero generator of its field line. -/
theorem U_smul_ne_zero (v : Vec F) {t : F} (ht : t ≠ 0) : U (t • v) = U v := by
  have hl : line (t • v) = line v :=
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ht) v
  ext p
  simp only [mem_U, hl, dot_smul_left, mul_eq_zero, ht, false_or]

omit [Finite F] in
theorem U_eq_of_nonzero_mem_line {v z : Vec F} (hz : z ≠ 0)
    (hm : z ∈ line v) : U z = U v := by
  obtain ⟨t, rfl⟩ := (mem_line_iff v z).mp hm
  have ht : t ≠ 0 := by
    intro ht
    apply hz
    simp [ht]
  exact U_smul_ne_zero v ht

end

section

open Module
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The complete genericity predicate. The universal linear
map quantifier occurs inside the property of the selected subspace. -/
def IsGeneric (S : Submodule (ZMod 2) (Fin 3 → F)) : Prop := by
  classical
  exact
    (∀ z w : S, z ≠ 0 → w ≠ 0 →
      (∃ t : F, (z : Fin 3 → F) = t • (w : Fin 3 → F)) → z = w) ∧
    (∀ g : S →ₗ[ZMod 2] (Fin 3 → F),
      (alignmentEvent (R := ZMod 2) (fun z : S => (z : Fin 3 → F)) g
        (fun z : S => alignmentRightHandSide (z : Fin 3 → F))).card ≤
          3 * Module.finrank (ZMod 2) S)

end

/-!
# Rank-loss accounting for quadratic blocks

A nonzero kernel character determines the field line of a lossy block.  On
a generic space there is at most one such character on each field line, so
the rank drops by at most one.  Counting the possible determining characters
also bounds the number of lossy lines.  These are deterministic statements;
the random orientation may be selected only after this data is fixed.
-/

end MaxCutGames.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_BlockRestriction
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Actual child restriction maps

A common-parent lift `g` gives a binary linear map from its logical character
space into the dual of each quadratic block.  Its kernel is literal character
annihilation, so the trace calculation and the all-lifts genericity predicate
apply directly to this map.
-/

/-!
# At most `3r` actual lossy field lines

The genericity bound applies to the common-parent lift before a line or an
orientation is chosen.  A nonzero kernel character determines exactly one
projective field line, and its actual kernel equation implies alignment.
-/

namespace MaxCutGames.Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance instFintypeFieldLine : Fintype (FieldLine F) := Fintype.ofFinite _
local instance instFintypeSubtypeVecMemSubmoduleZModOfNatNat (S : Submodule (ZMod 2) (Vec F)) : Fintype S := by
  classical
  exact Subtype.fintype (Membership.mem S)

/-- A total projective-line map; the default is irrelevant on nonzero characters. -/
def characterFieldLine (A₀ : FieldLine F) (z : Vec F) : FieldLine F := by
  classical
  exact if hz : z = 0 then A₀ else Projectivization.mk F z hz

/-- All maps have the same binary dual codomain, despite their different blocks. -/
def fieldLineRestrictions (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A) :
    FieldLine F → S →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2) :=
  fun A => orientedBlockRestriction S g (lineGenerator A) (J A)

end MaxCutGames.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_HarmonicLoss
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Harmonic loss for the actual quadratic child maps

The probabilistic hypotheses of the MaxCutGames.Gadget.Harmonic.harmonic accounting lemmas are discharged
here by the proved field-line kernel criterion and genericity count.
-/

namespace MaxCutGames.Quadratic

open scoped BigOperators
open MaxCutGames.Gadget.Harmonic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance instFintypeFieldLine_1 : Fintype (FieldLine F) := Fintype.ofFinite _
local instance instFintypeSubtypeVecMemSubmoduleZModOfNatNat_1 (S : Submodule (ZMod 2) (Vec F)) : Fintype S := by
  classical
  exact Subtype.fintype (Membership.mem S)

def fieldLineTheta (F : Type*) [Field F] [Finite F] : ℚ :=
  (Nat.card (FieldLine F) : ℚ)⁻¹

/-- The image dimension of the actual oriented child restriction map. -/
def nextBlockRank (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (A : FieldLine F) : ℕ :=
  Module.finrank (ZMod 2) (fieldLineRestrictions S g J A).range

end MaxCutGames.Quadratic

/-!
# Outgoing MaxCutGames.Gadget.Harmonic.harmonic loss for the actual adaptive child map

Uniform sampling of the concrete pair `(field line, binary orientation)` has
the uniform field-line marginal. The child rank is independent of orientation,
so the proved quadratic kernel count gives the outgoing conditional loss for
the common map produced by every parent lift.
-/

namespace MaxCutGames.Gadget.OutgoingHarmonic

open Quadratic OrientedBlockKernel BlockDescent Harmonic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance instFiniteLinearEquivZModOfNatNatIdVec : Finite (Vec F ≃ₗ[ZMod 2] Vec F) := DFunLike.finite _
local instance instFintypeLinearEquivZModOfNatNatIdVec : Fintype (Vec F ≃ₗ[ZMod 2] Vec F) := Fintype.ofFinite _

def outgoingLoss (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) : ℚ :=
  average (fun i : BlockOrientationIndex F => MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
    MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ i).range))

end MaxCutGames.Gadget.OutgoingHarmonic

/-!
# The finite nongeneric fraction

This definition records the actual uniform event on the rank-indexed
Grassmannian. Its quantitative bounds are proved in GenericSubspaceProbability;
orientation arguments can use the definition independently of that proof.
-/

section

open MaxCutGames.Gadget.Orientation

namespace MaxCutGames.Quadratic

/-- The actual uniform fraction of nongeneric rank-`r` binary subspaces. -/
def nongenericFraction (F : Type*) [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] (r : ℕ) : ℚ :=
  (Nat.card {S : RankSpace (ZMod 2) (Fin 3 → F) r // ¬IsGeneric S.1} : ℚ) /
    Nat.card (RankSpace (ZMod 2) (Fin 3 → F) r)

end MaxCutGames.Quadratic
end

section

open scoped BigOperators Classical
open Module

namespace MaxCutGames.Gadget.FreshGenericity

open _root_.OAI.MaxCutGames.Gadget.Orientation Quadratic BlockDescent OrientedBlockKernel

section RankTransport

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

attribute [local instance] OAI.MaxCutGames.Gadget.FreshGenericity.linearMapFintype
attribute [local instance] OAI.MaxCutGames.Gadget.FreshGenericity.linearEquivFintype
attribute [local instance] OAI.MaxCutGames.Gadget.FreshGenericity.submoduleFintype
local instance rankSpaceFintype [Fintype V] (r : ℕ) : Fintype (RankSpace K V r) :=
  inferInstanceAs (Fintype {S : Submodule K V // finrank K S = r})

end RankTransport

attribute [local instance] linearMapFintype linearEquivFintype submoduleFintype rankSpaceFintype

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Nongenericity includes the universal lift quantifier in `IsGeneric`.
The field's simultaneous bound includes rank zero as well. -/
def bad (S : Submodule (ZMod 2) (BinaryDual (F := F))) : Prop :=
  ¬ IsGeneric (traceSpace S)

end MaxCutGames.Gadget.FreshGenericity
end

/-!
# Harmonic potential for the actual recursively selected lifts

This is the adaptive induction on the concrete descendant lift construction.
The first outgoing step may begin at a bad subspace; every later orientation
is fresh. Accordingly the bound has one initial bad-space penalty, which
vanishes for the fixed generic top subspace.
-/

namespace MaxCutGames.Gadget.LeafDetection

open Harmonic Descent DescentProbability

universe v

variable {B I X : Type v}
variable [AddCommGroup B] [Module (ZMod 2) B] [Finite B] [FiniteDimensional (ZMod 2) B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module (ZMod 2) X]

variable (J : I → B →ₗ[ZMod 2] X × B)
variable (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable def survivalProbability (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) : ℚ :=
  probability (fun t => 0 < leafRank J hJ Q n S L t)

noncomputable def detectionProbability (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) : ℚ := by
  classical
  exact probability (fun t => ∃ z : S, L.family z ((Stage.iterate J hJ Q n).noise t) ≠ 0)

omit [FiniteDimensional (ZMod 2) B] in
@[simp] theorem survivalProbability_zero
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q 0) S) :
    survivalProbability J hJ Q 0 S L =
      if 0 < Module.finrank (ZMod 2) S then 1 else 0 := by
  change average (fun _ : (Stage.iterate J hJ Q 0).Noise =>
    if 0 < Module.finrank (ZMod 2) S then (1 : ℚ) else 0) = _
  exact average_const _

end MaxCutGames.Gadget.LeafDetection

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_BaseDetection
attribute [-instance] _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Gadget.Quotient

variable {𝕜 P B : Type*} [Ring 𝕜]
variable [AddCommGroup P] [Module 𝕜 P] [AddCommGroup B] [Module 𝕜 B]

/-- Translation by the logical kernel parametrizes a quotient fiber. -/
def fiberMap (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (a : P) :
    shiftKernel R lam → {u : P // projection R lam u = projection R lam a} :=
  fun h => ⟨a + (h : P), by
    have hh : projection R lam (h : P) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr h.property
    rw [map_add, hh, add_zero]⟩

end MaxCutGames.Gadget.Quotient

/-!
# From full character lifts to linear-map detection

If a target linear map is injective on the logical alphabet, a linear left
inverse of that restriction turns all logical characters into a full lift.
Detection by this lift implies that the target map does not annihilate the
noise. The left inverse is proved to exist by the vector-space splitting
theorem; it is not an additional premise.
-/

/-!
# Detection survives the logical-kernel quotient

A full family of logical characters on the quotient pulls back to a full
lift on the original stage. Its detection event is the same pointwise.
Combining this with the proved left-inverse construction gives detection of
every linear map injective on the quotient's logical subspace.
-/

namespace MaxCutGames.Gadget.QuotientDetection

open Harmonic DetectionBridge
open scoped Classical

universe u v

variable {k : Type u} {B : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B]

noncomputable def pullbackFullLift (s : Stage k B)
    (ψ : Module.Dual k B →ₗ[k] Module.Dual k (StageQuotient.Space s))
    (hψ : IsFullLift (StageQuotient.shift s) ψ) :
    Lift s (⊤ : Submodule k (Module.Dual k B)) where
  family :=
    { toFun z := (ψ z.val).comp (StageQuotient.projection s)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  agrees := by
    intro z h
    change ψ z.val (StageQuotient.projection s (s.embed h)) = z.val (s.logical h)
    rw [← StageQuotient.shift_logical]
    exact hψ z.val (s.logical h)

end MaxCutGames.Gadget.QuotientDetection

namespace MaxCutGames.Gadget.NonlinearRecurrence

open scoped BigOperators

variable {k I P R X B : Type*} [CommRing k]
variable [Fintype I] [DecidableEq I]
variable [AddCommGroup P] [Module k P] [Fintype P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X] [Fintype X]
variable [AddCommGroup B] [Module k B] [Fintype B] [DecidableEq B]

omit [Fintype X] [Fintype B] in
@[simp] theorem change_zero (F : X × B → B) (p : X × B) : change F p 0 = 0 := by
  simp [change]

end MaxCutGames.Gadget.NonlinearRecurrence

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Generator
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP

namespace ConstraintGraph

variable {V E A : Type*}

theorem mem_rejectedDarts [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    e ∈ G.rejectedDarts labeling ↔ G.edgeSatisfied labeling e = false := by
  simp [rejectedDarts]

end ConstraintGraph

end MaxCutGames.Foundations.PCP

/-!
# Executable directed-dart tables for the fixed 64-label alphabet

The header gives vertex and dart counts. Every dart has one ordered row:
tail index, reverse-dart index, and 4096 Boolean predicate entries. Entry
`b + 64 * a` is the predicate at labels `(a,b)`. All fields, including bits
as 0/1 words, use the existing zero-delimited unary natural-word codec.

The decoder checks all index bounds, row counts, predicate lengths, reverse
involution, predicate transpose, and absence of trailing fields. Directed rows
preserve loops, self-reversing darts, and repeated constraint occurrences.
The size theorems concern the full encoded table, not a machine runtime.
-/

namespace MaxCutGames.Foundations.PCP.GraphTables

open MaxCutGames.Foundations.Complexity

theorem enumeratedGraph_edgeSatisfied {V E A : Type*} {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ Label) (labeling : V → A) (e : E) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).edgeSatisfied
      (fun v => labelOrder (labeling (vertexOrder.symm v))) (dartOrder e) =
        G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head, enumeratedGraph]

/-- Every directed occurrence contributes once before and after enumeration. -/
theorem enumeratedGraph_rejectionCount {V E A : Type*} [Fintype E] {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ Label) (labeling : V → A) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).rejectionCount
      (fun v => labelOrder (labeling (vertexOrder.symm v))) = G.rejectionCount labeling := by
  classical
  unfold ConstraintGraph.rejectionCount
  symm
  apply Finset.card_equiv dartOrder
  intro e
  simp only [ConstraintGraph.mem_rejectedDarts, enumeratedGraph_edgeSatisfied]

end MaxCutGames.Foundations.PCP.GraphTables

/-! Reversible regular port graphs and their actual finite walks. Vertices may
repeat; loops and parallel edges retain their distinct ports. The rotation
map sends an outgoing dart to its arrival dart and is an involution. -/

namespace MaxCutGames.Foundations.PCP.PoweringWalks

variable {V D : Type*}

def headTailEquiv (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ (Walk V D n × D) where
  toFun w := ((w.1, fun j => w.2 j.succ), w.2 0)
  invFun z := (z.1.1, Fin.cases z.2 z.1.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    · funext j
      exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

/-- Isolate any actual path edge. Previously traversed ports are replaced by
their arrival ports, so the change of coordinates remains invertible. -/
def pivotEquiv (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) →
      (Walk V D (n + 1) ≃ (Edge V D × (Fin n → D)))
  | 0, _ => splitHead V D 0
  | n + 1, k => Fin.cases (splitHead V D (n + 1))
      (fun j => (rotateHead G (n + 1)).trans
        ((headTailEquiv V D (n + 1)).trans
          ((Equiv.prodCongr (pivotEquiv G n j) (Equiv.refl D)).trans
            (headTailEquiv (Edge V D) D n).symm))) k

theorem pivotEquiv_fst (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      (pivotEquiv G n k w).1 = edgeAt G n w k := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · change (pivotEquiv G n j (advanceTail G w)).1 =
        edgeAt G n (advanceTail G w) j
      exact ih j (advanceTail G w)

theorem pivotEquiv_succ_apply (G : PortGraph V D)
    (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 2)) :
    pivotEquiv G (n + 1) k.succ w =
      ((pivotEquiv G n k (advanceTail G w)).1,
       Fin.cases (G.rot (w.1, w.2 0)).2
         (pivotEquiv G n k (advanceTail G w)).2) := rfl

def leftFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → V → (Fin n → D) → V
  | 0, _, v, _ => v
  | n + 1, k, v, r => Fin.cases v
      (fun j => next G (leftFromPivot G n j v (fun m => r m.succ)) (r 0)) k

def rightFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → Edge V D → (Fin n → D) → V
  | 0, _, e, _ => next G e.1 e.2
  | n + 1, k, e, r => Fin.cases
      (wordEnd G (n + 1) (next G e.1 e.2) r)
      (fun j => rightFromPivot G n j e (fun m => r m.succ)) k

theorem leftFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      leftFromPivot G n k (pivotEquiv G n k w).1.1 (pivotEquiv G n k w).2 = w.1 := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change next G
        (leftFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1.1
          (pivotEquiv G n j (advanceTail G w)).2)
        (G.rot (w.1, w.2 0)).2 = w.1
      rw [ih j (advanceTail G w)]
      change (G.rot ((G.rot (w.1, w.2 0)).1, (G.rot (w.1, w.2 0)).2)).1 = w.1
      exact congrArg Prod.fst (rot_rot G (w.1, w.2 0))

theorem rightFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      rightFromPivot G n k (pivotEquiv G n k w).1 (pivotEquiv G n k w).2 =
        endpoint G w := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change rightFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1
        (pivotEquiv G n j (advanceTail G w)).2 = endpoint G w
      rw [ih j (advanceTail G w)]
      rfl

end MaxCutGames.Foundations.PCP.PoweringWalks

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PortTables
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable regular constraint tables on the fixed 64-label alphabet

Every pair `(vertex,port)` has one stored reverse index and one complete
4096-bit relation. Flat row `port + ports * vertex` has its tail implicitly
fixed by that pair. Rotation uses the stored vector lookup, followed by the
inverse row-index bijection. Loops and repeated directed occurrences remain
distinct rows.

Serialization uses the existing `GraphTables` codec: header `[vertices,darts]`
with `darts=vertices*ports`, then tail/reverse/4096 bit words per row.
-/

section

/-!
Cloud replacement for arbitrary finite constraint graphs. The new vertices are
the old darts; internal ports enforce equality inside each cloud, and one
external port applies the original constraint. Dummy loop darts allow padding
each cloud independently before replacement.

The supplied cloud port graphs are explicit parameters; no expansion or
soundness claim is assumed.
-/

open scoped BigOperators

namespace MaxCutGames.Foundations.PCP.DegreeReplacement

open PoweringWalks

variable {V E A D : Type*}

theorem replacement_complete [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ p, (replacementGraph G H).edgeSatisfied (liftLabel G labeling) p = true := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · exact replacement_satisfied_inl G H labeling e d
  · rw [replacement_satisfied_inr]
    exact h e

theorem rejectionCount_eq_sum [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) :
    G.rejectionCount labeling =
      ∑ e, if G.edgeSatisfied labeling e = false then 1 else 0 := by
  classical
  simp only [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts,
    Finset.card_eq_sum_ones, Finset.sum_filter]

theorem padded_complete (G : ConstraintGraph V E A) (dummy : V → Type*)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ c, (paddedGraph G dummy).edgeSatisfied labeling c = true := by
  intro c
  cases c with
  | inl e => exact h e
  | inr z => rfl

theorem padded_rejectionCount [Fintype V] [Fintype E]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    (labeling : V → A) :
    (paddedGraph G dummy).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_sum_type]
  simp
  simp only [Finset.card_filter]
  congr 1

end MaxCutGames.Foundations.PCP.DegreeReplacement

end

/-! A concrete constant-query proximity tester for a finite relation.

The proof oracle is a Boolean function on the Boolean functions on the finite
set of legal assignments. The tests are BLR linearity, self-corrected AND,
self-corrected unit, and comparison with a queried input coordinate.
The oracle's size depends exponentially on the number of legal assignments;
this is a fixed-relation construction, not a polynomial-size tester for an
arbitrary input formula. All tests below are explicit finite expectations.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_CayleySampling
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite binary-word tail counts for the proposed Cayley base graph.

No expander, independence, spectral, or random-generator existence result is
assumed here.
-/

namespace MaxCutGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

def correlation {A : Type*} [Fintype A] (f g : A → ℝ) : ℝ :=
  mean (fun x => f x * g x)

def iterateOperator {V D : Type*} [Fintype D] (G : PortGraph V D) :
    Nat → (V → ℝ) → (V → ℝ)
  | 0, f => f
  | n + 1, f => averagingOperator G (iterateOperator G n f)

def edgeDensity {V D : Type*} [Fintype V] [Fintype D] (bad : V × D → Bool) : ℝ :=
  mean (edgeProfile bad)

def markedStep {V D : Type*} [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then f (G.rot (v, d)).1 else 0)

def returnMass {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (bad : V × D → Bool) (gap : Nat) : ℝ :=
  mean (markedStep G bad (iterateOperator G gap (edgeProfile bad)))

/-! ## Finite normalized averages -/

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mean_eq_sum_div_card (f : A → ℝ) :
    mean f = (∑ x, f x) / (Fintype.card A : ℝ) :=
  Fintype.expect_eq_sum_div_card f

theorem mean_equiv (e : A ≃ B) (f : B → ℝ) :
    mean (fun x => f (e x)) = mean f :=
  Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem mean_add (f g : A → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g :=
  Finset.expect_add_distrib _ f g

theorem mean_sub (f g : A → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g :=
  Finset.expect_sub_distrib _ f g

theorem mean_mul_left (c : ℝ) (f : A → ℝ) :
    mean (fun x => c * f x) = c * mean f :=
  (Finset.mul_expect _ f c).symm

theorem mean_mul_right (f : A → ℝ) (c : ℝ) :
    mean (fun x => f x * c) = mean f * c :=
  (Finset.expect_mul _ f c).symm

theorem mean_nonnegative (f : A → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f :=
  Finset.expect_nonneg (fun x _ => hf x)

theorem mean_mono {f g : A → ℝ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  Finset.expect_le_expect (fun x _ => h x)

theorem energy_nonnegative (f : A → ℝ) : 0 ≤ energy f :=
  mean_nonnegative _ (fun x => sq_nonneg (f x))

/-- The finite Cauchy--Schwarz inequality, in the chosen normalized convention. -/
theorem correlation_sq_le (f g : A → ℝ) :
    correlation f g ^ 2 ≤ energy f * energy g :=
  Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f g

theorem energy_sub_const [Nonempty A] (f : A → ℝ) (c : ℝ) :
    energy (fun x => f x - c) = energy f - 2 * c * mean f + c ^ 2 := by
  have h : (fun x => (f x - c) ^ 2) =
      (fun x => (f x) ^ 2 - (2 * c) * f x + c ^ 2) := by
    funext x
    ring
  unfold energy
  rw [h, mean_add, mean_sub, mean_mul_left, mean_const]

theorem correlation_sub_const [Nonempty A] (f g : A → ℝ) (c d : ℝ) :
    correlation (fun x => f x - c) (fun x => g x - d) =
      correlation f g - d * mean f - c * mean g + c * d := by
  have h : (fun x => (f x - c) * (g x - d)) =
      (fun x => f x * g x - d * f x - c * g x + c * d) := by
    funext x
    ring
  unfold correlation
  rw [h, mean_add, mean_sub, mean_sub, mean_mul_left, mean_mul_left, mean_const]

end Averages

/-! ## The exact graph operator and the reversal identity -/

section Graph

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  (G : PortGraph V D)

omit [Nonempty V] in
theorem mean_operator (f : V → ℝ) : mean (averagingOperator G f) = mean f := by
  calc
    mean (averagingOperator G f) = mean (fun e : V × D => f (G.rot e).1) :=
      (mean_prod (fun e : V × D => f (G.rot e).1)).symm
    _ = mean (fun e : V × D => f e.1) := mean_equiv G.rot (fun e => f e.1)
    _ = mean (fun v : V => mean (fun _ : D => f v)) :=
      mean_prod (fun e : V × D => f e.1)
    _ = mean f := by simp only [mean_const]

omit [Fintype V] [Nonempty V] in
theorem operator_sub_const (f : V → ℝ) (c : ℝ) :
    averagingOperator G (fun v => f v - c) = fun v => averagingOperator G f v - c := by
  funext v
  change mean (fun d => f (G.rot (v, d)).1 - c) = _
  rw [mean_sub, mean_const]
  rfl

omit [Nonempty V] in
theorem mean_iterate (n : Nat) (f : V → ℝ) : mean (iterateOperator G n f) = mean f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, mean_operator, ih]

omit [Fintype V] [Nonempty V] in
theorem iterate_sub_const (n : Nat) (f : V → ℝ) (c : ℝ) :
    iterateOperator G n (fun v => f v - c) = fun v => iterateOperator G n f v - c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, ih, operator_sub_const]; rfl

omit [Nonempty V] [Nonempty D] in
/-- Reversal moves the first marked edge to its endpoint. The profile therefore
appears at the endpoint, before the `gap` remaining vertex transitions. -/
theorem mean_markedStep (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (f : V → ℝ) :
    mean (markedStep G bad f) = correlation (edgeProfile bad) f := by
  calc
    mean (markedStep G bad f) =
        mean (fun e : V × D => if bad e then f (G.rot e).1 else 0) := by
      exact (mean_prod (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad (G.rot e)
          then f (G.rot (G.rot e)).1 else 0) :=
      (mean_equiv G.rot (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad e then f e.1 else 0) := by
      congr 1
      funext e
      rw [reversal e, G.rot_involutive e]
    _ = mean (fun v => mean (fun d => if bad (v, d) then f v else 0)) :=
      mean_prod (fun e : V × D => if bad e then f e.1 else 0)
    _ = correlation (edgeProfile bad) f := by
      unfold correlation
      congr 1
      funext v
      have h : (fun d => if bad (v, d) then f v else 0) =
          (fun d => (if bad (v, d) then (1 : ℝ) else 0) * f v) := by
        funext d
        cases bad (v, d) <;> simp
      rw [h, mean_mul_right]
      rfl

omit [Nonempty V] [Nonempty D] in
theorem returnMass_eq_correlation (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap = correlation (edgeProfile bad)
      (iterateOperator G gap (edgeProfile bad)) :=
  mean_markedStep G bad reversal _

/-! ## Iterated contraction and centering -/

omit [Nonempty V] in
theorem iterate_energy_bound (lambda : ℝ) (certificate : SpectralCertificate G lambda)
    (f : V → ℝ) (hf : mean f = 0) (n : Nat) :
    energy (iterateOperator G n f) ≤ (lambda ^ n) ^ 2 * energy f := by
  induction n with
  | zero => simp [iterateOperator]
  | succ n ih =>
      calc
        energy (iterateOperator G (n + 1) f) ≤
            lambda ^ 2 * energy (iterateOperator G n f) :=
          certificate.contraction _ ((mean_iterate G n f).trans hf)
        _ ≤ lambda ^ 2 * ((lambda ^ n) ^ 2 * energy f) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg lambda)
        _ = (lambda ^ (n + 1)) ^ 2 * energy f := by rw [pow_succ]; ring

omit [Nonempty V] in
theorem zero_mean_correlation_bound (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (f : V → ℝ)
    (hf : mean f = 0) (n : Nat) :
    correlation f (iterateOperator G n f) ≤ lambda ^ n * energy f := by
  have hsq : correlation f (iterateOperator G n f) ^ 2 ≤
      (lambda ^ n * energy f) ^ 2 := by
    calc
      _ ≤ energy f * energy (iterateOperator G n f) := correlation_sq_le _ _
      _ ≤ energy f * ((lambda ^ n) ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (iterate_energy_bound G lambda certificate f hf n)
          (energy_nonnegative f)
      _ = _ := by ring
  exact le_of_sq_le_sq hsq
    (mul_nonneg (pow_nonneg certificate.nonnegative n) (energy_nonnegative f))

theorem correlation_centered (f : V → ℝ) (n : Nat) :
    correlation f (iterateOperator G n f) = mean f ^ 2 +
      correlation (fun v => f v - mean f)
        (iterateOperator G n (fun v => f v - mean f)) := by
  rw [iterate_sub_const, correlation_sub_const, mean_iterate]
  ring

end Graph

/-! ## The edge profile has Bernoulli-size variance -/

section Profiles

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

omit [Fintype V] [Nonempty V] [Nonempty D] in
theorem edgeProfile_nonnegative (bad : V × D → Bool) (v : V) : 0 ≤ edgeProfile bad v :=
  mean_nonnegative _ (fun d => by cases bad (v, d) <;> norm_num)

omit [Fintype V] [Nonempty V] in
theorem edgeProfile_le_one (bad : V × D → Bool) (v : V) : edgeProfile bad v ≤ 1 := by
  change mean (fun d => if bad (v, d) then (1 : ℝ) else 0) ≤ 1
  calc
    _ ≤ mean (fun _ : D => (1 : ℝ)) := mean_mono (fun d => by
      cases bad (v, d) <;> norm_num)
    _ = 1 := mean_const _

omit [Nonempty V] [Nonempty D] in
theorem edgeDensity_nonnegative (bad : V × D → Bool) : 0 ≤ edgeDensity bad :=
  mean_nonnegative _ (edgeProfile_nonnegative bad)

omit [Nonempty V] in
theorem edgeProfile_energy_le_density (bad : V × D → Bool) :
    energy (edgeProfile bad) ≤ edgeDensity bad :=
  mean_mono (fun v => by
    have h0 := edgeProfile_nonnegative bad v
    have h1 := edgeProfile_le_one bad v
    nlinarith)

theorem edgeProfile_centered_energy (bad : V × D → Bool) :
    energy (fun v => edgeProfile bad v - edgeDensity bad) ≤
      edgeDensity bad * (1 - edgeDensity bad) := by
  rw [energy_sub_const]
  have h := edgeProfile_energy_le_density bad
  change energy (edgeProfile bad) - 2 * edgeDensity bad * edgeDensity bad +
    edgeDensity bad ^ 2 ≤ _
  nlinarith

/-- Sharp return bound. No division by the bad-edge density occurs, so the empty
bad set is covered. `gap = 0` gives the adjacent-edge upper bound `epsilon`. -/
theorem returnMass_le_sharp (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap ≤ edgeDensity bad ^ 2 +
      lambda ^ gap * (edgeDensity bad * (1 - edgeDensity bad)) := by
  rw [returnMass_eq_correlation G bad reversal, correlation_centered]
  have hzero : mean (fun v => edgeProfile bad v - edgeDensity bad) = 0 := by
    rw [mean_sub, mean_const]
    simp only [edgeDensity, sub_self]
  have hc := zero_mean_correlation_bound G lambda certificate
    (fun v => edgeProfile bad v - edgeDensity bad) hzero gap
  have hv := mul_le_mul_of_nonneg_left (edgeProfile_centered_energy bad)
    (pow_nonneg certificate.nonnegative gap)
  change edgeDensity bad ^ 2 + _ ≤ _
  exact add_le_add (le_refl _) (hc.trans hv)

/-- The simple bound used in the second-moment estimate. -/
theorem returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap ≤ edgeDensity bad ^ 2 + edgeDensity bad * lambda ^ gap := by
  have h := returnMass_le_sharp G lambda certificate bad reversal gap
  have hvar : edgeDensity bad * (1 - edgeDensity bad) ≤ edgeDensity bad := by
    nlinarith [sq_nonneg (edgeDensity bad)]
  have hm := mul_le_mul_of_nonneg_left hvar (pow_nonneg certificate.nonnegative gap)
  nlinarith

end Profiles

/-- The finite geometric-series bound that absorbs forward and reverse returns.
It applies to every finite window, with no limiting probability argument. -/
theorem geometric_sum_le (lambda : ℝ) (h0 : 0 ≤ lambda) (h1 : lambda < 1) (n : Nat) :
    (∑ k ∈ Finset.range n, lambda ^ k) ≤ 1 / (1 - lambda) := by
  have hsum : (∑ k ∈ Finset.range n, lambda ^ k) * (1 - lambda) = 1 - lambda ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
  have hden : 0 < 1 - lambda := by linarith
  apply (le_div_iff₀ hden).2
  rw [hsum]
  linarith [pow_nonneg h0 n]

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

/-- The return contribution from one marked edge, over a finite forward window. -/
theorem sum_returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (∑ gap ∈ Finset.range n, returnMass G bad gap) ≤
      (n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad / (1 - lambda) := by
  calc
    _ ≤ ∑ gap ∈ Finset.range n,
        (edgeDensity bad ^ 2 + edgeDensity bad * lambda ^ gap) :=
      Finset.sum_le_sum (fun gap _ => returnMass_le G lambda certificate bad reversal gap)
    _ = (n : ℝ) * edgeDensity bad ^ 2 +
        edgeDensity bad * (∑ gap ∈ Finset.range n, lambda ^ gap) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad * (1 / (1 - lambda)) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (geometric_sum_le lambda certificate.nonnegative certificate.lt_one n)
          (edgeDensity_nonnegative bad))
    _ = _ := by ring

/-- Sum over all distinct ordered-time pairs, counting each pair once.
The row for the later edge `j` has gaps `0,...,j-1`. -/
theorem triangular_returnMass_sum_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (∑ j ∈ Finset.range n, ∑ gap ∈ Finset.range j, returnMass G bad gap) ≤
      ((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
        (n : ℝ) * (edgeDensity bad / (1 - lambda)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hrow := sum_returnMass_le G lambda certificate bad reversal n
      have h := add_le_add ih hrow
      calc
        _ ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
            (n : ℝ) * (edgeDensity bad / (1 - lambda)) +
            ((n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad / (1 - lambda)) := h
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; ring

/-- The exact finite envelope needed after expanding the square of the hit
count. The diagonal contributes `n * epsilon`; both off-diagonal triangles
contribute twice the return sum. The actual walk-event identity is supplied by
`PoweringMoment` and `PoweringReturn`. -/
theorem secondMoment_return_envelope (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (n : ℝ) * edgeDensity bad +
        2 * (∑ j ∈ Finset.range n, ∑ gap ∈ Finset.range j, returnMass G bad gap) ≤
      (n : ℝ) * edgeDensity bad *
        (1 + 2 / (1 - lambda) + ((n : ℝ) - 1) * edgeDensity bad) := by
  calc
    _ ≤ (n : ℝ) * edgeDensity bad +
        2 * (((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
          (n : ℝ) * (edgeDensity bad / (1 - lambda))) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (triangular_returnMass_sum_le G lambda certificate bad reversal n) (by norm_num))
    _ = _ := by ring

end

end MaxCutGames.Foundations.PCP.SpectralReturn

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_CayleySpectral
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Walsh diagonalization of actual Boolean-cube Cayley graphs

Every port is an indexed generator. The rotation keeps the port and adds its
generator by pointwise xor, so loops and repeated generators keep their full
multiplicity. The Fourier multiplier and energy estimate are proved for this
actual averaging operator; no Fourier/operator compatibility is assumed.
-/

/-!
# Finite existence of the Cayley expander base

The sample space is the actual finite type of indexed Boolean-cube generators.
For each nonzero character, the checked sign sampling equivalence supplies its
uniform word law. A finite union bound then selects a generator family whose
nonconstant character biases are small. There is no random-graph hypothesis.

The fixed numbers below are manipulated symbolically; no enumeration of the
generator sample space is executed. The subsequent square-and-zigzag family
is a separate construction.
-/

/-! Exact changes of finite vertex and port coordinates. The graph rotation and
its normalized averaging operator are transported by the same equivalences. -/

namespace MaxCutGames.Foundations.PCP.GraphTransport

open PoweringWalks SpectralReturn

variable {V W D E : Type*}

variable [Fintype V] [Fintype W] [Fintype D] [Fintype E]

theorem energy_reindex (vertices : V ≃ W) (f : W → ℝ) :
    energy (fun v => f (vertices v)) = energy f :=
  mean_equiv vertices (fun w => f w ^ 2)

end MaxCutGames.Foundations.PCP.GraphTransport

/-!
# Actual graph squares and zigzag products

Rotations operate on actual vertex-port pairs. All returned ports are retained,
including ports belonging to loops and parallel edges. Each construction is a
palindrome of involutions and hence defines a reversible regular port graph.
-/

/-!
# Energy contraction for the actual zigzag graph

The proof splits a function into its cloud average and its cloud-centered
part. All operators are the actual graph averages from `ZigzagGraphs`.
-/

namespace MaxCutGames.Foundations.PCP.ZigzagSpectral

open PoweringWalks SpectralReturn ZigzagGraphs

noncomputable section

variable {V D E : Type*}

def cloudMean [Fintype D] (f : V × D → ℝ) (v : V) : ℝ :=
  mean (fun d => f (v, d))

def projection [Fintype D] (f : V × D → ℝ) : V × D → ℝ :=
  liftCloud (cloudMean f)

def centered [Fintype D] (f : V × D → ℝ) : V × D → ℝ := f - projection f

theorem mean_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    mean (liftCloud (D := D) f) = mean f := by
  change mean (fun x : V × D => f x.1) = mean f
  rw [mean_prod]
  simp only [mean_const]

theorem energy_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    energy (liftCloud (D := D) f) = energy f :=
  mean_liftCloud (D := D) (fun v => f v ^ 2)

theorem mean_cloudMean [Fintype V] [Fintype D] (f : V × D → ℝ) :
    mean (cloudMean f) = mean f := (mean_prod f).symm

theorem energy_prod [Fintype V] [Fintype D] (f : V × D → ℝ) :
    energy f = mean (fun v => energy (fun d => f (v, d))) :=
  mean_prod (fun x => f x ^ 2)

theorem cloudMean_centered_zero [Fintype D] [Nonempty D]
    (f : V × D → ℝ) (v : V) : cloudMean (centered f) v = 0 := by
  change mean (fun d => f (v, d) - cloudMean f v) = 0
  rw [mean_sub, mean_const]
  exact sub_self _

theorem energy_centered_eq_sub [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) = energy f - energy (projection f) := by
  have hpoint (v : V) : energy (fun d => centered f (v, d)) =
      energy (fun d => f (v, d)) - (cloudMean f v) ^ 2 := by
    change energy (fun d => f (v, d) - cloudMean f v) = _
    rw [energy_sub_const]
    change energy (fun d => f (v, d)) - 2 * cloudMean f v * cloudMean f v +
      (cloudMean f v) ^ 2 = _
    ring
  have hproj : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  calc
    energy (centered f) = mean (fun v => energy (fun d => centered f (v, d))) :=
      energy_prod _
    _ = mean (fun v => energy (fun d => f (v, d)) - (cloudMean f v) ^ 2) := by
      congr 1
      funext v
      exact hpoint v
    _ = mean (fun v => energy (fun d => f (v, d))) -
        mean (fun v => (cloudMean f v) ^ 2) := mean_sub _ _
    _ = energy f - energy (projection f) := by
      rw [← energy_prod f, hproj]
      rfl

theorem projection_energy_decomposition [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy f = energy (projection f) + energy (centered f) := by
  rw [energy_centered_eq_sub]
  ring

theorem energy_centered_le [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) ≤ energy f := by
  rw [energy_centered_eq_sub]
  exact sub_le_self _ (energy_nonnegative _)

theorem energy_add_three_le {A : Type*} [Fintype A] (a b c : A → ℝ) :
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := by
  calc
    energy (a + b + c) ≤ mean (fun x => 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)) := by
      apply mean_mono
      intro x
      change (a x + b x + c x) ^ 2 ≤ 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)
      nlinarith [sq_nonneg (a x - b x), sq_nonneg (a x - c x), sq_nonneg (b x - c x)]
    _ = 3 * (energy a + energy b + energy c) := by
      rw [mean_mul_left, mean_add, mean_add]
      rfl

end

end MaxCutGames.Foundations.PCP.ZigzagSpectral

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ExpanderFamily
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A concrete finite family from the Cayley base

The initial graph has one vertex and the fixed number of loop ports. Each
subsequent graph is the actual square-and-zigzag construction. Consequently
the vertex sizes are exact powers of one fixed integer, including size one.
The finite base is selected from the proved existence theorem.
-/

namespace MaxCutGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

instance basePortNonempty : Nonempty BasePort :=
  ⟨fun _ => ⟨0, by norm_num [initialQuarterDegree]⟩⟩

instance vertexNonempty (n : Nat) : Nonempty (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ n ih =>
    let : Nonempty (Vertex n) := ih
    change Nonempty (Vertex n × CloudPort)
    infer_instance

end MaxCutGames.Foundations.PCP.ExpanderFamily

/-!
# Padding actual tail fibers to the geometric graph-family sizes

Every nonempty cloud is padded to the next family size. Empty clouds stay
empty, so their old vertices do not create new darts. Explicit equivalences
identify padded tail fibers and partition all darts by their original tails.
These facts give the global size bound without an expansion assumption.
-/

/-!
# Executable indexing of the actual outgoing-dart clouds

Clouds are enumerated by filtering the input table's increasing dart-index
list. Ranking searches that list, and selection reads its indexed entry.
The same functions work for empty clouds without selecting a default dart.
Padded cloud indices put all old darts first and the dummy indices afterward.
All data functions below are executable; their proofs establish the connection
to the semantic graph's actual tail fibers.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Overlay
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Overlay a regular constraint graph with an actual regular port graph whose
new constraints always accept. The port sets are disjoint, so all original
rejected darts are retained exactly. The averaging operator is the actual
degree-weighted mixture of the two graph averages.
-/

open scoped BigOperators

namespace MaxCutGames.Foundations.PCP.Overlay

open PoweringWalks SpectralReturn

variable {V D E A : Type*}

variable [Fintype V] [Fintype D] [Fintype E]

/-- Convexity of the squared energy, proved pointwise before taking the finite mean. -/
theorem energy_convex_mix (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (f g : V → ℝ) :
    energy (fun v => a * f v + b * g v) ≤ a * energy f + b * energy g := by
  calc
    energy (fun v => a * f v + b * g v) ≤
        mean (fun v => a * (f v) ^ 2 + b * (g v) ^ 2) := by
      apply mean_mono
      intro v
      have hnormalize := congrArg (fun t : ℝ => t * (a * (f v) ^ 2 + b * (g v) ^ 2)) hab
      have hnonneg := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (f v - g v))
      nlinarith
    _ = a * energy f + b * energy g := by
      rw [mean_add, mean_mul_left, mean_mul_left]
      rfl

end MaxCutGames.Foundations.PCP.Overlay

end

/-! Additive smoothing of the actual fair Boolean-tape length law.  This is
the finite-probability input to the lazy-walk amplification argument. -/

/-! Lazification of the actual constraint graph. Original ports retain their
tests; the equally many stay-put ports always accept. The reverse is precisely
the existing lazy port-graph rotation used by the spectral and walk lemmas. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_GraphGap
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite counting for rounding copied dart labels. Minority color classes
are small enough for the cloud's directed-cut expansion. Their boundary darts
inject into all label disagreements. A separate endpoint charge counts at
most two affected original darts per changed copied label.
-/

namespace MaxCutGames.Foundations.PCP.CloudRounding

open scoped BigOperators

theorem dart_rejection_count_le
    {E V A : Type*} [Fintype E] [DecidableEq A]
    (tail : E → V) (reverse : E ≃ E) (accepts : E → A → A → Bool)
    (ell : E → A) (rounded : V → A) :
    (Finset.univ.filter (fun e =>
      accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)).card ≤
    (Finset.univ.filter (fun e => accepts e (ell e) (ell (reverse e)) = false)).card +
      2 * (Finset.univ.filter (fun e => ell e ≠ rounded (tail e))).card := by
  classical
  let R : Finset E := Finset.univ.filter (fun e =>
    accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)
  let B : Finset E := Finset.univ.filter (fun e =>
    accepts e (ell e) (ell (reverse e)) = false)
  let M : Finset E := Finset.univ.filter (fun e => ell e ≠ rounded (tail e))
  let MR : Finset E := Finset.univ.filter (fun e =>
    ell (reverse e) ≠ rounded (tail (reverse e)))
  have hrev : MR.card = M.card := by
    have hsets : MR = M.map reverse.symm.toEmbedding := by
      ext e
      constructor
      · intro he
        apply Finset.mem_map.mpr
        refine ⟨reverse e, ?_, reverse.symm_apply_apply e⟩
        simpa [MR, M] using he
      · intro he
        obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp he
        simpa [MR, M] using hd
    rw [hsets, Finset.card_map]
  have hsub : R ⊆ (B ∪ M) ∪ MR := by
    intro e he
    by_cases hl : ell e = rounded (tail e)
    · by_cases hr : ell (reverse e) = rounded (tail (reverse e))
      · have hb : e ∈ B := by simpa [B, R, hl, hr] using he
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
      · exact Finset.mem_union_right _ (by simp [MR, hr])
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [M, hl]))
  change R.card ≤ B.card + 2 * M.card
  calc
    R.card ≤ ((B ∪ M) ∪ MR).card := Finset.card_le_card hsub
    _ ≤ (B ∪ M).card + MR.card := Finset.card_union_le _ _
    _ ≤ (B.card + M.card) + MR.card :=
      Nat.add_le_add_right (Finset.card_union_le B M) _
    _ = B.card + 2 * M.card := by rw [hrev]; omega

section CloudCounts

variable {X A D : Type*} [Fintype X] [Fintype A] [Fintype D]
variable [DecidableEq X] [DecidableEq A]

omit [Fintype A] in
/-- Every nonchosen color occupies at most half the cloud. -/
theorem nonchosen_color_twice_le (ell : X → A) (m : A)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (a : A) (ha : a ≠ m) :
    2 * (colorSet ell a).card ≤ Fintype.card X := by
  have hd : Disjoint (colorSet ell a) (colorSet ell m) := by
    apply Finset.disjoint_left.mpr
    intro x hx hm
    have hxa : ell x = a := by simpa [colorSet] using hx
    have hxm : ell x = m := by simpa [colorSet] using hm
    exact ha (hxa.symm.trans hxm)
  have hu : (colorSet ell a).card + (colorSet ell m).card ≤ Fintype.card X := by
    calc
      _ = (colorSet ell a ∪ colorSet ell m).card :=
        (Finset.card_union_of_disjoint hd).symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card X := Finset.card_univ
  have hm := maximal a
  omega

def minorityEquiv (ell : X → A) (m : A) :
    (Σ a : Nonmajor m, ↥(colorSet ell a.val)) ≃ ↥(minoritySet ell m) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val = t.1.val := (Finset.mem_filter.mp t.2.property).2
    have hn : ell t.2.val ≠ m := fun h => t.1.property (hc.symm.trans h)
    simpa [minoritySet] using hn⟩
  invFun x :=
    ⟨⟨ell x.val, by simpa [minoritySet] using x.property⟩,
      ⟨x.val, by simp [colorSet]⟩⟩
  left_inv t := by
    rcases t with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    have hxa : ell x = a := by simpa [colorSet] using hx
    cases hxa
    rfl
  right_inv x := by apply Subtype.ext; rfl

omit [DecidableEq X] in
theorem minority_card_eq_sum (ell : X → A) (m : A) :
    (minoritySet ell m).card = ∑ a : Nonmajor m, (colorSet ell a.val).card := by
  have h := Fintype.card_congr (minorityEquiv ell m)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

/-- The tail label determines the forgotten minority color. -/
def minorityCutEmbedding (ell : X → A) (next : X × D → X) (m : A) :
    (Σ a : Nonmajor m, ↥(directedCut next (colorSet ell a.val))) ↪
      ↥(disagreementSet ell next) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val.1 = t.1.val ∧ ell (next t.2.val) ≠ t.1.val := by
      simpa [directedCut, colorSet] using t.2.property
    have hn : ell t.2.val.1 ≠ ell (next t.2.val) :=
      fun h => hc.2 (h.symm.trans hc.1)
    simpa [disagreementSet] using hn⟩
  inj' p q h := by
    rcases p with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    rcases q with ⟨⟨b, hb⟩, ⟨y, hy⟩⟩
    have hxy : x = y := congrArg Subtype.val h
    cases hxy
    have hxa : ell x.1 = a := by
      have hc : ell x.1 = a ∧ ell (next x) ≠ a := by
        simpa [directedCut, colorSet] using hx
      exact hc.1
    have hxb : ell x.1 = b := by
      have hc : ell x.1 = b ∧ ell (next x) ≠ b := by
        simpa [directedCut, colorSet] using hy
      exact hc.1
    have hab : a = b := hxa.symm.trans hxb
    cases hab
    rfl

theorem minority_cut_sum_le (ell : X → A) (next : X × D → X) (m : A) :
    (∑ a : Nonmajor m, (directedCut next (colorSet ell a.val)).card) ≤
      (disagreementSet ell next).card := by
  have h := Fintype.card_le_of_injective
    (minorityCutEmbedding ell next m) (minorityCutEmbedding ell next m).injective
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h

/-- Sum genuine directed-cut expansion over the nonchosen color classes. -/
theorem minority_expansion_bound (ell : X → A) (next : X × D → X) (m : A)
    (h : ℚ)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (expansion : ∀ S : Finset X, S.card ≤ Fintype.card X / 2 →
      h * (S.card : ℚ) ≤ ((directedCut next S).card : ℚ)) :
    h * ((minoritySet ell m).card : ℚ) ≤ ((disagreementSet ell next).card : ℚ) := by
  have each (a : Nonmajor m) :
      h * ((colorSet ell a.val).card : ℚ) ≤
        ((directedCut next (colorSet ell a.val)).card : ℚ) := by
    apply expansion
    have ha := nonchosen_color_twice_le ell m maximal a.val a.property
    omega
  calc
    h * ((minoritySet ell m).card : ℚ) =
        ∑ a : Nonmajor m, h * ((colorSet ell a.val).card : ℚ) := by
      rw [minority_card_eq_sum, Nat.cast_sum, Finset.mul_sum]
    _ ≤ ∑ a : Nonmajor m, ((directedCut next (colorSet ell a.val)).card : ℚ) :=
      Finset.sum_le_sum (fun a _ => each a)
    _ ≤ ((disagreementSet ell next).card : ℚ) := by
      exact_mod_cast minority_cut_sum_le ell next m

end CloudCounts

end MaxCutGames.Foundations.PCP.CloudRounding

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_SpectralCut
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual directed-cut expansion from the graph's zero-mean spectral
certificate. Parallel edges and loops retain their indexed port multiplicities. -/
noncomputable section
namespace MaxCutGames.Foundations.PCP.SpectralCut

open scoped BigOperators
open PoweringWalks SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mean_indicator (S : Finset V) :
    mean (indicator S) = (S.card : ℝ) / (Fintype.card V : ℝ) := by
  have hf : Finset.univ.filter (fun v : V => v ∈ S) = S := by
    ext v
    simp
  rw [mean_eq_sum_div_card]
  simp only [indicator, Finset.sum_boole, hf]

theorem energy_indicator (S : Finset V) : energy (indicator S) = mean (indicator S) := by
  unfold energy
  congr 1
  funext v
  unfold indicator
  split_ifs <;> norm_num

end Indicators

end MaxCutGames.Foundations.PCP.SpectralCut
end

/-!
An actual fixed-degree graph obtained by padding each outgoing-dart cloud to
the explicit expander family and then replacing vertices by cloud darts.
Expansion and majority rounding are proved dependencies, not hypotheses of
the final soundness theorem. Isolated original vertices have empty clouds.
-/

/-! Spectral contraction for the actual Boolean-flag lazy port graph. The
operator identity is proved in `PoweringLazy`; the estimate here averages the
elementary two-term square inequality. -/

/-!
# Concrete preprocessing table algorithm

Given one fixed expander base table, this function computes regularized
cloud rows, pads the whole vertex set, overlays a stored family table, and
adds the half-lazy rows. It is total even on zero-dart input tables. The
bounds below concern actual output data; an actual TM2 execution certificate
is a separate theorem and is not inferred from these size bounds.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingRegularSoundness
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Soundness of the executable regularization tables

The fixed input base table is required only to have its proved spectral
certificate. Every positive cloud uses the actual recursively generated table
at its computed size. Its spectral certificate gives the precise cut bound
used by majority rounding. Empty clouds are handled by their zero cardinality.
Thus neither expansion nor the desired count comparison is an input premise.
-/

/-!
Spectral certificates for the actual materialized preprocessing tables.
Exact rotation identities transport the checked semantic overlay and lazy
estimates to the stored tables. No spectral premise is imposed on the
original constraint table in the overlay theorem.
-/

/-! Soundness and expansion of the actual executable preprocessing tables.
The fixed base-table spectral certificate is supplied by the proved expander
existence theorem; no output expansion or output gap is assumed. -/

/-! Full-radius local opinions use a common alphabet indexed by bounded
port addresses. Every opinion is decoded through a fixed address selector;
arbitrary alphabet symbols need not agree on colliding addresses. -/

namespace MaxCutGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

instance finitePortWords [Finite D] (t : Nat) : Finite (PortWords D t) := by
  let := Fintype.ofFinite D
  exact Finite.of_fintype _

end MaxCutGames.Foundations.PCP.PoweringLabels

/-!
# Executable bounded port-address enumeration

For a port alphabet `Fin d`, the lists below enumerate every word of every
length at most the fixed radius. The resulting first-match selector searches
these addresses and never enumerates the ambient vertex type.
-/

/-!
# Executable integer encodings for the powering construction

All encodings below have explicit inverses. They use the arithmetic finite
function, sigma, and product equivalences rather than choosing enumerations
from cardinality proofs. Word digits use the head-major convention; addresses
are grouped by increasing word length. A dart is numbered first by its vertex,
then its word, with its two orientations adjacent.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringDecoding
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Modal decoding is an actual maximum of finite empirical letter masses.
Its reciprocal-alphabet lower bound is derived from their total mass one. -/

/-! Actual indicator counting and the second-moment rejection estimate.
The hypotheses describe event inclusion and moment bounds, while the
Cauchy--Schwarz conclusion and all positivity properties are proved here. -/

/-! Actual finite walk averages and their operator representations.
All changes of probability coordinates come from explicit equivalences. -/

namespace MaxCutGames.Foundations.PCP.PoweringReturn

open PoweringWalks SpectralReturn
open PoweringMoment (bit)

variable {V D : Type*}

theorem mean_word_cons_head [Fintype D] (n : Nat)
    (F : (Fin (n + 1) → D) → ℝ) :
    mean F = mean (fun d : D => mean (fun r : Fin n → D => F (Fin.cases d r))) := by
  calc
    mean F = mean (fun z : D × (Fin n → D) => F (Fin.cases z.1 z.2)) :=
      (mean_equiv (portConsEquiv D n) F).symm
    _ = _ := mean_prod _

theorem mean_word_cons_tail [Fintype D] (n : Nat)
    (F : (Fin (n + 1) → D) → ℝ) :
    mean F = mean (fun r : Fin n → D => mean (fun d : D => F (Fin.cases d r))) := by
  calc
    mean F = mean (fun z : (Fin n → D) × D => F (Fin.cases z.2 z.1)) :=
      (mean_equiv ((Equiv.prodComm (Fin n → D) D).trans (portConsEquiv D n)) F).symm
    _ = _ := mean_prod _

theorem mean_edge_bit [Fintype D] (bad : V × D → Bool) (v : V) :
    mean (fun d : D => bit (bad (v, d) = true)) = edgeProfile bad v := by
  simp only [bit_bool, mean, edgeProfile]

end MaxCutGames.Foundations.PCP.PoweringReturn

/-! Actual local-label opinions, modal decoding at the reference length, and
its proved persistence at nearby lazy-walk lengths. -/

/-!
# Full-radius access to the endpoints of each actual walk edge

The tail of each traversed edge is reachable from the walk's start. Its head
is reachable from the walk's end by reversing the remaining suffix with the
actual arrival ports. These facts supply values in the two neighborhood-ball
types used by the endpoint label decoders.
-/

/-!
# The actual constraint-graph powering test

Every recorded port walk gives two directed darts. Reversal flips an
orientation bit while preserving the recorded walk. The common vertex
alphabet is the full-radius padded local-label alphabet. The test checks the
actual base constraint at every traversed edge using the two endpoint labels.

Honest local encodings give perfect completeness. A decoded bad edge together
with the two matching local opinions forces rejection of the actual test.
Neither conclusion is assumed as a rejection-inclusion or distribution law.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringOpinionTables
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded first-address tables for actual powering constraints

For a graph with numbered vertices and ports, each stored local-opinion index
is the first address in `allAddresses` that reaches the requested vertex.
The search traverses bounded port words, never the ambient vertex set.

The walk table stores one base dart and two address indices per traversed
edge. Looking up the endpoint labels at those indices gives exactly the
existing `finitePortSelector` decoders, including when addresses collide.
The resulting finite table predicate equals the actual powering predicate.
-/

/-!
# Executable directed graph tables over a fixed finite alphabet

The alphabet size `q` is fixed by the encoding, not encoded as a variable input
field. The header stores vertex and directed-dart counts. Each ordered dart row
stores its tail, reverse index, and every `q*q` predicate bit in order `b+q*a`.
All fields use the existing unary natural-word codec. Decoding validates graph
laws and preserves loops and repeated darts. Size bounds count the complete
serialized table and make no running-time assertion.
-/

namespace MaxCutGames.Foundations.PCP.GenericGraphTables

open MaxCutGames.Foundations.Complexity

variable {q : Nat}

instance instDecidableValid {n m : Nat} (rows : Rows q n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

end MaxCutGames.Foundations.PCP.GenericGraphTables

/-!
# Executable tables of the actual powering graph

The input rotor and every base predicate are stored finite vectors. The output
has one row for each start vertex, bounded port word, and orientation, with the
two orientations adjacent. Every complete predicate table is generated from the
bounded first-address lookup test. Degree and walk length fix the output alphabet;
neither the alphabet nor an address list depends on the input vertex count.
-/

/-!
# Actual rejection counts and sizes for the powering construction

Normalized rejection averages are the cardinal ratios of the corresponding
rejected-dart sets. These identities include empty finite types. Positivity
of the dart cardinality is required only when translating inequalities by
division. The powered dart count and common alphabet size are computed from
their actual product and function types.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Lookup
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite registers and physical tape roles of the alphabet-table machine.
Input-sized numbers occur only on unary tapes. The comparison and emitter
register layouts are related by explicit, executable product rearrangements.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.RuntimeModel

open Turing
open MaxCutGames.Foundations.Complexity

protected abbrev Tape.enumList : List Tape := [.original, .cursor, .scan, .vertices, .darts,
  .counter, .edge, .tail, .reverseIndex, .head, .scratch, .indexScan, .compareLeft,
  .compareRight, .reversed, .output]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

def headPorts : Fin 6 → Tape :=
  ![.original, .reverseIndex, .scan, .indexScan, .head, .scratch]

theorem cleanupPorts_cover (tape : Tape) (h : tape ≠ .output) :
    ∃ i, cleanupPorts i = tape := by
  cases tape
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨10, rfl⟩
  · exact ⟨11, rfl⟩
  · exact ⟨12, rfl⟩
  · exact ⟨13, rfl⟩
  · exact ⟨14, rfl⟩
  · exact (h rfl).elim

end MaxCutGames.Foundations.PCP.AlphabetTable.RuntimeModel

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringTableSemantics
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
# Exact semantics of the executable powering tables

The explicit label and dart bijections preserve every actual edge test and
every rejected directed occurrence. The inverse label map covers all encoded
assignments, so satisfiability and uniform rejection-count bounds transport
without any consistency restriction on padded labels.
-/


/-!
An actual incidence constraint graph for a finite Boolean verifier with q queries.
Left labels are complete local answer tuples. Their validity includes consistency
at repeated proof addresses. A dart checks the tuple at the least position naming
its proof address. Both sides use the same 2^q-element alphabet; arbitrary right
labels are explicitly decoded by their first coordinate, and honest right labels
are constant tuples. Every incidence is represented by two opposite darts.

The count theorem proves a loss of exactly q in a supplied verifier rejection
fraction. It supplies a concrete construction, not a PCP-hardness premise. The
generic count statements permit an empty event type and introduce no dummy darts.
-/

namespace MaxCutGames.Foundations.PCP.QueryIncidence

variable {E X : Type*} {q : Nat}

theorem incidenceAccept_true [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (event : E) (slot : Fin q) (left right : Label q)
    (accepted : incidenceAccept T positive event slot left right = true) :
    T.accepts event left = true ∧ RepeatedConsistent T event left ∧
      left (canonicalSlot T event slot) = decodeRight positive right := by
  simp only [incidenceAccept, Bool.and_eq_true] at accepted
  have hvalid : LeftValid T event left := _root_.of_decide_eq_true accepted.1
  exact ⟨hvalid.1, hvalid.2, _root_.of_decide_eq_true accepted.2⟩

end MaxCutGames.Foundations.PCP.QueryIncidence



end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_CompareLoop
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite TM2 templates for affine unary fields and finite relation bits.
Commands write in forward bit order onto a stack, so their concatenated result
appears reversed in the accumulator. Every unbounded operand is read from an
isolated unary tape and restored by the checked preserving transducer.
-/

/-!
# Affine numeric fields of the alphabet-reduction table

The five unbounded unary inputs are n, m, e, tail, head, in that order.
Every field uses a fixed list of natural coefficients and one bounded offset.
For a fixed local event and slot, the query field's coefficient list does not
depend on the input predicate. The predicate changes only its bounded offset.
Evaluation uses the same `Emitter.affineValue` as the actual unary emitter.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Addresses

open MaxCutGames.Foundations.Hastad
open Enumeration

def eval {bound : Nat} (field : Field bound) (inputs : Fin 5 → Nat) : Nat :=
  Emitter.affineValue field.terms inputs field.offset.val

end MaxCutGames.Foundations.PCP.AlphabetTable.Addresses

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_EmitRows
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The actual alphabet-reduction row template. The old predicate and the loop flag
are finite registers. All unbounded quantities reside in five preserved unary
tapes. The fixed event/slot/orientation order is retained without deduplication.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open MaxCutGames.Foundations.Complexity
open Emitter

theorem bitValues_ofFn_inline_EmitRows {σ : Type} {n : Nat}
    (relation : σ → Vector Bool n) (context : σ) :
    (List.ofFn (fun index : Fin n => fun state => (relation state)[index])).map
      (fun bit => if bit context then 1 else 0) =
      (relation context).toList.map GraphTables.bitWord := by
  rw [← vector_list_ofFn_inline_EmitRows (relation context)]
  simp only [List.map_ofFn]
  rfl

end MaxCutGames.Foundations.PCP.AlphabetTable.EmitRows

/-! Actual finite-stack cleanup. Each selected stack is drained using the
checked pop loop, followed by one transition resetting the finite state.
Repeated selections are allowed; they only reduce the cost upper bound. -/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Cleanup

open Turing
open Complexity
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

@[simp] theorem clearTapes_selected {n : Nat} (selected : Fin n → K)
    (base : K → List Bool) (i : Fin n) : clearTapes selected base (selected i) = [] := by
  rw [clearTapes_apply, ite_eq_left ⟨i, rfl⟩]

theorem clearTapes_unselected {n : Nat} (selected : Fin n → K)
    (base : K → List Bool) (k : K) (notSelected : ∀ i, selected i ≠ k) :
    clearTapes selected base k = base k := by
  rw [clearTapes_apply]
  simp [notSelected]

/-- Enumerating exactly the nonoutput stacks yields the standard final tape
family. Repeated selected stacks are permitted. -/
theorem clearTapes_outputOnly {n : Nat} (selected : Fin n → K)
    (output : K) (base : K → List Bool)
    (excludesOutput : ∀ i, selected i ≠ output)
    (coversOther : ∀ k, k ≠ output → ∃ i, selected i = k) :
    clearTapes selected base = fun k => if k = output then base output else [] := by
  funext k
  by_cases h : k = output
  · subst k
    simp [clearTapes_unselected selected base output excludesOutput]
  · rw [clearTapes_apply]
    simp [h, coversOther k h]

end MaxCutGames.Foundations.PCP.AlphabetTable.Cleanup

/-!
Exact tape invariant for the old-dart loop. The cursor stores the remaining
input rows, while the reversed tape stores precisely the output headers and
the blocks already emitted. The scan and index-scan tapes are unconstrained:
the next lookup prefixes fresh copies and retains old residues as suffixes.
Finite control state is specified by the actual execution theorems using this
tape invariant.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_InitialGraph
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The initial finite constraint graph of an arbitrary concrete 3CNF formula.
Clause and variable vertices use one eight-element alphabet. Variable labels
are the canonical triples `(bit, false, false)`; clause labels are arbitrary
triples. Every incidence has two directed darts, including repeated names.
A tautological dummy loop keeps the graph nonempty for empty formulas.

Name compaction precedes the public construction. The resulting vertex count
is at most `4*m+1`, and the dart count is exactly `6*m+1`. Unsatisfiability gives
an inverse-size gap, not a constant gap. No PCP theorem is assumed or claimed.
-/

namespace MaxCutGames.Foundations.PCP.InitialGraph

open Target

def variableLabel (value : Bool) : Label := (value, false, false)

end MaxCutGames.Foundations.PCP.InitialGraph

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RawInitialTables
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

/-!
A stable type of finite graphs over one fixed alphabet. Vertex and dart types,
their finite enumeration and equality data, and the actual constraint graph
are stored together. The gap is computed from that graph's actual finite
labeling minimum. This mathematical bundle is not a serialized machine input;
no finite numbering is chosen here.
-/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

/-!
The finite iteration and size arithmetic for an amplification transformation.
The transformation itself must be supplied by the actual graph construction;
these theorems do not assert that such a transformation exists.  In particular,
the polynomial size estimate below is not a machine runtime certificate.
-/

namespace MaxCutGames.Foundations.PCP.AmplificationIteration

theorem run_preserves {X : Type*} (step : X → X) (P : X → Prop)
    (preserves : ∀ x, P x → P (step x)) (n : Nat) (x : X) (hx : P x) :
    P (run step n x) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact preserves _ ih

end MaxCutGames.Foundations.PCP.AmplificationIteration

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Clone100Counting
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete clone sample space. Global distinctness is a stronger
conditioning rule than distinctness only at repeated original «variables».
It retains the same 3/100 bound and makes the number of copies uniform. -/

namespace MaxCutGames.Outer.Clone100

open MaxCutGames.Reduction CloneGap
open Clone100Triples Clone100Counting
open scoped BigOperators

noncomputable section

def lift {n : Nat} (a : Fin n → Bool) : Fin (n * 100) → Bool :=
  fun v => a ((nameEquiv n).symm v).1

def majority {n : Nat} (a : Fin (n * 100) → Bool) : Fin n → Bool :=
  fun v => majorityBit (fun i => a (nameEquiv n (v, i)))

end
end MaxCutGames.Outer.Clone100

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinishBounds
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Scalar estimates for the last paragraph of the v2 construction. These lemmas
only perform the stated rounding/subdivision/repetition arithmetic; they do
not assume or assert an unproved repetition theorem or hardness result.
-/

/-!
The outer error parameters are fixed before the latent gadget or its alphabet.
We use the same positive reciprocal integer for the latent noise budget and
the rounding tolerance. This permitted specialization makes uniform occurrence
rounding an exact fixed-copy operation. The later parity error is chosen only
after the tuple length has been fixed.
-/

namespace MaxCutGames.ParameterSelection
noncomputable section

namespace OuterParameters

variable {ε δ : ℝ} (P : OuterParameters ε δ)

theorem exists_parity_error (k : ℕ) (hk : 0 < k) :
    ∃ ξ : ℚ, 0 < ξ ∧ ξ < 1 / 100 ∧
      ξ < P.epsilon0 / (2 * k * P.repetitions) := by
  have hdenom : (0 : ℚ) < 2 * k * P.repetitions := by
    exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast hk))
      (by exact_mod_cast P.repetitions_pos)
  let ξ := min (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions)) / 2
  have hmin : 0 < min (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions)) :=
    lt_min (by norm_num) (div_pos P.epsilon0_pos hdenom)
  refine ⟨ξ, div_pos hmin (by norm_num), ?_, ?_⟩
  · have hle := min_le_left (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions))
    dsimp [ξ]
    linarith
  · have hle := min_le_right (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions))
    dsimp [ξ]
    linarith

/-- Both matrix-test completeness losses fit the budget fixed before the
alphabet, for the later chosen positive tuple length. -/
theorem matrix_error_budget (k : ℕ) (hk : 0 < k) (ξ : ℚ)
    (hξ : ξ ≤ P.epsilon0 / (2 * k * P.repetitions)) :
    (k : ℚ) * ξ + P.pStar / 2 ≤ P.epsilon0 / P.repetitions := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have htq : (0 : ℚ) < P.repetitions := by exact_mod_cast P.repetitions_pos
  have hx := (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hkq) htq)).mp hξ
  have hp := (le_div_iff₀ htq).mp P.reciprocal_budget
  apply (le_div_iff₀ htq).mpr
  dsimp [pStar]
  nlinarith

end OuterParameters
end
end MaxCutGames.ParameterSelection

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSBasisComparisonNeighborsFiberFunctional
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Binary linear functionals are determined by their kernels. The statement
includes the zero functional; no choice of a nonzero normalization is needed.
Injective linear images retain the same uniqueness property.
-/

/-!
The complete pair fiber of the ordered-basis neighbor sampler. Equal updated
images determine the binary functional exactly. The remaining ambiguity is
the affine kernel coset, of cardinality `2 ^ (dim E - 1)`.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

/-!
# Constant ordered-basis fibers

An injective linear map with a fixed range is exactly an ordered basis of that
range. Choosing one such basis identifies this fiber with the automorphisms of
the domain. The generic finite-fiber lemma below proves uniformity, including
the complete normalization in the rational density identity.
-/

noncomputable section
open scoped BigOperators Classical

/-- Every Grassmann vertex admits an ordered basis of the prescribed domain. -/
def vertexBasis {n ell : ℕ} (L : KMS.Vertex n ell) :
    KMS.Ambient ell ≃ₗ[KMS.F2] L.val :=
  LinearEquiv.ofFinrankEq _ _ (by simpa [KMS.Ambient] using L.property.symm)

instance basisAutomorphismFinite (ell : ℕ) :
    Finite (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
  Finite.of_injective
    (fun e : KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell =>
      (e : KMS.Ambient ell → KMS.Ambient ell)) DFunLike.coe_injective

instance basisAutomorphismFintype (ell : ℕ) :
    Fintype (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) := Fintype.ofFinite _

/-- The range quotient restricted to the lifted event itself. -/
def liftRange {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : lift S) : S :=
  ⟨rangeVertex X.val (injective_of_inLift ((mem_lift S X.val).mp X.property)),
    (inLift_iff_rangeVertex_mem S X.val _).mp ((mem_lift S X.val).mp X.property)⟩

def liftRangeFiberEquiv {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) (L : S) :
    {X : lift S // liftRange S X = L} ≃
      RangeFiber (E := KMS.Ambient ell) L.val.val where
  toFun X := ⟨X.val.val, injective_of_inLift ((mem_lift S X.val.val).mp X.val.property),
    congrArg (fun Z : S => Z.val.val) X.property⟩
  invFun X := ⟨⟨X.val, (mem_lift S X.val).mpr ⟨L.val, L.property, X.property.2⟩⟩,
    Subtype.ext (Subtype.ext X.property.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def liftRangeFiberAut {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) (L : S) :
    {X : lift S // liftRange S X = L} ≃
      (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
  (liftRangeFiberEquiv S L).trans (rangeFiberEquivAut (vertexBasis L.val))

end
end MaxCutGames.Inverse.KMSBasisComparison

/-!
Rank-one differences parametrize the actual Grassmann neighbors that remain
in the matrix chart. The equivalences retain the graph subspaces themselves,
so cardinalities and uniform sampling can be transported to the graph.
-/

/-! Exact chart-to-Grassmann degree comparison over the binary field. -/

/-! Concrete matrix coordinates for the graph chart. In particular the upper
interval equations become `M q = t`, while the lower equations become `dᵀ M = sᵀ`.
The right-hand sides are retained; none of these slices is required to be linear.
-/

/-! Transport the product-coordinate chart into the actual Grassmann vertices
used by the KMS boundary. The transport is a proved ambient linear equivalence.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Matrix

/-- A matrix as an actual Grassmann vertex on `ell + m` binary coordinates. -/
def matrixVertex {ell m : Nat} (M : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    KMS.Vertex (ell + m) ell :=
  ⟨(matrixGraph M).map (coordinateJoin (ZMod 2) ell m).toLinearMap, by
    rw [LinearEquiv.finrank_map_eq, finrank_matrixGraph, Fintype.card_fin]⟩

theorem matrixVertex_injective {ell m : Nat} :
    Function.Injective (matrixVertex (ell := ell) (m := m)) := by
  intro M N h
  apply matrixGraph_injective
  apply Submodule.map_injective_of_injective (coordinateJoin (ZMod 2) ell m).injective
  exact congrArg Subtype.val h

theorem finrank_matrixVertex_intersection {ell m : Nat}
    (M N : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    Module.finrank (ZMod 2) ((matrixVertex M).val ⊓ (matrixVertex N).val :
      Submodule (ZMod 2) (KMS.Ambient (ell + m))) =
      Module.finrank (ZMod 2) (matrixGraph M ⊓ matrixGraph N :
        Submodule (ZMod 2) ((Fin ell → ZMod 2) × (Fin m → ZMod 2))) := by
  change Module.finrank (ZMod 2)
    ((matrixGraph M).map (coordinateJoin (ZMod 2) ell m).toLinearMap ⊓
      (matrixGraph N).map (coordinateJoin (ZMod 2) ell m).toLinearMap :
        Submodule (ZMod 2) (KMS.Ambient (ell + m))) = _
  rw [← Submodule.map_inf _ (coordinateJoin (ZMod 2) ell m).injective,
    LinearEquiv.finrank_map_eq]

/-- Exact correspondence with the KMS adjacency predicate, including its
explicit inequality requirement. -/
theorem adjacent_matrixVertex_iff {ell m : Nat}
    (M N : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    KMS.Adjacent (matrixVertex M) (matrixVertex N) ↔
      Module.finrank (ZMod 2) (LinearMap.range (M.vecMulLinear - N.vecMulLinear)) = 1 := by
  have hdim : Module.finrank (ZMod 2) (Fin ell → ZMod 2) = ell := by simp
  constructor
  · intro h
    apply (adjacent_iff_rank_one M.vecMulLinear N.vecMulLinear).mp
    rw [hdim]
    rw [← finrank_matrixVertex_intersection M N]
    exact h.2
  · intro h
    refine ⟨?_, ?_⟩
    · intro heq
      have hMN : M = N := matrixVertex_injective heq
      subst N
      have hh := (adjacent_iff_rank_one M.vecMulLinear M.vecMulLinear).mpr h
      rw [inf_idem, finrank_graph] at hh
      omega
    · rw [finrank_matrixVertex_intersection]
      simpa only [hdim] using
        (adjacent_iff_rank_one M.vecMulLinear N.vecMulLinear).mpr h

noncomputable section

/-- The finite matrix chart in the Grassmann vertex type. -/
def matrixChart (ell m : Nat) : Finset (KMS.Vertex (ell + m) ell) := by
  classical
  exact Finset.univ.image (matrixVertex (ell := ell) (m := m))

@[simp] theorem mem_matrixChart {ell m : Nat} (L : KMS.Vertex (ell + m) ell) :
    L ∈ matrixChart ell m ↔
      ∃ M : Matrix (Fin ell) (Fin m) (ZMod 2), matrixVertex M = L := by
  classical
  simp [matrixChart]

end

end MaxCutGames.Inverse.MatrixChart

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RowErasure
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Inverse.RowErasure

section

open scoped BigOperators

def equalityAcceptance {X Y E : Type*} [Fintype E]
    (left right : E → X) (f : X → Y) : ℝ :=
  uniformMass fun e => f (left e) = f (right e)

open scoped BigOperators

variable {X Y A S D : Type*}

def SliceFamily.erasedUnion (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) : X → Prop :=
  goodUnion (F.goodAt f α)

/-- Only randomized entries count; an unchanged entry contributes zero, even
when its old label already matches the target. -/
def SliceFamily.randomizedAgreement (F : SliceFamily X Y A S D)
    (B : X → Prop) (replacement : X → Y) (d : D) : ℝ :=
  (F.points d).expect fun x => indicator (B x ∧ replacement x = F.target d x)

end

open scoped BigOperators Classical

end MaxCutGames.Inverse.RowErasure

/-!
`InversePrinciple` concerns an arbitrary table function, full uniform factor
sampling, and an affine intercept.
-/

namespace MaxCutGames.Inverse.Shortcode

open scoped BigOperators Classical

def Slice.constantAgreement {ell m : ℕ} (S : Slice ell m)
    (f : Mat ell m → Vector ell) (u : Vector ell) : ℝ :=
  S.points.expect fun M => if f M = u then 1 else 0

/-- Dimension-uniform inverse statement. The constants `α,r` depend only
on `η`; only the final input dimension threshold may depend on `ell`. There is
no folding assumption, and no inverse-theorem certificate is hidden in `f`. -/
def InversePrinciple : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∃ r : ℕ, 1 ≤ r ∧
      ∃ ell₀ : ℕ, ∀ ell : ℕ, ell₀ ≤ ell →
        ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
          ∀ f : Mat ell m → Vector ell,
            η ≤ equalityAcceptance f → HasAffineSlice f α r

end MaxCutGames.Inverse.Shortcode

/-!
Fixed-length descriptions for the row-erasure union bound. Row and column
equation lists are padded with zero equations. Targets retain both the linear
coefficient and the affine intercept. Thus the finite description count is
exactly `2^((2r+1)(ell+m))`, including descriptions with empty solution sets.
-/

namespace MaxCutGames.Inverse.RowErasureMatrix

open MaxCutGames.Inverse.Shortcode
open MaxCutGames.Inverse.RowErasure
open MaxCutGames.Inverse.RowErasureDescriptions
open scoped BigOperators Classical

abbrev Samples (ell m : ℕ) := Mat ell m × Vector ell × Vector m

def left {ell m : ℕ} (e : Samples ell m) : Mat ell m := e.1

def right {ell m : ℕ} (e : Samples ell m) : Mat ell m :=
  e.1 + rankOne e.2.1 e.2.2

/-- Translation of the sampled matrix is a permutation while the two sampled
factors remain fixed; this also covers either factor being zero. -/
def stepEquiv (ell m : ℕ) : Samples ell m ≃ Samples ell m where
  toFun e := (right e, e.2)
  invFun e := (e.1 - rankOne e.2.1 e.2.2, e.2)
  left_inv e := by
    apply Prod.ext
    · exact add_sub_cancel_right e.1 (rankOne e.2.1 e.2.2)
    · rfl
  right_inv e := by
    apply Prod.ext
    · exact sub_add_cancel e.1 (rankOne e.2.1 e.2.2)
    · rfl

end MaxCutGames.Inverse.RowErasureMatrix

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixChartKMSNeighbors
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-neighbor count in the KMS vertex representation. -/

namespace MaxCutGames.Inverse.MatrixChart

open Module

/-- Extrinsic submodule neighbors and the finite KMS neighbor predicate agree. -/
def kmsNeighborsEquiv {n ell : Nat} (L : KMS.Vertex n ell) :
    GrassmannNeighbors L.val ≃ {W : KMS.Vertex n ell // KMS.Adjacent L W} where
  toFun W := ⟨⟨W.val, W.property.1.trans L.property⟩, by
    refine ⟨?_, ?_⟩
    · intro h
      have hv := congrArg Subtype.val h
      have hd := W.property.2
      rw [← hv, inf_idem] at hd
      omega
    · exact W.property.2.trans L.property⟩
  invFun W := ⟨W.val.val, W.val.property.trans L.property.symm,
    W.property.2.trans L.property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MaxCutGames.Inverse.MatrixChart

/-! Local ordered-basis retention in the precise KMS vertex representation. -/

/-!
# Ordered-basis retention versus Grassmann retention

This is the sampling comparison in KMS Lemma 2.7. The original experiment
uses all functionals and all directions, including zero. Its good event
induces exactly the full Grassmann-neighbor law; all other outcomes contribute
at most their explicit probability mass. Initial bases push forward uniformly
to the original Grassmann set.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

/-- The complete rank-one update experiment at a specified starting map. -/
def fullStepRetention {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : ℝ :=
  𝔼 p : Functional ell × KMS.Ambient n,
    liftedIndicator S (rankOneUpdate X p.1 p.2)

/-- Start uniformly in the lifted set, then run the unconditioned update. -/
def liftRetention {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) : ℝ :=
  𝔼 X : lift S, fullStepRetention S X.val

/-- Equivalence of the two explicit presentations of the good sampling event. -/
def goodParametersEquiv {n ell : ℕ} (X : BasisMap n ell) :
    goodParameters X ≃ OutsideNeighborFactors X where
  toFun p := ⟨⟨p.val.1, ((mem_goodParameters X p.val).mp p.property).1⟩,
    ⟨p.val.2, ((mem_goodParameters X p.val).mp p.property).2⟩⟩
  invFun p := ⟨(p.1.val, p.2.val),
    (mem_goodParameters X _).mpr ⟨p.1.property, p.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The indicator's density in the full linear-map space. -/
def liftDensity {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) : ℝ :=
  𝔼 X : BasisMap n ell, liftedIndicator S X

end
end MaxCutGames.Inverse.KMSBasisComparison

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical
open KMSBasisComparisonPseudorandom

/-- The precise analytic obligation at the ordered-basis lift. Its constants
are fixed before the tuple length, which is fixed before the ambient size. -/
def LiftExpansionPrinciple : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∃ r ell₀ : ℕ, ∀ ell : ℕ, ell₀ ≤ ell →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∀ S : Finset (KMS.Vertex n ell), S.Nonempty →
            TuplePseudorandom S r ε → liftRetention S ≤ ζ

end
end MaxCutGames.Inverse.KMSBasisComparison

/-! The proved KMS Grassmann expansion principle. Its quantitative analytic
input is the actual basis-invariant fourth-moment theorem, whose proof uses
fixed-character and fixed-point inductions. No expansion, inverse,
rank-level, or missing-moment premise occurs in this theorem. -/

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

def matrixFiber {ell m : ℕ} (f : Mat ell m → Vector ell) (y : Vector ell) :
    Finset (Mat ell m) := Finset.univ.filter fun M => f M = y

def liftedFiber {ell m : ℕ} (f : Mat ell m → Vector ell) (y : Vector ell) :
    Finset (KMS.Vertex (ell + m) ell) := (matrixFiber f y).image matrixVertex

@[simp] theorem matrixVertex_mem_liftedFiber {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) (M : Mat ell m) :
    matrixVertex M ∈ liftedFiber f y ↔ f M = y := by
  constructor
  · intro h
    obtain ⟨N, hN, hNM⟩ := Finset.mem_image.mp h
    have : N = M := matrixVertex_injective hNM
    subst N
    exact (Finset.mem_filter.mp hN).2
  · intro h
    exact Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

/-! Every Grassmann interval has a chart description with exactly `dim A`
lower equations and `codim B` upper equations. This supplies the quantitative
row/column budget used when the expansion theorem selects an interval.
-/

/-! Extract actual vector-valued row/column data from an arbitrary interval.
The equation counts are the dimension/codimension of that interval, and no
homogeneity is imposed on the equation right-hand sides.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixChartShortcode
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete interface consumed by the shortcode assembly: an arbitrary
KMS interval becomes a `Shortcode.Slice`, with exact equation counts.
-/

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped Classical
open Shortcode MatrixChart

/-- Finite sampling bridge, stated on the actual equality test, actual
lifted output fibers, and actual Grassmann retention. The positive dimensions
exclude the degenerate empty-neighbor cases. No KMS or inverse principle is
part of this proposition. -/
def ChartFiberRetention : Prop :=
  ∀ {ell m : ℕ}, 1 ≤ ell → 1 ≤ m →
    ∀ η : ℝ, 0 < η → η < 1 → zeroFactorMass ell m ≤ η / 2 →
      ∀ f : Mat ell m → Vector ell, η ≤ equalityAcceptance f →
        ∃ y : Vector ell, (liftedFiber f y).Nonempty ∧
          η / 4 ≤ KMS.retention (liftedFiber f y)

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

/-!
The exact sampling bridge from the vector factors in the shortcode test
to actual KMS Grassmann vertices. Every nonzero vector pair is sent to the
matrix `M + rankOne a l`, and this is a bijection onto the chart neighbors.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Matrix
open Shortcode (Vector Mat rankOne)

variable {ell m : ℕ}

@[simp] theorem dotFunctional_zero_binary :
    dotFunctional (0 : Vector ell) = 0 := by
  apply LinearMap.ext
  intro x
  change (0 : Vector ell) ⬝ᵥ x = 0
  simp

theorem dotFunctional_ne_zero {a : Vector ell} (ha : a ≠ 0) :
    dotFunctional a ≠ 0 := by
  intro h
  exact ha (dotFunctional_injective (h.trans dotFunctional_zero_binary.symm))

/-- The shortcode outer product is precisely the rank-one chart map. -/
theorem vecMulLinear_rankOne (a : Vector ell) (l : Vector m) :
    (rankOne a l).vecMulLinear = (dotFunctional a).smulRight l := by
  apply LinearMap.ext
  intro x
  change x ᵥ* Matrix.vecMulVec a l = (a ⬝ᵥ x) • l
  rw [Matrix.vecMul_vecMulVec, dotProduct_comm x a]

/-- This is the exact perturbation, including its functional/vector order. -/
theorem vecMulLinear_add_rankOne (M : Mat ell m) (a : Vector ell) (l : Vector m) :
    (M + rankOne a l).vecMulLinear = M.vecMulLinear + (dotFunctional a).smulRight l := by
  apply LinearMap.ext
  intro x
  change x ᵥ* (M + rankOne a l) = M.vecMulLinear x +
    ((dotFunctional a).smulRight l) x
  rw [Matrix.vecMul_add]
  exact congrArg (fun y => M.vecMulLinear x + y)
    (LinearMap.congr_fun (vecMulLinear_rankOne a l) x)

theorem adjacent_matrixVertex_add_rankOne (M : Mat ell m)
    (a : Vector ell) (l : Vector m) (ha : a ≠ 0) (hl : l ≠ 0) :
    KMS.Adjacent (matrixVertex M) (matrixVertex (M + rankOne a l)) := by
  apply (adjacent_matrixVertex_iff M (M + rankOne a l)).mpr
  apply (adjacent_iff_rank_one M.vecMulLinear (M + rankOne a l).vecMulLinear).mp
  rw [vecMulLinear_add_rankOne]
  exact adjacent_rank_one_step M.vecMulLinear (dotFunctional a) l
    (dotFunctional_ne_zero ha) hl

abbrev NonzeroVectorFactors (ell m : ℕ) :=
  {a : Vector ell // a ≠ 0} × {l : Vector m // l ≠ 0}

/-- Actual Grassmann vertices adjacent to `matrixVertex M` and remaining
inside the finite matrix chart. -/
abbrev MatrixVertexChartNeighbors (M : Mat ell m) :=
  {L : KMS.Vertex (ell + m) ell //
    KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m}

def vectorFactorMatrixNeighbor (M : Mat ell m) (p : NonzeroVectorFactors ell m) :
    MatrixVertexChartNeighbors M :=
  ⟨matrixVertex (M + rankOne p.1.val p.2.val),
    adjacent_matrixVertex_add_rankOne M p.1.val p.2.val p.1.property p.2.property,
    (mem_matrixChart _).mpr ⟨M + rankOne p.1.val p.2.val, rfl⟩⟩

theorem vectorFactorMatrixNeighbor_injective (M : Mat ell m) :
    Function.Injective (vectorFactorMatrixNeighbor M) := by
  intro p q h
  have hM : M + rankOne p.1.val p.2.val = M + rankOne q.1.val q.2.val :=
    matrixVertex_injective (congrArg Subtype.val h)
  have hrank := congrArg Matrix.vecMulLinear (add_left_cancel hM)
  rw [vecMulLinear_rankOne, vecMulLinear_rankOne] at hrank
  obtain ⟨ha, hl⟩ := binary_smulRight_unique (dotFunctional_ne_zero p.1.property)
    p.2.property hrank
  exact Prod.ext (Subtype.ext (dotFunctional_injective ha)) (Subtype.ext hl)

theorem vectorFactorMatrixNeighbor_surjective (M : Mat ell m) :
    Function.Surjective (vectorFactorMatrixNeighbor M) := by
  intro L
  obtain ⟨N, hN⟩ := (mem_matrixChart L.val).mp L.property.2
  have hMN : KMS.Adjacent (matrixVertex M) (matrixVertex N) := by
    rw [hN]
    exact L.property.1
  have hNM : KMS.Adjacent (matrixVertex N) (matrixVertex M) :=
    ⟨hMN.1.symm, by rw [inf_comm]; exact hMN.2⟩
  obtain ⟨a, l, ha, hl, hfactor⟩ := exists_smulRight_of_rank_one
    (N.vecMulLinear - M.vecMulLinear) ((adjacent_matrixVertex_iff N M).mp hNM)
  obtain ⟨v, hv⟩ := dotFunctional_surjective a
  have hv0 : v ≠ 0 := by
    intro h
    apply ha
    rw [← hv, h, dotFunctional_zero_binary]
  have hmatrix : M + rankOne v l = N := by
    apply (LinearMap.toMatrixRight' (R := ZMod 2)).symm.injective
    change (M + rankOne v l).vecMulLinear = N.vecMulLinear
    rw [vecMulLinear_add_rankOne, hv]
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hfactor).symm
  refine ⟨(⟨v, hv0⟩, ⟨l, hl⟩), ?_⟩
  apply Subtype.ext
  change matrixVertex (M + rankOne v l) = L.val
  rw [hmatrix]
  exact hN

/-- Uniform independent nonzero vector factors induce exactly uniform
neighbors of the actual Grassmann vertex within the matrix chart. -/
noncomputable def vectorFactorsEquivMatrixVertexChartNeighbors (M : Mat ell m) :
    NonzeroVectorFactors ell m ≃ MatrixVertexChartNeighbors M :=
  Equiv.ofBijective (vectorFactorMatrixNeighbor M)
    ⟨vectorFactorMatrixNeighbor_injective M, vectorFactorMatrixNeighbor_surjective M⟩

@[simp] theorem vectorFactorsEquivMatrixVertexChartNeighbors_apply (M : Mat ell m)
    (p : NonzeroVectorFactors ell m) :
    (vectorFactorsEquivMatrixVertexChartNeighbors M p).val =
      matrixVertex (M + rankOne p.1.val p.2.val) := rfl

end MaxCutGames.Inverse.MatrixChart

/-!
The exact finite sampling conversion in the shortcode proof. Independent
nonzero binary vector factors parametrize chart neighbors bijectively; the full
Grassmann degree is twice the chart degree. These identities imply the exact
factor one half, including its averaging over a nonempty output fiber.
-/

/-!
Finite equality-fiber extraction for the Grassmann-to-matrix route.

These elementary results do not assume a shortcode inverse theorem.  They
separate the equality test, the retention of a nonempty output fiber, and the
subsequent removal of zero perturbation factors.  The dimension-uniform
Grassmann expansion theorem remains a separate mathematical obligation.
-/

/-! The actual uniform matrix test supplies a positive-mass output fiber with
large retention. The transition kernel averages independent full vectors,
including zero, exactly as in the shortcode theorem. -/

namespace MaxCutGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Foundations.Information

def matrixWeight {ell m : ℕ} (_ : Mat ell m) : ℝ :=
  (Fintype.card (Mat ell m) : ℝ)⁻¹

def matrixKernel {ell m : ℕ} (M N : Mat ell m) : ℝ :=
  𝔼 a : Vector ell, 𝔼 l : Vector m,
    if N = M + rankOne a l then 1 else 0

end
end MaxCutGames.Inverse.Shortcode

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RowErasureConcentration
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Inverse.RowErasure

open scoped BigOperators Classical

def randomizedMatches {X Y : Type*} (s : Finset X) (B : X → Prop)
    (target replacement : X → Y) : ℝ :=
  ∑ x ∈ s, indicator (B x ∧ replacement x = target x)

end MaxCutGames.Inverse.RowErasure

/-!
The row-erasure union bound is eventually strictly below one. The number of
descriptions grows exponentially in `m`, while the tail exponent grows as
`2 ^ ((ell-r)*(m-r))`. The only asymptotic input is the standard proved limit
that a fixed polynomial divided by `2^n` tends to zero.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RowErasureSelection
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Visible selection of a row-erasure witness. The selected description depends
only on the fixed table function, the row map, and the observed row value.
The full sampled matrix enters only the later event testing its membership in
the already selected slice. Classical choice fixes one witness once and for all;
proof irrelevance makes the choice independent of the goodness proof.
-/

/-!
Finite partition estimates for a selector fixed by visible data. The observation
fibers need not have equal sizes. Each local counting inequality is summed over
the actual fibers, then divided by the size of the hidden sample space.
-/

/-!
Exact mass of a nonempty column slice within a fixed row-advice fiber. A
column span of dimension at most `r` costs at most `ell*r` binary degrees of
freedom. All inhomogeneous values are represented by the chosen base point.
-/

/-!
Exact uniform parametrization of the concrete row/column slice.  The quotient
parameter describes every point, not only a lower-bounding subfamily.  Affine
targets retain the base-point contribution and their original intercept.
-/

namespace MaxCutGames.Inverse.Shortcode.Slice

open scoped BigOperators Matrix

variable {ell m : ℕ}

instance directionsFintype (S : Slice ell m) : Fintype S.Directions := by
  classical
  letI : Fintype (Vector m ⧸ S.columnSpan) := Fintype.ofFinite _
  letI : Fintype S.rowMap.ker := Fintype.ofFinite _
  exact Fintype.ofInjective
    (fun N : S.Directions => (N : (Vector m ⧸ S.columnSpan) → S.rowMap.ker))
    DFunLike.coe_injective

end MaxCutGames.Inverse.Shortcode.Slice

/-!
The actual finite matrix column event occupies at least `2^(-ell*r)` of its
row-advice fiber. This connects the intrinsic quotient-map count to the padded
descriptions used by the selector, without assuming independent equations.
-/

namespace MaxCutGames.Inverse.RowErasureDescriptionColumnMass

open MaxCutGames.Inverse.Shortcode
open MaxCutGames.Inverse.RowErasureDescriptions
open MaxCutGames.Inverse.RowErasureMatrix
open scoped BigOperators Classical

/-- Forget only the column equations of a slice. -/
def rowOnly {ell m : ℕ} (S : Slice ell m) : Slice ell m where
  rows := S.rows
  columns := 0
  rowCoefficient := S.rowCoefficient
  rowValue := S.rowValue
  columnCoefficient := Fin.elim0
  columnValue := Fin.elim0

end MaxCutGames.Inverse.RowErasureDescriptionColumnMass

/-!
The selected column event under the actual uniform matrix and row-map samples.
The witness is fixed by visible row advice before testing the hidden matrix.
Fiber sizes are retained explicitly; no uniformity of row values is assumed.
The final averaging lemmas also allow arbitrary nonnegative context weights.
-/

namespace MaxCutGames.Inverse.RowErasure

open scoped BigOperators

variable {X Y A S D : Type*}

def SliceFamily.selectedPoints (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) : Finset X :=
  match F.selectedDescription f α a s with
  | none => ∅
  | some d => F.points d

def SliceFamily.selectedHit (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a s = some d ∧ f x = F.target d x

end MaxCutGames.Inverse.RowErasure

namespace MaxCutGames.Inverse.RowErasureMatrix

open MaxCutGames.Inverse.Shortcode
open MaxCutGames.Inverse.RowErasure
open MaxCutGames.Inverse.RowErasureDescriptions
open MaxCutGames.Inverse.RowErasureDescriptionColumnMass
open scoped BigOperators

variable {ell m r : ℕ}

def selectedEventMass (r : ℕ) (f : Mat ell m → Vector ell) (α : ℝ) : ℝ :=
  𝔼 A : RowMap ell r, uniformMass ((family ell m r).selectedEvent f α A)

def selectedMatchMass (r : ℕ) (f : Mat ell m → Vector ell) (α : ℝ) : ℝ :=
  𝔼 A : RowMap ell r, uniformMass ((family ell m r).selectedMatch f α A)

end MaxCutGames.Inverse.RowErasureMatrix

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_SeparationCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A single finite polynomial certifies injectivity and pair separation of
the actual binary-linear parametrization. -/

/-!
Uniform injective parameter maps induce the uniform law on subspaces of the
specified rank.  The proof uses actual transitivity of ambient linear
automorphisms on injections, not an assumed distributional premise.
-/

section

open scoped BigOperators
open Module
open MaxCutGames.Gadget.Orientation

namespace MaxCutGames.Quadratic.UniformSubspaces

variable {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The image has the dimension of the parameter space. -/
def image (J : Injection K V W) : RankSpace K W (finrank K V) :=
  ⟨LinearMap.range J.val, LinearMap.finrank_range_of_inj J.property⟩

end MaxCutGames.Quadratic.UniformSubspaces
end

/-!
The polynomial exceptional-event bound is transported first to all binary
linear parameter maps and then, by proved uniformity conditional on
injectivity, to the actual finite Grassmannian.  The same argument supplies
a generic subspace, rather than presupposing that one exists.
-/

open Module
open MaxCutGames.Gadget.Orientation

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_ShortcodeFiberSampling
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite output-fiber sampling identities. These connect the weighted
kernel extraction to uniform sampling of a matrix in the actual output fiber.
-/

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MaxCutGames.Foundations.Information

def fiberFactorRetention {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) (a : Vector ell) (l : Vector m) : ℝ :=
  (matrixFiber f y).expect fun M => if f (M + rankOne a l) = y then 1 else 0

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

/-! The unconditional affine matrix inverse theorem. The Grassmann theorem,
chart retention, zero-factor correction, output-fiber extraction, and affine
row/column slice construction are all proved in its dependency chain. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_StageNoiseRecurrence
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact finite-stage nonlinear noise law

This packages the one-level recurrence for the actual recursive `Stage`, solves
it at every height, and proves that the ambient-kernel quotient preserves it.
The averaged block kernel remains an explicit argument for later instantiation
with the concrete quadratic family.
-/

namespace MaxCutGames.Gadget.StageNoiseRecurrence

open scoped BigOperators

universe u v

variable {k : Type u} {B : Type v} [CommRing k] [AddCommGroup B] [Module k B]

/-- Uniform finite input and the stage's actual uniform finite noise choices. -/
noncomputable def error (s : Stage k B) : ℚ := by
  classical
  exact average (fun n : s.Noise => average (fun u : s.Input =>
    if s.output (u + s.noise n) ≠ s.output u then 1 else 0))

end MaxCutGames.Gadget.StageNoiseRecurrence

/-!
The spanning clause of v2 Lemma `latent-block`.  Three coordinate lines
already suffice.  Horizontal coordinate vectors lie in their own block;
vertical coordinate vectors lie in either of the other two blocks.
-/

namespace MaxCutGames.Quadratic

variable {F : Type*} [Field F]

/-- The three standard coordinate vectors of the quadratic block. -/
def basisCoord (i : Fin 3) : Vec F := Pi.single i 1

theorem basisCoord_ne_zero (i : Fin 3) : (basisCoord i : Vec F) ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [basisCoord] at hi

@[simp] theorem Q_smul_basisCoord (t : F) (i : Fin 3) :
    Q (t • (basisCoord i : Vec F)) = 0 := by
  ext k
  fin_cases i <;> fin_cases k <;> simp [Q, basisCoord]

theorem dot_smul_basisCoord_of_ne (t : F) (i j : Fin 3) (hij : i ≠ j) :
    dot (basisCoord j : Vec F) (t • (basisCoord i : Vec F)) = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [dot, basisCoord]

variable [CharP F 2] [Algebra (ZMod 2) F]

theorem horizontal_mem_U_basisCoord (t : F) (i : Fin 3) :
    (t • basisCoord i, (0 : Vec F)) ∈ U (basisCoord i) := by
  refine ⟨(mem_line_iff _ _).mpr ⟨t, rfl⟩, ?_⟩
  change dot (basisCoord i) (0 + Q (t • basisCoord i)) = 0
  simp

theorem vertical_mem_U_basisCoord_of_ne (t : F) (i j : Fin 3) (hij : i ≠ j) :
    ((0 : Vec F), t • basisCoord i) ∈ U (basisCoord j) := by
  refine ⟨(line _).zero_mem, ?_⟩
  change dot (basisCoord j) (t • basisCoord i + Q 0) = 0
  simpa using dot_smul_basisCoord_of_ne t i j hij

/-- The binary span of the three coordinate block spaces. -/
def coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F) :=
  (U (basisCoord 0) ⊔ U (basisCoord 1)) ⊔ U (basisCoord 2)

theorem U_basisCoord_le_coordinateBlockSpan (i : Fin 3) :
    U (basisCoord i) ≤ (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  fin_cases i
  · exact le_trans le_sup_left le_sup_left
  · exact le_trans le_sup_right le_sup_left
  · exact le_sup_right

theorem horizontal_mem_coordinateBlockSpan (t : F) (i : Fin 3) :
    (t • basisCoord i, (0 : Vec F)) ∈
      (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) :=
  U_basisCoord_le_coordinateBlockSpan i (horizontal_mem_U_basisCoord t i)

theorem vertical_mem_coordinateBlockSpan (t : F) (i : Fin 3) :
    ((0 : Vec F), t • basisCoord i) ∈
      (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  have h (j : Fin 3) (hij : i ≠ j) :
      ((0 : Vec F), t • basisCoord i) ∈
        (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) :=
    U_basisCoord_le_coordinateBlockSpan j (vertical_mem_U_basisCoord_of_ne t i j hij)
  fin_cases i
  · exact h 1 (by decide)
  · exact h 0 (by decide)
  · exact h 0 (by decide)

/-- Every pair is a sum of three horizontal and three vertical coordinate
pairs, all already in the sum of the coordinate blocks. -/
theorem mem_coordinateBlockSpan (p : Vec F × Vec F) :
    p ∈ (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  let S : Submodule (ZMod 2) (Vec F × Vec F) := coordinateBlockSpan
  have hh : (p.1, (0 : Vec F)) ∈ S := by
    have h := S.add_mem
      (S.add_mem (horizontal_mem_coordinateBlockSpan (p.1 0) 0)
        (horizontal_mem_coordinateBlockSpan (p.1 1) 1))
      (horizontal_mem_coordinateBlockSpan (p.1 2) 2)
    convert h using 1 ; ext i <;> fin_cases i <;> simp [basisCoord]
  have hv : ((0 : Vec F), p.2) ∈ S := by
    have h := S.add_mem
      (S.add_mem (vertical_mem_coordinateBlockSpan (p.2 0) 0)
        (vertical_mem_coordinateBlockSpan (p.2 1) 1))
      (vertical_mem_coordinateBlockSpan (p.2 2) 2)
    convert h using 1 ; ext i <;> fin_cases i <;> simp [basisCoord]
  have h := S.add_mem hh hv
  simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta] using h

theorem coordinateBlockSpan_eq_top :
    (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) = ⊤ := by
  apply top_unique
  intro p _
  exact mem_coordinateBlockSpan p

/-- The block spaces for all nonzero line generators span the whole ambient
binary vector space.  The proof uses just the three coordinate generators. -/
theorem iSup_U_nonzero_eq_top :
    (⨆ v : {v : Vec F // v ≠ 0}, U v.1) = ⊤ := by
  apply top_unique
  rw [← coordinateBlockSpan_eq_top (F := F)]
  unfold coordinateBlockSpan
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 0, basisCoord_ne_zero 0⟩
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 1, basisCoord_ne_zero 1⟩
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 2, basisCoord_ne_zero 2⟩

end MaxCutGames.Quadratic

/-! Surjectivity of the actual all-lines/all-orientations parent aggregate. -/

noncomputable section

open scoped BigOperators

namespace MaxCutGames.Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [Fintype (BlockOrientationIndex F)]

def blockEmbedding (i : BlockOrientationIndex F) :
    Vec F →ₗ[ZMod 2] Vec F × Vec F :=
  (U (lineGenerator i.1)).subtype.comp i.2.toLinearMap

def blockAggregate : (BlockOrientationIndex F → Vec F) →ₗ[ZMod 2] Vec F × Vec F :=
  Gadget.aggregate (blockEmbedding (F := F))

theorem blockAggregate_single [DecidableEq (BlockOrientationIndex F)]
    (i : BlockOrientationIndex F) (b : Vec F) :
    blockAggregate (Pi.single i b) = blockEmbedding i b := by
  classical
  change (∑ j : BlockOrientationIndex F,
    blockEmbedding j ((Pi.single i b : BlockOrientationIndex F → Vec F) j)) = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem fieldLine_block_le_range_aggregate (A : FieldLine F) :
    U (lineGenerator A) ≤ LinearMap.range (blockAggregate (F := F)) := by
  classical
  intro p hp
  let J := chosenBlockOrientation A
  let i : BlockOrientationIndex F := ⟨A, J⟩
  obtain ⟨b, hb⟩ := J.surjective ⟨p, hp⟩
  refine ⟨Pi.single i b, ?_⟩
  rw [blockAggregate_single]
  change ((J b : U (lineGenerator A)) : Vec F × Vec F) = p
  exact congrArg Subtype.val hb

/-- All blocks occur in the actual pair-indexed aggregate.  Their already
proved span is the entire horizontal/vertical space, so the aggregate is
surjective, as required by the recursive shift construction. -/
theorem blockAggregate_surjective : Function.Surjective (blockAggregate (F := F)) := by
  have hspan : (⨆ v : {v : Vec F // v ≠ 0}, U v.1) ≤
      LinearMap.range (blockAggregate (F := F)) := by
    apply iSup_le
    intro v
    let A : FieldLine F := Projectivization.mk F v.1 v.2
    have hl : line (lineGenerator A) = line v.1 := by
      simpa only [A, Projectivization.submodule_mk, line] using line_lineGenerator A
    have hm : lineGenerator A ∈ line v.1 := by
      rw [← hl]
      exact (mem_line_iff _ _).mpr ⟨1, one_smul _ _⟩
    have hu := U_eq_of_nonzero_mem_line (lineGenerator_ne_zero A) hm
    simpa only [hu] using fieldLine_block_le_range_aggregate A
  rw [iSup_U_nonzero_eq_top] at hspan
  exact LinearMap.range_eq_top.mp (top_unique hspan)

theorem aggregate_blockEmbedding_surjective :
    Function.Surjective (Gadget.aggregate (blockEmbedding (F := F))) :=
  blockAggregate_surjective

end MaxCutGames.Quadratic
end

noncomputable section

namespace MaxCutGames.Gadget.QuadraticStageNoise

open scoped BigOperators Classical
open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance indexDecidableEq : DecidableEq (BlockOrientationIndex F) := Classical.decEq _

local instance automorphismFinite : Finite (Vec F ≃ₗ[ZMod 2] Vec F) := DFunLike.finite _
noncomputable local instance automorphismFintype : Fintype (Vec F ≃ₗ[ZMod 2] Vec F) :=
  Fintype.ofFinite _

local instance indexNonempty : Nonempty (BlockOrientationIndex F) := by
  have hA : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  obtain ⟨A⟩ := hA
  exact ⟨⟨A, chosenBlockOrientation A⟩⟩

/-- The actual recursive spaces, shifts, outputs and finite leaf-noise sampler. -/
noncomputable def stage (n : ℕ) : Stage (ZMod 2) (Vec F) :=
  Stage.iterate (blockEmbedding (F := F)) aggregate_blockEmbedding_surjective Q n

/-- The logical alphabet is an actual injected shift subspace after quotient. -/
noncomputable def quotientStage (n : ℕ) : Stage (ZMod 2) (Vec F) :=
  StageQuotient.toStage (stage (F := F) n)

end MaxCutGames.Gadget.QuadraticStageNoise
end

namespace MaxCutGames.Gadget.Parameters

open Harmonic
open scoped BigOperators

/-- Strictly positive genericity error meeting the MaxCutGames.Gadget.Harmonic.harmonic bad-rank budget. -/
def genericityError (r₀ : ℕ) : ℚ := 1 / (2 * (badRankCoefficient r₀ + 1))

end MaxCutGames.Gadget.Parameters

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_FramedLen
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine
open scoped BigOperators
namespace Expr

def framedLen (n : Expr) : Expr := .add (.mul (.const 2) (size n)) (.const 1)
def framedBit (n i : Expr) : Expr := cond (lt i (.mul (.const 2) (size n)))
  (cond (equal (remainder i (.const 2)) (.const 0)) (.const 1)
    (digit n (quotient i (.const 2)))) (.const 0)

end Expr

@[simp] theorem frame_length (s : List Bool) : (frame s).length = 2*s.length+1 := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [frame, ih]; omega

end OptimalMaxCut.CounterMachine

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Printer
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine
open Turing Polynomial Command

def printer (len bit : Expr) : Command ℕ := .seq (print len bit) eraseInput

noncomputable def printerTime (len bit : Expr) : Polynomial ℕ :=
  len.timePolynomial+len.valuePolynomial*
    (bit.timePolynomial.comp (X+len.valuePolynomial)+
      2*bit.valuePolynomial.comp (X+len.valuePolynomial)+4)+1+7*X+8

 theorem printer_evaluates (len bit : Expr) (input : List Bool) :
    Within (printer len bit) (initial input)
      ⟨fun _ => 0, [], [], table len bit input⟩ ((printerTime len bit).eval input.length-1) := by
  have hp := print_evaluates len bit input
  have he := eraseInput_evaluates {initial input with output := table len bit input}
    (by intro r hr; rfl) rfl
  have h := hp.seq he
  apply h.mono
  simp only [printerTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_comp, Expr.timePolynomial_eval, Expr.valuePolynomial_eval]

  simp only [initial] at *
  omega

 theorem halted_eq {R : Type} [DecidableEq R] [Fintype R] (c : Command R) (out : List Bool) :
    embed (⟨⟨fun _ => 0, [], [], out⟩, none⟩ : Configuration R c.FinalLabel) =
      haltList c.finiteMachine out := by
  unfold embed haltList
  congr 1
  funext k
  cases k <;> simp [tapes, finiteMachine, machine]
  rfl

/-- A genuine polynomial-time finite Boolean-tape Turing machine for any closed
bounded-arithmetic bit table. This is an operational theorem, not a closure
axiom or a unit-cost machine convention. -/
noncomputable def tableComputer (len bit : Expr) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id (table len bit) where
  tm := (printer len bit).finite.finiteMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := printerTime len bit
  outputsFun input := by
    let h := printer_evaluates len bit input
    let n := Classical.choose h
    have hn := Classical.choose_spec h
    have he := Command.finite_evaluates hn.2
    change Evaluates _ (initial input) ⟨fun _ => 0, [], [], table len bit input⟩ n at he
    have run := machine_run he
    have hout := halted_eq (printer len bit).finite (table len bit input)
    have run' : StateTransition.EvalsToInTime (printer len bit).finite.finiteMachine.step
        (initList (printer len bit).finite.finiteMachine input)
        (some (haltList (printer len bit).finite.finiteMachine (table len bit input))) (n+1) := by
      convert run using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      unfold haltList embed
      congr 1
      funext k
      cases k <;> simp [tapes, finiteMachine, machine]
      rfl
    let run := run'
    refine ⟨⟨run.steps, ?_⟩, ?_⟩
    · change (flip Option.bind (printer len bit).finite.finiteMachine.step)^[run.steps]
        (some (initList (printer len bit).finite.finiteMachine (input.map (id : Bool → Bool)))) =
        some (haltList (printer len bit).finite.finiteMachine ((table len bit input).map (id : Bool → Bool)))
      erw [List.map_id, List.map_id]
      exact run.evals_in_steps
    · have hs := run.steps_le_m
      have hb := hn.1
      have hp : 0 < (printerTime len bit).eval input.length := by
        simp only [printerTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
          Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_comp, Expr.timePolynomial_eval, Expr.valuePolynomial_eval]
        omega
      change run.steps ≤ (printerTime len bit).eval input.length
      omega

end OptimalMaxCut.CounterMachine

end

end OAI
end


