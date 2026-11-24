-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EntriesWellDefined
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_EntriesWellDefined
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:51.755294+00:00
-- url     : https://prove2.me/theorems/98a81e28-7980-4baf-b2c3-8f5752647c6a
-- title:
--   Entries Well Defined
-- statement:
--   Definitions and structural lemmas for Entries Well Defined, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EntriesWellDefined.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsCOPrXCgrpStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsParabolicDoubleCosetFunctionEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentExistsResidueCardPowMemNhdsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarCompactOpenRatioEqZpowOfTopNilpotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParabolicHaarVolumeConjIntersectionEqMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralTranslateIndicatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsQuotIntCosetFnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsAdaptedExponentSchwartzBruhatLastColumnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteQuotientCosetsScaledStandardLatticeBoxStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGenericLevelOfFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GenericLevelOfFrameBlockAndCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SymmetricPositionLevelShapeOnParabolicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexIteratedLevelChainInFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexParahoricLevelChainTwistStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology
open scoped ENNReal
noncomputable section
namespace GlobalTheory.UnfoldedEntries
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
section Basic
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
end Basic
section Step
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k}
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
  {μ : kˣ →* ℂˣ} {P' : Level (GL (n' ⊕ Fin (c + 1)) k)} {P : Level (GL (n ⊕ Fin c) k)}
  {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
variable [ν.IsAddHaarMeasure]
end Step
section Laws
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
end Laws
section Volumes
variable [MeasurableSpace k] [BorelSpace k] {ν : Measure k} [ν.IsAddHaarMeasure]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
end Volumes
section First
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]
end First
end GlobalTheory.UnfoldedEntries


