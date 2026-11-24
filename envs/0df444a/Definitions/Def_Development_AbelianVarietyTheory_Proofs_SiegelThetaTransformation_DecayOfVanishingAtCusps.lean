-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DecayOfVanishingAtCusps
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DecayOfVanishingAtCusps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:30.782883+00:00
-- url     : https://prove2.me/theorems/e1ce84b2-682b-465e-90a7-82b523c4d58a
-- title:
--   Decay Of Vanishing At Cusps
-- statement:
--   Definitions and structural lemmas for Decay Of Vanishing At Cusps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DecayOfVanishingAtCusps.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsFourierExpansionHolomorphicTubeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDualStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TracePairingGeDetImPowHermitianHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableExpNegTraceTotallyPositiveHermitianStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory.SW.Decay
open MeasureTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {N : ℕ}
def pr (T : Matrix (Fin N) (Fin N) E) (Z : CM Ψ N N) : ℂ := ∑ τ : Ψ, (T.map τ.1 * Z τ).trace
def cube (m : ℕ) : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ : Fin m => Set.Ico (0 : ℝ) 1)
def IsCoef {m : ℕ} (X : (Fin m → ℝ) → CM Ψ N N) (f : CM Ψ N N → ℂ) (T : Matrix (Fin N) (Fin N) E)
    (a : ℂ) : Prop :=
  ∀ Y : CM Ψ N N, (∀ τ, (Y τ).PosDef) → a = ∫ x in cube m,
    f (fun τ => X x τ + I • Y τ) * cexp (-(2 * π * I * pr T (fun τ => X x τ + I • Y τ)))
section coef
variable {m : ℕ} {X : (Fin m → ℝ) → CM Ψ N N} {f : CM Ψ N N → ℂ} {T : Matrix (Fin N) (Fin N) E}
  {a : ℂ} {η B : ℝ}
end coef
end
end GlobalTheory.SW.Decay


