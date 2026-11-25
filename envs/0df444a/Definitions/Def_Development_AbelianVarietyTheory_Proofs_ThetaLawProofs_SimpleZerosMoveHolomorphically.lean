-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SimpleZerosMoveHolomorphically
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SimpleZerosMoveHolomorphically
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T17:19:20.114274+00:00
-- url     : https://prove2.me/theorems/2b2b67ab-1c0b-588f-bde7-0f35a2de5ac9
-- title:
--   Simple Zeros Move Holomorphically
-- statement:
--   Definitions and structural lemmas for Simple Zeros Move Holomorphically, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SimpleZerosMoveHolomorphically.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open Filter Topology
namespace GlobalTheory.HolZeros
noncomputable def coords {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) :
    (Fin g → ℝ) × (Fin g → ℝ) :=
  ((fun i => (w i).re) - (τ.map Complex.re).mulVec
      ((τ.map Complex.im)⁻¹.mulVec fun i => (w i).im),
    (τ.map Complex.im)⁻¹.mulVec fun i => (w i).im)
noncomputable def comb {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : (Fin g → ℝ) × (Fin g → ℝ)) :
    Fin g → ℂ :=
  (fun i => (x.1 i : ℂ)) + τ.mulVec (fun i => (x.2 i : ℂ))
end GlobalTheory.HolZeros


