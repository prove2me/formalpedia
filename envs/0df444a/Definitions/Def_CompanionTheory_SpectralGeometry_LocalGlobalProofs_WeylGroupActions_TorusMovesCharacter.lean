-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_WeylGroupActions_TorusMovesCharacter
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_WeylGroupActions_TorusMovesCharacter
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:35:16.047224+00:00
-- url     : https://prove2.me/theorems/16b44c6e-02af-5980-9d65-aacaabbeec27
-- title:
--   Torus Moves Character
-- statement:
--   Definitions and structural lemmas for Torus Moves Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/TorusMovesCharacter.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpkAlt
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
noncomputable section
namespace GlobalTheory.CompanionTheory.Bes
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
def torusTail {r : ℕ} (c : Fin r → ℂ) (n : ℕ) : ℂ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin r => n ≤ j.val), c j
def torusDiag (k : ℕ) {r : ℕ} (c : Fin r → ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val ≤ r + k then torusTail c i.val else (star (torusTail c (2 * r + k - i.val)))⁻¹
end GlobalTheory.CompanionTheory.Bes


