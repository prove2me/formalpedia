-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:04.117575+00:00
-- url     : https://prove2.me/theorems/583f2b3a-d80d-4d0a-b969-7148a6b79e9c
-- title:
--   Ind Of Not
-- statement:
--   Definitions and structural lemmas for Ind Of Not, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IndOfNot.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace GlobalTheory.CompanionTheory.DSNormLt
open CompanionTheory.D.DSIC
variable {n : ℕ}
def sig (a b : Fin n) : ℝ := if a < b then 1 else if b < a then -1 else 0
open Classical in

def ind {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : ℝ :=
  if ∃ h : ε a = true ∧ ε b = false, (⟨(a, b), h⟩ : NC ε) ∈ A then 1 else 0
def tt {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : ℝ :=
  sig a b + 2 * ((ind (A1 ε) a b - ind (A1 ε) b a) - (ind A a b - ind A b a))
end GlobalTheory.CompanionTheory.DSNormLt


