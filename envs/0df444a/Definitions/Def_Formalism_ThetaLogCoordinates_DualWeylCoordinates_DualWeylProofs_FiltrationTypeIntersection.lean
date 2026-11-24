-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationTypeIntersection
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationTypeIntersection
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T12:17:10.957251+00:00
-- url     : https://prove2.me/theorems/d67b9502-3188-4d7a-8c5b-9135b4e62f16
-- title:
--   Filtration Type Intersection
-- statement:
--   Definitions and structural lemmas for Filtration Type Intersection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
def qd_low (mu : Fin n → ℤ) : Set (Fin n → ℤ) := {la | Dominant la ∧ DomLE la mu}
variable [NeZero n]
def qd_phQ {M : GLMod n} (CF : ColFam M) (j : CF.J) : (TIdx (CF.mu j) → ℚ) →ₗ[ℚ] (M.ι → ℚ) :=
  Matrix.mulVecLin ((CF.ph j).map (Int.castRingHom ℚ))
end Formalism.InvariantFactorPaths.ColumnFamilies


