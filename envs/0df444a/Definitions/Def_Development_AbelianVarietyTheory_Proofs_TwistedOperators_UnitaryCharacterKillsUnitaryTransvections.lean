-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryCharacterKillsUnitaryTransvections
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryCharacterKillsUnitaryTransvections
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:55.151106+00:00
-- url     : https://prove2.me/theorems/d8a09c11-c5d4-4256-a956-848f0f4c9758
-- title:
--   Unitary Character Kills Unitary Transvections
-- statement:
--   Definitions and structural lemmas for Unitary Character Kills Unitary Transvections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryCharacterKillsUnitaryTransvections.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
namespace GlobalTheory.UTrans.TvKill
open GlobalTheory.UTrans GlobalTheory.UTrans.Calc
variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
def rk (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : Matrix (Fin n) (Fin n) E :=
  Matrix.of fun a b => x a * ∑ e, G b e * σ (y e)
end GlobalTheory.UTrans.TvKill


