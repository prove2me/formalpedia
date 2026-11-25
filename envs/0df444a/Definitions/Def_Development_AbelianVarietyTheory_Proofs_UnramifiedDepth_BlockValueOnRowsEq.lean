-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:48.42154+00:00
-- url     : https://prove2.me/theorems/8a47b44a-a115-411b-bf0a-f16b7d7611c5
-- title:
--   Block Value On Rows Eq
-- statement:
--   Definitions and structural lemmas for Block Value On Rows Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BlockValueOnRowsEq.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open scoped BigOperators
namespace GlobalTheory.BlockValue
variable {C : Type} [Field C] {σ κ : Type}
def OnlyIn (S : σ → Prop) (f : MvPowerSeries σ C) : Prop :=
  ∀ m : σ →₀ ℕ, MvPowerSeries.coeff m f ≠ 0 → ∀ x ∈ m.support, S x
def Lead (π : σ → κ) (d : σ →₀ ℕ) (f : MvPowerSeries σ C) : Prop :=
  (∀ m : σ →₀ ℕ, MvPowerSeries.coeff m f ≠ 0 →
    d.mapDomain π ≤ m.mapDomain π ∧ (m.mapDomain π ≤ d.mapDomain π → m = d)) ∧
  MvPowerSeries.coeff d f = 1
def sideRow (n : ℕ) : PVar n → Fin n ⊕ Fin n := Sum.map Prod.fst Prod.fst
end GlobalTheory.BlockValue


