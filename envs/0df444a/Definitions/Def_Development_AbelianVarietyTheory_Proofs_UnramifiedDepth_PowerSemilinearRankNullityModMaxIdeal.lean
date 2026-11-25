-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSemilinearRankNullityModMaxIdeal
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSemilinearRankNullityModMaxIdeal
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:33.961858+00:00
-- url     : https://prove2.me/theorems/15f1bb5f-ed6d-4550-b8ac-a0d97a6c8e8c
-- title:
--   Power Semilinear Rank Nullity Mod Max Ideal
-- statement:
--   Definitions and structural lemmas for Power Semilinear Rank Nullity Mod Max Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowerSemilinearRankNullityModMaxIdeal.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
namespace GlobalTheory.SemilinearNullity
variable {C : Type} [Field C] {V : VF C}
def IndepOn (V : VF C) {m : ℕ} {σ : Type} (Y : Fin m → σ → C) (T : Finset (Fin m)) : Prop :=
  ∀ c : Fin m → C, (∀ δ, V.Ge 0 (c δ)) → (∀ δ, δ ∉ T → c δ = 0) →
    (∀ s, V.MM (∑ δ, c δ * Y δ s)) → ∀ δ, V.MM (c δ)
end GlobalTheory.SemilinearNullity


