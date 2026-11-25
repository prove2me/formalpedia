-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LeafHolds
-- name    : Formalism_LocalToGlobal_CharacterGerms_LeafHolds
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:25:05.022387+00:00
-- url     : https://prove2.me/theorems/1dcb3609-c6be-484e-9b2f-c1ccd5930cea
-- title:
--   Leaf Holds
-- statement:
--   Definitions and structural lemmas for Leaf Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LeafHolds.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCut
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
section EqOn
variable {K : Type} [Field K] {σ : Type}
def EqOn (A : Set σ) (F G : MvPowerSeries σ K) : Prop :=
  ∀ μ : σ →₀ ℕ, (↑μ.support : Set σ) ⊆ A → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ G
end EqOn
end Formalism.L2.FormalSeriesBounds


