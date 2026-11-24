-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeries__DSExist_a6dd32cbfb035a07
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeries__DSExist_a6dd32cbfb035a07
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T17:11:05.111141+00:00
-- url     : https://prove2.me/theorems/ef9f7d71-d62b-4a1c-b21b-f9d26db78b52
-- title:
--   DSExist
-- statement:
--   Definitions and structural lemmas for DSExist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/DiscreteSeries₂/DSExist.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPrAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
noncomputable section
namespace BranchingSupport
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
def DSExist : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ), Formalism.QuantumDeterminants.IsHCParam mu →
    (∃ P, PI.UpqRep.IsCayleyU k r ε P) → ∃ R : Rep k r, R.IsDS ε mu
end BranchingSupport


