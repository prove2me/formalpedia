-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeries__Zuckerman_6aed16b9d2c0b045
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeries__Zuckerman_6aed16b9d2c0b045
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T17:01:33.342867+00:00
-- url     : https://prove2.me/theorems/0d1697cf-d318-4384-bdd0-7003be22f920
-- title:
--   Zuckerman
-- statement:
--   Definitions and structural lemmas for Zuckerman, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/DiscreteSeries₂/Zuckerman.lean

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
def Zuckerman : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu →
    (∀ a c, a < c → 2 ≤ mu a - mu c) →
    (∀ (l : ℕ) (RI : Sub (2 * r + k + 1) l → Rep k r), (∀ I, (RI I).IsDS ε (addSet mu I.1)) →
      ∃ io pr, TensRaw (cmp l) R RI io pr) ∧
    (∀ RI : Fin (2 * r + k + 1) → Rep k r, (∀ s, (RI s).IsDS ε (mu - Pi.single s 1)) →
      ∃ io pr, TensRaw dualM R RI io pr)
end BranchingSupport


