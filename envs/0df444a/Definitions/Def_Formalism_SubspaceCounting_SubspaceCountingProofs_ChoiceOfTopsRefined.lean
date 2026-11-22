-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
-- name    : Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:47.268854+00:00
-- url     : https://prove2.me/theorems/838f5953-e505-4db6-a0fb-3814ea9e111f
-- title:
--   Choice Of Tops Refined
-- statement:
--   Definitions and structural lemmas for Choice Of Tops Refined, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
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
namespace Formalism.G0
namespace TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
def Dep (S : Finset ℕ) (A : Finset ℕ → Prop) : Prop := ∀ t, A t ↔ A (t ∩ S)
end TopsChoiceProbabilityLemmas
namespace TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
def tile (r u s : ℕ) : Finset ℕ := Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u))
def EC (r u s c : ℕ) (t : Finset ℕ) : Prop :=
  (Odd c → t ∩ cell r u s c = ∅) ∧ (Even c → ∃ x, t ∩ cell r u s c = {x} ∧ Even x)
end TopsChoiceProbabilityLemmas
namespace TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
end TopsChoiceProbabilityLemmas
end Formalism.G0


