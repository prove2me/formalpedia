-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
-- name    : Formalism_PieriBlockIdeals_ExZTranslate
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:21:55.06331+00:00
-- url     : https://prove2.me/theorems/14a0f693-fbd3-4a6a-b303-695922933321
-- title:
--   Ex ZTranslate
-- statement:
--   Definitions and structural lemmas for Ex ZTranslate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/ExZTranslate.lean

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CohomologicalDescent.LA
def InclZTwist : Prop :=
  ∀ (r : ℕ) (ν : Fin r → ℕ) (c l e : ℕ), Antitone ν → l.Prime →
    (InclZ r r le_rfl (fun a => ν a + c) l e ↔ InclZ r r le_rfl ν l e)
def ExZTwist : Prop :=
  ∀ (r : ℕ) (ν : Fin r → ℕ) (c l : ℕ), Antitone ν → l.Prime →
    exZ r r le_rfl (fun a => ν a + c) l = exZ r r le_rfl ν l
def ExZTranslate : Prop :=
  ∀ (r : ℕ) (U : Fin r → ℤ) (c l : ℕ), StrictAnti U → (∀ a, 0 ≤ U a) → l.Prime →
    exZ r r le_rfl (nuOf (fun a => U a + (c : ℤ))) l = exZ r r le_rfl (nuOf U) l
end Formalism.CohomologicalDescent.LA


