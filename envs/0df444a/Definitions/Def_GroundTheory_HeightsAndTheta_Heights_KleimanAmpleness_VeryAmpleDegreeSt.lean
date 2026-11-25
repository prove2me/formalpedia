-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDegreeSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDegreeSt
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:48.100631+00:00
-- url     : https://prove2.me/theorems/9b10fbb6-574d-5854-9bad-ae7eba57bf71
-- title:
--   Very Ample Degree St
-- statement:
--   Definitions and structural lemmas for Very Ample Degree St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/VeryAmpleDegreeSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u w
def VeryAmpleDegree.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ)
    (Nb : LineBundle k x) (r : ℕ) (h : Fin (r + 1) → Ω), IsSubvar x (primeOf (S := k) x) e →
    IsVeryAmpleBy Nb.toSubSystem h →
    interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) =
      interNum (primeOf (S := k) h) (fun _ : Fin e => twistSys k h 1)
end
end GroundTheory.Heights₂.Heights.Kleiman


