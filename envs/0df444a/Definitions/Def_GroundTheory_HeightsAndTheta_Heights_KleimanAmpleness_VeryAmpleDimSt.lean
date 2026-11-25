-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:31.986204+00:00
-- url     : https://prove2.me/theorems/48cd5801-9ae6-4afe-944e-5aed59cde4aa
-- title:
--   Very Ample Dim St
-- statement:
--   Definitions and structural lemmas for Very Ample Dim St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/VeryAmpleDimSt.lean

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
def VeryAmpleDim.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ)
    (Nb : LineBundle k x) (r : ℕ) (h : Fin (r + 1) → Ω), IsSubvar x (primeOf (S := k) x) e →
    IsVeryAmpleBy Nb.toSubSystem h → IsSubvar h (primeOf (S := k) h) e
end
end GroundTheory.Heights₂.Heights.Kleiman


