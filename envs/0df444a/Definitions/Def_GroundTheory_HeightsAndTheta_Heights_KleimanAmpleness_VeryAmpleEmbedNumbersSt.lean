-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedNumbersSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedNumbersSt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:11:07.641424+00:00
-- url     : https://prove2.me/theorems/ec04f5bb-631d-56fd-adfe-715873b6592a
-- title:
--   Very Ample Embed Numbers St
-- statement:
--   Definitions and structural lemmas for Very Ample Embed Numbers St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/VeryAmpleEmbedNumbersSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
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
open MvPolynomial Filter
noncomputable section
universe u v w
def VeryAmpleEmbed.Numbers.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω)
    (Q : LineBundle k y) (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy Q.toSubSystem h →
    ∀ n : ℕ, IsSubvar y (primeOf (S := k) y) n →
      IsSubvar h (primeOf (S := k) h) n ∧
        interNum (primeOf (S := k) y) (fun _ : Fin n => Q.toSubSystem) =
          interNum (primeOf (S := k) h) (fun _ : Fin n => twistSys k h 1)
end
end GroundTheory.Heights₂.Heights.Kleiman


