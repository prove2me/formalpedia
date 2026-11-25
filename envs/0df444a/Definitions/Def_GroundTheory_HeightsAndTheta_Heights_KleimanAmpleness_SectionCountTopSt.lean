-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountTopSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountTopSt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:14:02.19843+00:00
-- url     : https://prove2.me/theorems/bce616a3-a027-5add-b9f0-c57fb5e01051
-- title:
--   Section Count Top St
-- statement:
--   Definitions and structural lemmas for Section Count Top St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SectionCountTopSt.lean

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
open Filter
noncomputable section
universe u w
def SectionCount.Top.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x), IsSubvar x (primeOf (S := k) x) (d + 1) → IsVeryAmple Nb.toSubSystem →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) : ℝ) *
          (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤
        (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ)
end
end GroundTheory.Heights₂.Heights.Kleiman


