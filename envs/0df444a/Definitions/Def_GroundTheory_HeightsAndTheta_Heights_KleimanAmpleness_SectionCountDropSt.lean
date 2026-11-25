-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropSt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:15:27.639726+00:00
-- url     : https://prove2.me/theorems/84d8fef7-310b-4e53-b82c-b6d4bbd5fb9e
-- title:
--   Section Count Drop St
-- statement:
--   Definitions and structural lemmas for Section Count Drop St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SectionCountDropSt.lean

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
def SectionCount.Drop.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) →
    IsVeryAmple Nb.toSubSystem → 1 ≤ b →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ i < n,
      (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℝ) -
          (Module.finrank k (twistMul Nb.toSubSystem n (-(((i + 1 : ℕ) : ℤ) * b))).secs : ℝ) ≤
        (interNum (primeOf (S := k) x)
            (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
              (fun _ : Fin d => Nb.toSubSystem)) : ℝ) * (n : ℝ) ^ d / (d.factorial : ℝ) +
          C * (n : ℝ) ^ d / n
end
end GroundTheory.Heights₂.Heights.Kleiman


