-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropHilbWSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropHilbWSt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:14:32.538091+00:00
-- url     : https://prove2.me/theorems/14b98431-b8fe-42db-9453-69e0e9069277
-- title:
--   Section Count Drop Hilb WSt
-- statement:
--   Definitions and structural lemmas for Section Count Drop Hilb WSt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SectionCountDropHilbWSt.lean

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
def SectionCount.Drop.HilbW.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Nb : LineBundle k x) (pp : Ideal (Poly k N)) (e : ℕ),
    IsVeryAmple Nb.toSubSystem → IsSubvar x pp e →
    ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      |(Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem m 0)
          ((twistMul Nb.toSubSystem m 0).twist (idealSys x pp)) 0) : ℝ) -
        (interNum pp (fun _ : Fin e => Nb.toSubSystem) : ℝ) * (m : ℝ) ^ e / (e.factorial : ℝ)| ≤
        C * (m : ℝ) ^ e / m
end
end GroundTheory.Heights₂.Heights.Kleiman


