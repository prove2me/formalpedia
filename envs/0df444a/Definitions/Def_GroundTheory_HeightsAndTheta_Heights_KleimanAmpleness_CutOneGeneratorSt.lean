-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutOneGeneratorSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutOneGeneratorSt
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:36:35.342487+00:00
-- url     : https://prove2.me/theorems/4c53372e-edb8-51e2-926f-12ae86439b98
-- title:
--   Cut One Generator St
-- statement:
--   Definitions and structural lemmas for Cut One Generator St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CutOneGeneratorSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutNonemptySt
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
open MvPolynomial
noncomputable section
universe u w
def CutOneGenerator.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar x pp (n + 1) →
    IsVeryAmple L.toSubSystem → s ∈ L.secs →
    ¬ ∀ (j : Fin (N + 1)) (hj : x j ≠ 0), L.sub (singleChart hj) ≤
      (L.twist (idealSys x pp)).sub (singleChart hj) ⊔
        Submodule.span (chartRing k x (singleChart hj)) {s}
end
end GroundTheory.Heights₂.Heights.Kleiman


