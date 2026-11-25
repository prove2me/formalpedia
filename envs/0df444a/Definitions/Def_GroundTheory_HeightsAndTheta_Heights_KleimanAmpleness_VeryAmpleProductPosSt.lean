-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleProductPosSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleProductPosSt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T05:57:38.981362+00:00
-- url     : https://prove2.me/theorems/c113834c-88d5-49ae-b519-d1310966d65a
-- title:
--   Very Ample Product Pos St
-- statement:
--   Definitions and structural lemmas for Very Ample Product Pos St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/VeryAmpleProductPosSt.lean

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
def VeryAmpleProductPos.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (Ls : Fin e → LineBundle k x), IsSubvar x pp e →
    (∀ i, IsVeryAmple (Ls i).toSubSystem) → 0 < interNum pp (fun i => (Ls i).toSubSystem)
end
end GroundTheory.Heights₂.Heights.Kleiman


