-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechSt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:07:22.619946+00:00
-- url     : https://prove2.me/theorems/7c0edf47-cc1f-5ca0-b779-155ed29a9256
-- title:
--   Very Ample Cech St
-- statement:
--   Definitions and structural lemmas for Very Ample Cech St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/VeryAmpleCechSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSnapper
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
universe u v w
def VeryAmpleCech.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E), (∀ I, (F.sub I).FG) → ∀ (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h →
    ∃ F' : SubFamily S h E, (∀ J, (F'.sub J).FG) ∧ ∀ a i : ℕ,
      Nonempty ((F.twist (H.pow a)).H i ≃ₗ[S] (F'.twist (twistSys S h (a : ℤ))).H i)
end
end GroundTheory.Heights₂.Heights.Kleiman


