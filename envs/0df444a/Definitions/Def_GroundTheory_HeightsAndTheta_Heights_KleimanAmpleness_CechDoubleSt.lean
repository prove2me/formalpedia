-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDoubleSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDoubleSt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:30:49.441487+00:00
-- url     : https://prove2.me/theorems/47b90565-aa7c-4e56-942f-d7008de430cc
-- title:
--   Cech Double St
-- statement:
--   Definitions and structural lemmas for Cech Double St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CechDoubleSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
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
def CechDouble.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] (N r : ℕ) (x : Fin (N + 1) → Ω) (h : Fin (r + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module S E]
    (A : Chart x → Submodule S E) (B : Chart h → Submodule S E) (M : Chart x → Chart h → Submodule S E),
    (∀ (I I' : Chart x) (J : Chart h), I.1 ⊆ I'.1 → M I J ≤ M I' J) →
    (∀ (I : Chart x) (J J' : Chart h), J.1 ⊆ J'.1 → M I J ≤ M I J') →
    (∀ I, Cech.AugExact S (M I) (A I)) → (∀ J, Cech.AugExact S (fun I => M I J) (B J)) →
    ∀ n : ℕ, Nonempty (Cech.Hdeg (fun _ : Chart x => E) A (Cech.idRes S E (support x)) n ≃ₗ[S]
      Cech.Hdeg (fun _ : Chart h => E) B (Cech.idRes S E (support h)) n)
end
end GroundTheory.Heights₂.Heights.Kleiman


