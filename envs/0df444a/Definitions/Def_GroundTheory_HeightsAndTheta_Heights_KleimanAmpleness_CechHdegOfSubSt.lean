-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechHdegOfSubSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechHdegOfSubSt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:29:39.617682+00:00
-- url     : https://prove2.me/theorems/c62800bb-5095-45e6-882b-06c8432159dc
-- title:
--   Cech Hdeg Of Sub St
-- statement:
--   Definitions and structural lemmas for Cech Hdeg Of Sub St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CechHdegOfSubSt.lean

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
def CechHdegOfSub.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (T : SubSystem S x E) (n : ℕ),
    Nonempty (T.H n ≃ₗ[S] Cech.Hdeg (fun _ : Chart x => E) (fun I => (T.sub I).restrictScalars S)
      (Cech.idRes S E (support x)) n)
end
end GroundTheory.Heights₂.Heights.Kleiman


