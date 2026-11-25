-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:28:27.557793+00:00
-- url     : https://prove2.me/theorems/22508d17-8bc9-5775-b897-e017ca2096f5
-- title:
--   Very Ample ZColumns St
-- statement:
--   Definitions and structural lemmas for Very Ample ZColumns St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/VeryAmpleZColumnsSt.lean

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
def VeryAmpleZColumns.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (G : SubFamily S x E) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h → ∀ I : Chart x,
      (∀ J J' : Chart h, J.1 ⊆ J'.1 →
        secsOnZChart G.toSubSystem H.toSubSystem h I J ≤ secsOnZChart G.toSubSystem H.toSubSystem h I J') ∧
      Cech.AugExact S (secsOnZChart G.toSubSystem H.toSubSystem h I) ((G.sub I).restrictScalars S)
end
end GroundTheory.Heights₂.Heights.Kleiman


