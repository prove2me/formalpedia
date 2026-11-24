-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:40.190903+00:00
-- url     : https://prove2.me/theorems/aeec7f29-de34-449e-8fa9-d75876d53743
-- title:
--   Ample Ring Finite St
-- statement:
--   Definitions and structural lemmas for Ample Ring Finite St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AmpleRingFiniteSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
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
def AmpleRingFinite.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (H : LineBundle S x) (D : AmpleData S x H) (j : Fin (D.r + 1)), D.h j ≠ 0 →
      ∃ (r : ℕ) (b : Fin r → Ω), (∀ l, b l ∈ ampleRing H.toSubSystem D.m (D.h j)) ∧
        ampleRing H.toSubSystem D.m (D.h j) ⊆ Submodule.span (ampleBase (S := S) D.h j) (Set.range b)
end GroundTheory.Heights₂.Heights.Kleiman


