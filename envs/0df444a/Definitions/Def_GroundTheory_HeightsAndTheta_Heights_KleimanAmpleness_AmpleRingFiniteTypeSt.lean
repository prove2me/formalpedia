-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteTypeSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteTypeSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:00.882264+00:00
-- url     : https://prove2.me/theorems/044f0d63-3dc3-4f8e-932f-b1eb25620957
-- title:
--   Ample Ring Finite Type St
-- statement:
--   Definitions and structural lemmas for Ample Ring Finite Type St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/AmpleRingFiniteTypeSt.lean

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
def AmpleRingFiniteType.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (H : LineBundle S x) (D : AmpleData S x H) (j : Fin (D.r + 1)), D.h j ≠ 0 →
      ∃ (r : ℕ) (g : Fin r → Ω), (∀ l, g l ∈ ampleRing H.toSubSystem D.m (D.h j)) ∧
        ampleRing H.toSubSystem D.m (D.h j) ⊆
          (Algebra.adjoin (ampleBase (S := S) D.h j) (Set.range g) : Set Ω)
end GroundTheory.Heights₂.Heights.Kleiman


