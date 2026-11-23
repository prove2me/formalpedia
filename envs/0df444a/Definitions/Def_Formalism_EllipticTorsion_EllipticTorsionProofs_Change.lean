-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Change
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_Change
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:59.7261+00:00
-- url     : https://prove2.me/theorems/523d75ab-4280-4efd-ab86-85cde70ea8c5
-- title:
--   Change
-- statement:
--   Definitions and structural lemmas for Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Change.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_ChangeIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ELL Formalism.G
namespace Formalism.ELL.RootExponentBounds
universe u
section
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
lemma memB {x : K} : x ∈ unitBall K ↔ ‖x‖ ≤ 1 := Iff.rfl
lemma natB (n : ℕ) : (n : K) ∈ unitBall K := memB.2 (IsUltrametricDist.norm_natCast_le_one K n)
lemma ofNatB (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : K) ∈ unitBall K := by
  have := natB (K := K) n
  exact this
end
end Formalism.ELL.RootExponentBounds
namespace Formalism.ELL
universe v
end Formalism.ELL


