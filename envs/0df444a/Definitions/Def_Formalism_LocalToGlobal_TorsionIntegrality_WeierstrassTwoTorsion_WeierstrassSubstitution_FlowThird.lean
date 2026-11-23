-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowThird
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowThird
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:24.350783+00:00
-- url     : https://prove2.me/theorems/7395c267-2dfd-45de-b4c7-2bc2fd5d2d7a
-- title:
--   Flow Third
-- statement:
--   Definitions and structural lemmas for Flow Third, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowThird.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace Formalism.L2.Th1.A
namespace CubicFlow
open QuadraticFlow
variable {A : Type u} [CommRing A]
def gE (W : WeierstrassCurve A) (z v : A) : A :=
  z ^ 3 + W.a₁ * z * v + W.a₂ * z ^ 2 * v + W.a₃ * v ^ 2 + W.a₄ * z * v ^ 2 + W.a₆ * v ^ 3 - v
def k3 (W : WeierstrassCurve A) (l : A) : A := 1 + W.a₂ * l + W.a₄ * l ^ 2 + W.a₆ * l ^ 3
def k2 (W : WeierstrassCurve A) (l n : A) : A :=
  W.a₁ * l + W.a₂ * n + W.a₃ * l ^ 2 + 2 * W.a₄ * l * n + 3 * W.a₆ * l ^ 2 * n
def k1 (W : WeierstrassCurve A) (l n : A) : A :=
  W.a₁ * n + 2 * W.a₃ * l * n + W.a₄ * n ^ 2 + 3 * W.a₆ * l * n ^ 2 - l
def k0 (W : WeierstrassCurve A) (n : A) : A := W.a₃ * n ^ 2 + W.a₆ * n ^ 3 - n
end CubicFlow
open QuadraticFlow CubicFlow
end Formalism.L2.Th1.A


