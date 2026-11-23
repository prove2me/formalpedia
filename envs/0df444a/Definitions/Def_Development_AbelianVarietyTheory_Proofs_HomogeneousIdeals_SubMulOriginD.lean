-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:42.594431+00:00
-- url     : https://prove2.me/theorems/cfb4aabd-3344-447a-a48c-a43375a19347
-- title:
--   Sub Mul Origin D
-- statement:
--   Definitions and structural lemmas for Sub Mul Origin D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SubMulOriginD.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Projective
namespace GlobalTheory.AddLaw
variable {R : Type*} [CommRing R]
def originN (W : Projective R) (z₁ w₁ z₂ : R) : R :=
  z₁ ^ 2 + z₁ * z₂ + z₂ ^ 2 + W.a₁ * w₁ + W.a₂ * w₁ * (z₁ + z₂) + W.a₄ * w₁ ^ 2
def originD (W : Projective R) (w₁ z₂ w₂ : R) : R :=
  1 - W.a₁ * z₂ - W.a₂ * z₂ ^ 2 - W.a₃ * (w₁ + w₂) - W.a₄ * z₂ * (w₁ + w₂)
    - W.a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)
def lineCubicCoeff (W : Projective R) (n d : R) : R :=
  d ^ 3 + W.a₂ * n * d ^ 2 + W.a₄ * n ^ 2 * d + W.a₆ * n ^ 3
def lineQuadCoeff (W : Projective R) (n v d : R) : R :=
  W.a₁ * n * d ^ 2 + W.a₂ * v * d ^ 2 + W.a₃ * n ^ 2 * d + 2 * W.a₄ * n * v * d
    + 3 * W.a₆ * n ^ 2 * v
variable {W : Projective R}
end GlobalTheory.AddLaw


