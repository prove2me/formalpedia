-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:32.560162+00:00
-- url     : https://prove2.me/theorems/ffcf6c59-d0f1-4af5-877c-29182cc0bc56
-- title:
--   Diag ZEq Neg Add Y
-- statement:
--   Definitions and structural lemmas for Diag ZEq Neg Add Y, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DiagZEqNegAddY.lean

import Mathlib
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
variable {R S : Type*} [CommRing R] [CommRing S]
def diagX (W : Projective R) (P Q : Fin 3 → R) : R :=
  -W.a₁ * W.a₂ * P 0 ^ 2 * Q 0 ^ 2 + W.a₁ ^ 2 * P 0 * P 1 * Q 0 ^ 2
    - W.a₂ * P 0 * P 1 * Q 0 ^ 2 + W.a₁ * P 1 ^ 2 * Q 0 ^ 2 - W.a₂ * W.a₃ * P 0 * P 2 * Q 0 ^ 2
    - W.a₁ * W.a₄ * P 0 * P 2 * Q 0 ^ 2 + W.a₁ * W.a₃ * P 1 * P 2 * Q 0 ^ 2
    - W.a₄ * P 1 * P 2 * Q 0 ^ 2 - W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 ^ 2 - W.a₂ * P 0 ^ 2 * Q 0 * Q 1
    + 2 * W.a₁ * P 0 * P 1 * Q 0 * Q 1 + P 1 ^ 2 * Q 0 * Q 1 - 2 * W.a₄ * P 0 * P 2 * Q 0 * Q 1
    + 2 * W.a₃ * P 1 * P 2 * Q 0 * Q 1 - 3 * W.a₆ * P 2 ^ 2 * Q 0 * Q 1 + P 0 * P 1 * Q 1 ^ 2
    - W.a₁ ^ 2 * W.a₃ * P 0 ^ 2 * Q 0 * Q 2 - 2 * W.a₁ * W.a₄ * P 0 ^ 2 * Q 0 * Q 2
    - 2 * W.a₄ * P 0 * P 1 * Q 0 * Q 2 + W.a₃ * P 1 ^ 2 * Q 0 * Q 2
    - 2 * W.a₁ * W.a₃ ^ 2 * P 0 * P 2 * Q 0 * Q 2 - 2 * W.a₃ * W.a₄ * P 0 * P 2 * Q 0 * Q 2
    - 6 * W.a₁ * W.a₆ * P 0 * P 2 * Q 0 * Q 2 - 6 * W.a₆ * P 1 * P 2 * Q 0 * Q 2
    - W.a₃ ^ 3 * P 2 ^ 2 * Q 0 * Q 2 - 6 * W.a₃ * W.a₆ * P 2 ^ 2 * Q 0 * Q 2
    - W.a₁ * W.a₃ * P 0 ^ 2 * Q 1 * Q 2 - W.a₄ * P 0 ^ 2 * Q 1 * Q 2
    - 2 * W.a₃ ^ 2 * P 0 * P 2 * Q 1 * Q 2 - 6 * W.a₆ * P 0 * P 2 * Q 1 * Q 2
    - W.a₂ * W.a₃ ^ 2 * P 2 ^ 2 * Q 1 * Q 2 + W.a₁ * W.a₃ * W.a₄ * P 2 ^ 2 * Q 1 * Q 2
    + W.a₄ ^ 2 * P 2 ^ 2 * Q 1 * Q 2 - W.a₁ ^ 2 * W.a₆ * P 2 ^ 2 * Q 1 * Q 2
    - 4 * W.a₂ * W.a₆ * P 2 ^ 2 * Q 1 * Q 2 - W.a₁ * W.a₃ ^ 2 * P 0 ^ 2 * Q 2 ^ 2
    - 3 * W.a₁ * W.a₆ * P 0 ^ 2 * Q 2 ^ 2 - W.a₃ ^ 2 * P 0 * P 1 * Q 2 ^ 2
    - 3 * W.a₆ * P 0 * P 1 * Q 2 ^ 2 - W.a₁ * W.a₂ * W.a₃ ^ 2 * P 0 * P 2 * Q 2 ^ 2
    - W.a₃ ^ 3 * P 0 * P 2 * Q 2 ^ 2 + W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * P 2 * Q 2 ^ 2
    + W.a₁ * W.a₄ ^ 2 * P 0 * P 2 * Q 2 ^ 2 - W.a₁ ^ 3 * W.a₆ * P 0 * P 2 * Q 2 ^ 2
    - 4 * W.a₁ * W.a₂ * W.a₆ * P 0 * P 2 * Q 2 ^ 2 - 3 * W.a₃ * W.a₆ * P 0 * P 2 * Q 2 ^ 2
    - W.a₂ * W.a₃ ^ 2 * P 1 * P 2 * Q 2 ^ 2 + W.a₁ * W.a₃ * W.a₄ * P 1 * P 2 * Q 2 ^ 2
    + W.a₄ ^ 2 * P 1 * P 2 * Q 2 ^ 2 - W.a₁ ^ 2 * W.a₆ * P 1 * P 2 * Q 2 ^ 2
    - 4 * W.a₂ * W.a₆ * P 1 * P 2 * Q 2 ^ 2 - W.a₂ * W.a₃ ^ 3 * P 2 ^ 2 * Q 2 ^ 2
    + W.a₁ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 2 * Q 2 ^ 2 + W.a₃ * W.a₄ ^ 2 * P 2 ^ 2 * Q 2 ^ 2
    - W.a₁ ^ 2 * W.a₃ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2 - 4 * W.a₂ * W.a₃ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2
def negDiagY (W : Projective R) (P Q : Fin 3 → R) : R :=
  W.a₁ ^ 2 * W.a₂ * P 0 ^ 2 * Q 0 ^ 2 + W.a₂ ^ 2 * P 0 ^ 2 * Q 0 ^ 2
    - 3 * W.a₁ * W.a₃ * P 0 ^ 2 * Q 0 ^ 2 - 3 * W.a₄ * P 0 ^ 2 * Q 0 ^ 2
    - W.a₁ ^ 3 * P 0 * P 1 * Q 0 ^ 2 - W.a₁ ^ 2 * P 1 ^ 2 * Q 0 ^ 2
    - 3 * W.a₃ ^ 2 * P 0 * P 2 * Q 0 ^ 2 + W.a₁ ^ 2 * W.a₄ * P 0 * P 2 * Q 0 ^ 2
    + W.a₂ * W.a₄ * P 0 * P 2 * Q 0 ^ 2 - 9 * W.a₆ * P 0 * P 2 * Q 0 ^ 2
    - W.a₁ ^ 2 * W.a₃ * P 1 * P 2 * Q 0 ^ 2 - W.a₂ * W.a₃ ^ 2 * P 2 ^ 2 * Q 0 ^ 2
    + W.a₁ * W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 ^ 2 + W.a₄ ^ 2 * P 2 ^ 2 * Q 0 ^ 2
    - 3 * W.a₂ * W.a₆ * P 2 ^ 2 * Q 0 ^ 2 + W.a₁ * W.a₂ * P 0 ^ 2 * Q 0 * Q 1
    - 3 * W.a₃ * P 0 ^ 2 * Q 0 * Q 1 - 2 * W.a₁ ^ 2 * P 0 * P 1 * Q 0 * Q 1
    - 2 * W.a₁ * P 1 ^ 2 * Q 0 * Q 1 - 2 * W.a₂ * W.a₃ * P 0 * P 2 * Q 0 * Q 1
    + 2 * W.a₁ * W.a₄ * P 0 * P 2 * Q 0 * Q 1 - 2 * W.a₁ * W.a₃ * P 1 * P 2 * Q 0 * Q 1
    - W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 * Q 1 + 3 * W.a₁ * W.a₆ * P 2 ^ 2 * Q 0 * Q 1
    - W.a₁ * P 0 * P 1 * Q 1 ^ 2 - P 1 ^ 2 * Q 1 ^ 2 - W.a₃ * P 1 * P 2 * Q 1 ^ 2
    - 3 * W.a₃ ^ 2 * P 0 ^ 2 * Q 0 * Q 2 + W.a₁ ^ 2 * W.a₄ * P 0 ^ 2 * Q 0 * Q 2
    + W.a₂ * W.a₄ * P 0 ^ 2 * Q 0 * Q 2 - 9 * W.a₆ * P 0 ^ 2 * Q 0 * Q 2
    - 2 * W.a₁ ^ 2 * W.a₃ * P 0 * P 1 * Q 0 * Q 2 - 2 * W.a₁ * W.a₃ * P 1 ^ 2 * Q 0 * Q 2
    - 4 * W.a₂ * W.a₃ ^ 2 * P 0 * P 2 * Q 0 * Q 2
    + 4 * W.a₁ * W.a₃ * W.a₄ * P 0 * P 2 * Q 0 * Q 2 + 4 * W.a₄ ^ 2 * P 0 * P 2 * Q 0 * Q 2
    - 12 * W.a₂ * W.a₆ * P 0 * P 2 * Q 0 * Q 2 - 2 * W.a₁ * W.a₃ ^ 2 * P 1 * P 2 * Q 0 * Q 2
    - W.a₂ ^ 2 * W.a₃ ^ 2 * P 2 ^ 2 * Q 0 * Q 2
    + W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 * Q 2 + W.a₂ * W.a₄ ^ 2 * P 2 ^ 2 * Q 0 * Q 2
    - W.a₁ ^ 2 * W.a₂ * W.a₆ * P 2 ^ 2 * Q 0 * Q 2 - 4 * W.a₂ ^ 2 * W.a₆ * P 2 ^ 2 * Q 0 * Q 2
    + 3 * W.a₁ * W.a₃ * W.a₆ * P 2 ^ 2 * Q 0 * Q 2 + 3 * W.a₄ * W.a₆ * P 2 ^ 2 * Q 0 * Q 2
    - W.a₂ * W.a₃ * P 0 ^ 2 * Q 1 * Q 2 + W.a₁ * W.a₄ * P 0 ^ 2 * Q 1 * Q 2
    - 2 * W.a₁ * W.a₃ * P 0 * P 1 * Q 1 * Q 2 - 2 * W.a₃ * P 1 ^ 2 * Q 1 * Q 2
    - 2 * W.a₃ * W.a₄ * P 0 * P 2 * Q 1 * Q 2 + 6 * W.a₁ * W.a₆ * P 0 * P 2 * Q 1 * Q 2
    - 2 * W.a₃ ^ 2 * P 1 * P 2 * Q 1 * Q 2 + W.a₁ * W.a₂ * W.a₃ ^ 2 * P 2 ^ 2 * Q 1 * Q 2
    - W.a₃ ^ 3 * P 2 ^ 2 * Q 1 * Q 2 - W.a₁ ^ 2 * W.a₃ * W.a₄ * P 2 ^ 2 * Q 1 * Q 2
    - W.a₁ * W.a₄ ^ 2 * P 2 ^ 2 * Q 1 * Q 2 + W.a₁ ^ 3 * W.a₆ * P 2 ^ 2 * Q 1 * Q 2
    + 4 * W.a₁ * W.a₂ * W.a₆ * P 2 ^ 2 * Q 1 * Q 2 - 3 * W.a₃ * W.a₆ * P 2 ^ 2 * Q 1 * Q 2
    - W.a₂ * W.a₃ ^ 2 * P 0 ^ 2 * Q 2 ^ 2 + W.a₁ * W.a₃ * W.a₄ * P 0 ^ 2 * Q 2 ^ 2
    + W.a₄ ^ 2 * P 0 ^ 2 * Q 2 ^ 2 - 3 * W.a₂ * W.a₆ * P 0 ^ 2 * Q 2 ^ 2
    - W.a₁ * W.a₃ ^ 2 * P 0 * P 1 * Q 2 ^ 2 - W.a₃ ^ 2 * P 1 ^ 2 * Q 2 ^ 2
    - W.a₂ ^ 2 * W.a₃ ^ 2 * P 0 * P 2 * Q 2 ^ 2
    + W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 0 * P 2 * Q 2 ^ 2 + W.a₂ * W.a₄ ^ 2 * P 0 * P 2 * Q 2 ^ 2
    - W.a₁ ^ 2 * W.a₂ * W.a₆ * P 0 * P 2 * Q 2 ^ 2 - 4 * W.a₂ ^ 2 * W.a₆ * P 0 * P 2 * Q 2 ^ 2
    + 3 * W.a₁ * W.a₃ * W.a₆ * P 0 * P 2 * Q 2 ^ 2 + 3 * W.a₄ * W.a₆ * P 0 * P 2 * Q 2 ^ 2
    - W.a₃ ^ 3 * P 1 * P 2 * Q 2 ^ 2 - W.a₂ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 2 * Q 2 ^ 2
    + W.a₁ * W.a₃ * W.a₄ ^ 2 * P 2 ^ 2 * Q 2 ^ 2 + W.a₄ ^ 3 * P 2 ^ 2 * Q 2 ^ 2
    + 3 * W.a₃ ^ 2 * W.a₆ * P 2 ^ 2 * Q 2 ^ 2 - W.a₁ ^ 2 * W.a₄ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2
    - 4 * W.a₂ * W.a₄ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2 + 9 * W.a₆ ^ 2 * P 2 ^ 2 * Q 2 ^ 2
def diagZ (W : Projective R) (P Q : Fin 3 → R) : R :=
  3 * W.a₁ * P 0 ^ 2 * Q 0 ^ 2 + 3 * P 0 * P 1 * Q 0 ^ 2 + W.a₁ * W.a₂ * P 0 * P 2 * Q 0 ^ 2
    + 3 * W.a₃ * P 0 * P 2 * Q 0 ^ 2 + W.a₂ * P 1 * P 2 * Q 0 ^ 2
    + W.a₂ * W.a₃ * P 2 ^ 2 * Q 0 ^ 2 + 3 * P 0 ^ 2 * Q 0 * Q 1
    + 2 * W.a₂ * P 0 * P 2 * Q 0 * Q 1 + W.a₄ * P 2 ^ 2 * Q 0 * Q 1 + P 1 * P 2 * Q 1 ^ 2
    + W.a₁ ^ 3 * P 0 ^ 2 * Q 0 * Q 2 + 2 * W.a₁ * W.a₂ * P 0 ^ 2 * Q 0 * Q 2
    + 2 * W.a₁ ^ 2 * P 0 * P 1 * Q 0 * Q 2 + 2 * W.a₂ * P 0 * P 1 * Q 0 * Q 2
    + W.a₁ * P 1 ^ 2 * Q 0 * Q 2 + 2 * W.a₁ ^ 2 * W.a₃ * P 0 * P 2 * Q 0 * Q 2
    + 2 * W.a₂ * W.a₃ * P 0 * P 2 * Q 0 * Q 2 + 2 * W.a₁ * W.a₄ * P 0 * P 2 * Q 0 * Q 2
    + 2 * W.a₁ * W.a₃ * P 1 * P 2 * Q 0 * Q 2 + 2 * W.a₄ * P 1 * P 2 * Q 0 * Q 2
    + W.a₁ * W.a₃ ^ 2 * P 2 ^ 2 * Q 0 * Q 2 + 2 * W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 * Q 2
    + W.a₁ ^ 2 * P 0 ^ 2 * Q 1 * Q 2 + W.a₂ * P 0 ^ 2 * Q 1 * Q 2
    + 2 * W.a₁ * P 0 * P 1 * Q 1 * Q 2 + P 1 ^ 2 * Q 1 * Q 2
    + 2 * W.a₁ * W.a₃ * P 0 * P 2 * Q 1 * Q 2 + 2 * W.a₄ * P 0 * P 2 * Q 1 * Q 2
    + 2 * W.a₃ * P 1 * P 2 * Q 1 * Q 2 + W.a₃ ^ 2 * P 2 ^ 2 * Q 1 * Q 2
    + 3 * W.a₆ * P 2 ^ 2 * Q 1 * Q 2 + W.a₁ ^ 2 * W.a₃ * P 0 ^ 2 * Q 2 ^ 2
    + W.a₁ * W.a₄ * P 0 ^ 2 * Q 2 ^ 2 + 2 * W.a₁ * W.a₃ * P 0 * P 1 * Q 2 ^ 2
    + W.a₄ * P 0 * P 1 * Q 2 ^ 2 + W.a₃ * P 1 ^ 2 * Q 2 ^ 2
    + 2 * W.a₁ * W.a₃ ^ 2 * P 0 * P 2 * Q 2 ^ 2 + W.a₃ * W.a₄ * P 0 * P 2 * Q 2 ^ 2
    + 3 * W.a₁ * W.a₆ * P 0 * P 2 * Q 2 ^ 2 + 2 * W.a₃ ^ 2 * P 1 * P 2 * Q 2 ^ 2
    + 3 * W.a₆ * P 1 * P 2 * Q 2 ^ 2 + W.a₃ ^ 3 * P 2 ^ 2 * Q 2 ^ 2
    + 3 * W.a₃ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2
def diagY (W : Projective R) (P Q : Fin 3 → R) : R :=
  W.negY ![diagX W P Q, negDiagY W P Q, diagZ W P Q]
def diagXYZ (W : Projective R) (P Q : Fin 3 → R) : Fin 3 → R :=
  ![diagX W P Q, diagY W P Q, diagZ W P Q]
variable {W : Projective R}
end GlobalTheory.AddLaw


