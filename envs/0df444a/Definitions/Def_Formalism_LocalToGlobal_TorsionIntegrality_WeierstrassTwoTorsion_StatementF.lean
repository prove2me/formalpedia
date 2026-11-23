-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:56:03.898202+00:00
-- url     : https://prove2.me/theorems/45ba6ea7-bf29-404c-ba0a-443fb066d902
-- title:
--   Statement F
-- statement:
--   Definitions and structural lemmas for Statement F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/StatementF.lean

import Mathlib
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
variable {A : Type u} [CommRing A]
def IsDer (D : A → A) : Prop :=
  (∀ a b, D (a + b) = D a + D b) ∧ ∀ a b, D (a * b) = a * D b + b * D a
def ConstCurve (D : A → A) (W : WeierstrassCurve A) : Prop :=
  D W.a₁ = 0 ∧ D W.a₂ = 0 ∧ D W.a₃ = 0 ∧ D W.a₄ = 0 ∧ D W.a₆ = 0
def IsFlow (W : WeierstrassCurve A) (D : A → A) (x y : A) : Prop :=
  W.toAffine.Equation x y ∧ D x = 2 * y + W.a₁ * x + W.a₃ ∧
    D y = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
def WEq (W : WeierstrassCurve A) (u w : A) : Prop :=
  w = u ^ 3 + W.a₁ * u * w + W.a₂ * u ^ 2 * w + W.a₃ * w ^ 2 + W.a₄ * u * w ^ 2 + W.a₆ * w ^ 3
def fwAt (W : WeierstrassCurve A) (u w : A) : A :=
  1 - W.a₁ * u - W.a₂ * u ^ 2 - 2 * W.a₃ * w - 2 * W.a₄ * u * w - 3 * W.a₆ * w ^ 2
def fuAt (W : WeierstrassCurve A) (u w : A) : A :=
  3 * u ^ 2 + W.a₁ * w + 2 * W.a₂ * u * w + W.a₄ * w ^ 2
def IsFlowUW (W : WeierstrassCurve A) (D : A → A) (u w : A) : Prop :=
  WEq W u w ∧ D u = fwAt W u w ∧ D w = fuAt W u w
def FlowOfUW : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (u w v : A),
    IsDer D → IsFlowUW W D u w → v * w = 1 → IsFlow W D (u * v) (-v)
def FlowUWOfFirst : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (u w : A),
    IsDer D → ConstCurve D W → WEq W u w → D u = fwAt W u w →
    (∀ a : A, fwAt W u w * a = 0 → a = 0) → IsFlowUW W D u w
def FlowSq : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (x y : A),
    IsDer D → ConstCurve D W → IsFlow W D x y →
    D x ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ∧
    D (D x) = 6 * x ^ 2 + W.b₂ * x + W.b₄
def FlowWp : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (x y c g2 g3 : A),
    IsDer D → ConstCurve D W → IsFlow W D x y → IsUnit (6 : A) →
    12 * c = W.b₂ → 12 * g2 = W.c₄ → 216 * g3 = W.c₆ →
    D (x + c) = 2 * y + W.a₁ * x + W.a₃ ∧
    D (x + c) ^ 2 = 4 * (x + c) ^ 3 - g2 * (x + c) - g3 ∧
    2 * D (D (x + c)) = 12 * (x + c) ^ 2 - g2
def FlowNeg : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (x y : A),
    IsDer D → ConstCurve D W → IsFlow W D x y →
    IsFlow W (fun a => -D a) x (W.toAffine.negY x y)
def FlowTranslate : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (x y xP yP t : A),
    IsDer D → ConstCurve D W → IsFlow W D x y → W.toAffine.Equation xP yP → D xP = 0 → D yP = 0 →
    t * (x - xP) = 1 →
    IsFlow W D (W.toAffine.addX x xP ((y - yP) * t)) (W.toAffine.addY x xP y ((y - yP) * t))
def FlowLogDeriv : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (x y xP yP t : A),
    IsDer D → ConstCurve D W → IsFlow W D x y → W.toAffine.Equation xP yP → D xP = 0 → D yP = 0 →
    t * (x - xP) = 1 →
    D (t * D x) = 2 * x - W.toAffine.addX x xP ((y - yP) * t)
      - W.toAffine.addX x xP ((y - W.toAffine.negY xP yP) * t)
def ChordRegular : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (x y xP yP t : A),
    W.toAffine.Equation x y → W.toAffine.Equation xP yP → t * (x - xP) = 1 →
    W.toAffine.addX x xP ((y - yP) * t) = xP +
      ((W.a₄ - W.a₁ * yP + 2 * W.a₂ * xP + 3 * xP ^ 2) * x - (2 * yP + W.a₁ * xP + W.a₃) * y
        + (2 * W.a₆ + W.a₄ * xP - W.a₃ * yP - xP ^ 3)) * t ^ 2 ∧
    W.toAffine.addY x xP y ((y - yP) * t) =
      -((y - yP) * t * (W.toAffine.addX x xP ((y - yP) * t) - xP)) - yP
        - W.a₁ * W.toAffine.addX x xP ((y - yP) * t) - W.a₃
def FlowTwoTorsion : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (x y xT yT t : A),
    IsDer D → ConstCurve D W → IsFlow W D x y → W.toAffine.Equation xT yT → D xT = 0 → D yT = 0 →
    2 * yT + W.a₁ * xT + W.a₃ = 0 → t * (x - xT) = 1 →
    W.toAffine.addX x xT ((y - yT) * t)
      = xT + (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * t ∧
    D t ^ 2 = 4 * t + (12 * xT + W.b₂) * t ^ 2
      + 4 * (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * t ^ 3 ∧
    D (D t) = 2 + (12 * xT + W.b₂) * t
      + 6 * (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * t ^ 2
def FlowTwoTorsionWp : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A)
    (x y xT yT t c g2 g3 kap : A),
    IsDer D → ConstCurve D W → IsFlow W D x y → W.toAffine.Equation xT yT → D xT = 0 → D yT = 0 →
    2 * yT + W.a₁ * xT + W.a₃ = 0 → t * (x - xT) = 1 → IsUnit (6 : A) →
    12 * c = W.b₂ → 12 * g2 = W.c₄ → 216 * g3 = W.c₆ → 4 * kap = 12 * (xT + c) ^ 2 - g2 →
    4 * (xT + c) ^ 3 - g2 * (xT + c) - g3 = 0 ∧
    kap = 3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT ∧
    W.toAffine.addX x xT ((y - yT) * t) + c = (xT + c) + kap * t ∧
    D t ^ 2 = 4 * t * (1 + 3 * (xT + c) * t + kap * t ^ 2) ∧
    ∀ e2 e3 : A, (xT + c) + e2 + e3 = 0 → 4 * ((xT + c) * e2 + (xT + c) * e3 + e2 * e3) = -g2 →
      D t ^ 2 = 4 * t * (1 + ((xT + c) - e2) * t) * (1 + ((xT + c) - e3) * t)
def FlowThird : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] (W : WeierstrassCurve A) (D : A → A)
    (u1 w1 u2 w2 l n u3 : A),
    IsDer D → ConstCurve D W → IsFlowUW W D u1 w1 → WEq W u2 w2 → D u2 = 0 → D w2 = 0 →
    l * (u1 - u2) = w1 - w2 → n = w1 - l * u1 →
    (1 + W.a₂ * l + W.a₄ * l ^ 2 + W.a₆ * l ^ 3) * (u1 + u2 + u3)
      + (W.a₁ * l + W.a₂ * n + W.a₃ * l ^ 2 + 2 * W.a₄ * l * n + 3 * W.a₆ * l ^ 2 * n) = 0 →
    1 + W.a₂ * l + W.a₄ * l ^ 2 + W.a₆ * l ^ 3 ≠ 0 → u1 ≠ u2 → u3 ≠ u1 → u3 ≠ u2 →
    WEq W u3 (l * u3 + n) ∧ D u3 = -fwAt W u3 (l * u3 + n) ∧
      D (l * u3 + n) = -fuAt W u3 (l * u3 + n)
def FlowNegUW : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (u w r : A),
    IsDer D → ConstCurve D W → IsFlowUW W D u w → r * (-1 + W.a₁ * u + W.a₃ * w) = 1 →
    IsFlowUW W (fun a => -D a) (u * r) (w * r)
end Formalism.L2.Th1.A


