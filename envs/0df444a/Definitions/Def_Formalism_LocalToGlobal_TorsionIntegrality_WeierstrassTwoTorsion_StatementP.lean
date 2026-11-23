-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementP
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:14.19003+00:00
-- url     : https://prove2.me/theorems/e31cc368-cc19-4cb9-92d2-40f1dbc196f0
-- title:
--   Statement P
-- statement:
--   Definitions and structural lemmas for Statement P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/StatementP.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
namespace Formalism.L2.Th1.A
def TSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP : R),
    constantCoeff (tDen W xP) = 1 ∧ tDen W xP * invOfUnit (tDen W xP) 1 = 1 ∧
    toL (tS W xP) * (xL W - HahnSeries.C xP) = 1 ∧
    coeff 2 (tS W xP) = 1 ∧ X ^ 2 ∣ tS W xP ∧
    (tS W xP).subst (iSer W) = tS W xP
def PlusChord : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP : R), W.toAffine.Equation xP yP →
    toL (xPlus W xP yP) = (curveL W).toAffine.addX (xL W) (HahnSeries.C xP) (slopeL W xP yP) ∧
    toL (yPlus W xP yP)
      = (curveL W).toAffine.addY (xL W) (HahnSeries.C xP) (yL W) (slopeL W xP yP)
def PlusFlow : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP : R), W.toAffine.Equation xP yP →
    IsFlow (curveS W) (D W) (xPlus W xP yP) (yPlus W xP yP) ∧
    constantCoeff (xPlus W xP yP) = xP ∧ constantCoeff (yPlus W xP yP) = yP
def PlusLogDeriv : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP : R), W.toAffine.Equation xP yP →
    DL W (toL (tS W xP) * DL W (xL W))
      = 2 * xL W - toL (xPlus W xP yP) - toL (xPlus W xP (W.toAffine.negY xP yP))
def PlusNeg : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP : R), W.toAffine.Equation xP yP →
    (xPlus W xP yP).subst (iSer W) = xPlus W xP (W.toAffine.negY xP yP)
def PlusMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)
    (xP yP : R),
    PowerSeries.map φ (tS W xP) = tS (W.map φ) (φ xP) ∧
    PowerSeries.map φ (xPlus W xP yP) = xPlus (W.map φ) (φ xP) (φ yP) ∧
    PowerSeries.map φ (yPlus W xP yP) = yPlus (W.map φ) (φ xP) (φ yP)
def TwoTorsionU : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xT yT : R), W.toAffine.Equation xT yT →
    2 * yT + W.a₁ * xT + W.a₃ = 0 →
    xPlus W xT yT = C xT + C (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * tS W xT ∧
    D W (tS W xT) ^ 2 = 4 * tS W xT + C (12 * xT + W.b₂) * tS W xT ^ 2
      + 4 * C (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * tS W xT ^ 3 ∧
    D W (D W (tS W xT)) = 2 + C (12 * xT + W.b₂) * tS W xT
      + 6 * C (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * tS W xT ^ 2
def TwoTorsionZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xT yT : K),
    W.toAffine.Equation xT yT → 2 * yT + W.a₁ * xT + W.a₃ = 0 →
    let e₁ : K := xT + W.b₂ / 12
    let kap : K := 3 * e₁ ^ 2 - g₂ W / 4
    let w₁ : K⟦X⟧ := (tS W xT).subst (expSer W)
    4 * e₁ ^ 3 - g₂ W * e₁ - g₃ W = 0 ∧
    (4 * Polynomial.X ^ 3 - Polynomial.C (g₂ W) * Polynomial.X - Polynomial.C (g₃ W) : Polynomial K)
      = 4 * (Polynomial.X - Polynomial.C e₁) *
        (Polynomial.X ^ 2 + Polynomial.C e₁ * Polynomial.X + Polynomial.C (e₁ ^ 2 - g₂ W / 4)) ∧
    kap = 3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT ∧
    toL w₁ * (wpL W - HahnSeries.C e₁) = 1 ∧
    X ^ 2 ∣ w₁ ∧ coeff 2 w₁ = 1 ∧ w₁.subst (-X : K⟦X⟧) = w₁ ∧
    derivative K w₁ ^ 2 = 4 * w₁ * (1 + 3 * C e₁ * w₁ + C kap * w₁ ^ 2) ∧
    derivative K (derivative K w₁) = 2 + 12 * C e₁ * w₁ + 6 * C kap * w₁ ^ 2 ∧
    (xPlus W xT yT).subst (expSer W) + C (W.b₂ / 12) = C e₁ + C kap * w₁ ∧
    ∀ e₂ e₃ : K, (4 * Polynomial.X ^ 3 - Polynomial.C (g₂ W) * Polynomial.X
        - Polynomial.C (g₃ W) : Polynomial K)
        = 4 * (Polynomial.X - Polynomial.C e₁) * (Polynomial.X - Polynomial.C e₂)
          * (Polynomial.X - Polynomial.C e₃) →
      kap = (e₁ - e₂) * (e₁ - e₃) ∧
      derivative K w₁ ^ 2 = 4 * w₁ * (1 + C (e₁ - e₂) * w₁) * (1 + C (e₁ - e₃) * w₁)
def PlusZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP yP : K),
    W.toAffine.Equation xP yP →
    IsFlow (curveS W) (derivative K) ((xPlus W xP yP).subst (expSer W))
      ((yPlus W xP yP).subst (expSer W)) ∧
    toL ((tS W xP).subst (expSer W)) * (xZ W - HahnSeries.C xP) = 1 ∧
    dL (toL ((tS W xP).subst (expSer W)) * dL (wpL W))
      = 2 * xZ W - toL ((xPlus W xP yP).subst (expSer W))
        - toL ((xPlus W xP (W.toAffine.negY xP yP)).subst (expSer W))
end Formalism.L2.Th1.A


