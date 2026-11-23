-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementO
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementO
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:12.972371+00:00
-- url     : https://prove2.me/theorems/85dae8e5-b03d-433b-a18a-58f70f2cc0a3
-- title:
--   Statement O
-- statement:
--   Definitions and structural lemmas for Statement O, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/StatementO.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
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
def divSer {R : Type u} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) : R⟦X⟧ := compInv (zSer W n)
def DivSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (n : ℤ), IsUnit (n : R) →
    constantCoeff (divSer W n) = 0 ∧ (n : R) * coeff 1 (divSer W n) = 1 ∧
    (zSer W n).subst (divSer W n) = X ∧ (divSer W n).subst (zSer W n) = X ∧
    (∀ (S : Type v) [CommRing S] (φ : R →+* S),
      PowerSeries.map φ (divSer W n) = divSer (W.map φ) n) ∧
    (n = 2 → divSer W n = halfSer W)
def DivLog : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (n : ℤ), n ≠ 0 →
    C (n : K) * (logSer W).subst (divSer W n) = logSer W
def FlowDouble : Prop :=
  ∀ (A : Type u) [CommRing A] (W : WeierstrassCurve A) (D : A → A) (x y s : A),
    IsDer D → ConstCurve D W → IsFlow W D x y → s * (2 * y + W.a₁ * x + W.a₃) = 1 →
    let ℓ := (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * s
    W.toAffine.Equation (W.toAffine.addX x x ℓ) (W.toAffine.addY x x y ℓ) ∧
    D (W.toAffine.addX x x ℓ)
      = 2 * (2 * W.toAffine.addY x x y ℓ + W.a₁ * W.toAffine.addX x x ℓ + W.a₃) ∧
    W.toAffine.addX x x ℓ * (2 * y + W.a₁ * x + W.a₃) ^ 2
      = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈
end Formalism.L2.Th1.A


