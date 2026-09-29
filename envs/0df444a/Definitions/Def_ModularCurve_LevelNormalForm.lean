-- Prove2me | Definitions.Def_ModularCurve_LevelNormalForm
-- name    : ModularCurve_LevelNormalForm
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/42d63976-448e-561e-8b1a-c09fd2216123
-- title:
--   Normal form for a Weierstrass curve with level data
-- statement:
--   Over a commutative ring $T$, the predicate [`ModularCurve.IsNormalForm`](../def/ModularCurve_LevelNormalForm.html#L10) takes a natural number $\ell$, a Weierstrass curve $W$ over $T$ (with coefficients $a_1,\dots,a_6$) and a quadruple $D = (x_P, y_P, x_Q, y_Q)$ of elements of $T$ (the project's `LevelPData`, the coordinates of two affine points), and asserts a list of equations on these data, split according to whether $\ell$ equals $3$. For $\ell = 3$ it asserts $a_2 = 0$, $a_4 = 0$, $a_6 = 0$, $x_P = 0$, $y_P = 0$ and $x_Q = y_Q$. For every $\ell \neq 3$ it asserts $a_4 = 0$, $a_6 = 0$, $a_2 = a_3$, $x_P = 0$ and $y_P = 0$; thus in the second case the curve is $y^2 + a_1xy + a_3y = x^3 + a_3x^2$ with the first point at the affine origin, the shape of the Tate normal form, while in the case $\ell = 3$ the curve is $y^2 + a_1xy + a_3y = x^3$ with the first point at the origin and the second on the line $x = y$. It is a condition on a chosen Weierstrass presentation together with chosen coordinates, not on an isomorphism class, and it imposes nothing beyond these equations: neither invertibility of the discriminant nor the condition `IsLevelPStructure` on $D$ is required. Two rewriting lemmas record the two branches of the definition explicitly, and [`ModularCurve.IsNormalForm.map`](../def/ModularCurve_LevelNormalForm.html#L25) states that the predicate is preserved by base change along a ring homomorphism $f : T \to T'$, applied to the coefficients of $W$ and to the four coordinates of $D$.
--
--   **Relation to Mathlib.** `WeierstrassCurve` and its base change `WeierstrassCurve.map` are Mathlib's; the level data $D$ and the normal-form predicate are the project's own, Mathlib having no notion of Tate or Deuring normal form.
--
--   **Where it is used.** The predicate selects a distinguished Weierstrass presentation in each orbit of the change-of-variables action on pairs (Weierstrass curve, level-$\ell$ data), so that the moduli problem of level-$\ell$ structures can be handled in explicit Weierstrass coordinates; this underlies the Katz-style level-$\ell$ modular forms of the accompanying definitions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LevelNormalForm.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace ModularCurve

def IsNormalForm {T : Type u} [CommRing T] (ℓ : ℕ) (W : WeierstrassCurve T) (D : LevelPData T) : Prop :=
  if ℓ = 3 then
    W.a₂ = 0 ∧ W.a₄ = 0 ∧ W.a₆ = 0 ∧ D.xP = 0 ∧ D.yP = 0 ∧ D.xQ = D.yQ
  else
    W.a₄ = 0 ∧ W.a₆ = 0 ∧ W.a₂ = W.a₃ ∧ D.xP = 0 ∧ D.yP = 0

theorem isNormalForm_of_ne_three {T : Type u} [CommRing T] {ℓ : ℕ} (hℓ : ℓ ≠ 3) (W : WeierstrassCurve T)
    (D : LevelPData T) :
    IsNormalForm ℓ W D ↔ W.a₄ = 0 ∧ W.a₆ = 0 ∧ W.a₂ = W.a₃ ∧ D.xP = 0 ∧ D.yP = 0 := by
  simp [IsNormalForm, hℓ]

theorem isNormalForm_three {T : Type u} [CommRing T] (W : WeierstrassCurve T) (D : LevelPData T) :
    IsNormalForm 3 W D ↔ W.a₂ = 0 ∧ W.a₄ = 0 ∧ W.a₆ = 0 ∧ D.xP = 0 ∧ D.yP = 0 ∧ D.xQ = D.yQ := by
  simp [IsNormalForm]

theorem IsNormalForm.map {T T' : Type u} [CommRing T] [CommRing T'] {ℓ : ℕ} {W : WeierstrassCurve T}
    {D : LevelPData T} (h : IsNormalForm ℓ W D) (f : T →+* T') : IsNormalForm ℓ (W.map f) (D.map f) := by
  unfold IsNormalForm at h ⊢
  split_ifs at h ⊢ with h3
  · obtain ⟨h1, h2, h3', h4, h5, h6⟩ := h
    simp [WeierstrassCurve.map, LevelPData.map, h1, h2, h3', h4, h5, h6]
  · obtain ⟨h1, h2, h3', h4, h5⟩ := h
    simp [WeierstrassCurve.map, LevelPData.map, h1, h2, h3', h4, h5]

end ModularCurve


