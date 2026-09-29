-- Prove2me | Definitions.Def_EllipticCurve_FifteenA1
-- name    : EllipticCurve_FifteenA1
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/cd88ac3f-9b4e-5222-a79a-53ff923c7569
-- title:
--   The curve 15a1: short model, square classes, descent map
-- statement:
--   Four objects are introduced, all attached to the elliptic curve of conductor $15$ with Cremona label 15a1, i.e. the modular curve $X_0(15)$.
--
--   `shortW` is the affine Weierstrass curve over $\mathbb{Q}$ with coefficients $(a_1,a_2,a_3,a_4,a_6) = (0,5,0,-152,-624)$, that is
--   $$Y^2 = X^3 + 5X^2 - 152X - 624 = (X-12)(X+4)(X+13),$$
--   the completed-square model obtained from the minimal model $y^2 + xy + y = x^3 + x^2 - 10x - 10$ by $X = 4x$, $Y = 8y + 4x + 4$; all three points of order $2$ are rational, with abscissae $12$, $-4$, $-13$. Five lemmas record the individual coefficients.
--
--   `IsSqClass d a` is the predicate $\exists c \in \mathbb{Q},\ c \neq 0 \wedge a = d c^2$, i.e. $a$ lies in the square class $d\,(\mathbb{Q}^\times)^2$; for $d \neq 0$ this is equality of the images of $a$ and $d$ in $\mathbb{Q}^\times/(\mathbb{Q}^\times)^2$.
--
--   `deltaPair` is a total function from the points of `shortW` (Mathlib's inductive type of affine points, with its point at infinity) to $\mathbb{Q} \times \mathbb{Q}$, given by cases: the point at infinity goes to $(1,1)$, and an affine point with abscissa $X$ goes to $(X - 12,\ X + 4)$ except that the first coordinate is replaced by $400$ when $X = 12$ and the second by $-144$ when $X = -4$. Thus the $2$-torsion point $(12,0)$ has image $(400,16)$ and $(-4,0)$ has image $(-16,-144)$, the vanishing factor being replaced by the product of the differences of the remaining roots, as in the classical complete $2$-descent map $P \mapsto ([X-e_1],[X-e_2])$. Two lemmas state the two cases of this definition explicitly.
--
--   `V₀` is the four-element finite subset $\{(1,1), (-5,-1), (-1,-1), (5,1)\}$ of $\mathbb{Q} \times \mathbb{Q}$, a set of representatives for the pairs of square classes realised by `deltaPair`.
--
--   **Relation to Mathlib.** `shortW` is an instance of Mathlib's `WeierstrassCurve.Affine` over $\mathbb{Q}$ and `deltaPair` is defined on Mathlib's `WeierstrassCurve.Affine.Point` for it; the square-class predicate `IsSqClass` and the descent map are the project's own.
--
--   **Where it is used.** These objects carry the complete $2$-descent on $X_0(15)$: the containment of the image of `deltaPair` in `V₀` modulo squares, its homomorphism property, and the determination of its kernel, which together give $X_0(15)(\mathbb{Q}) \cong \mathbb{Z}/4 \times \mathbb{Z}/2$. This Mordell–Weil computation is the input to the classification of elliptic curves over $\mathbb{Q}$ admitting a rational $15$-isogeny, which is what rules out simultaneous reducibility of the mod $3$ and mod $5$ representations of the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_EllipticCurve_FifteenA1.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Rat.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ModularCurve

namespace FifteenA1

open WeierstrassCurve Affine

def shortW : WeierstrassCurve.Affine ℚ := ⟨0, 5, 0, -152, -624⟩

@[simp] theorem shortW_a₁ : shortW.a₁ = 0 := rfl
@[simp] theorem shortW_a₂ : shortW.a₂ = 5 := rfl
@[simp] theorem shortW_a₃ : shortW.a₃ = 0 := rfl
@[simp] theorem shortW_a₄ : shortW.a₄ = -152 := rfl
@[simp] theorem shortW_a₆ : shortW.a₆ = -624 := rfl

def IsSqClass (d a : ℚ) : Prop := ∃ c : ℚ, c ≠ 0 ∧ a = d * c ^ 2

def deltaPair : shortW.Point → ℚ × ℚ
  | .zero => (1, 1)
  | .some X _ _ =>
      (if X = 12 then 400 else X - 12, if X = -4 then -144 else X + 4)

@[simp] theorem deltaPair_zero : deltaPair 0 = (1, 1) := rfl

theorem deltaPair_some {X Y : ℚ} (h : shortW.Nonsingular X Y) :
    deltaPair (.some X Y h) =
      (if X = 12 then 400 else X - 12, if X = -4 then -144 else X + 4) := rfl

def V₀ : Finset (ℚ × ℚ) := {(1, 1), (-5, -1), (-1, -1), (5, 1)}

end FifteenA1

end ModularCurve


