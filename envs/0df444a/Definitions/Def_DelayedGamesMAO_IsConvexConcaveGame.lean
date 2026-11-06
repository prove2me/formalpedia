-- Prove2me | Definitions.Def_DelayedGamesMAO_IsConvexConcaveGame
-- name    : DelayedGamesMAO_IsConvexConcaveGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:44.246048+00:00
-- url     : https://prove2.me/theorems/fc46185f-1b4c-4d4f-a3f6-f7cabc3e0a49
-- title:
--   Differentiable convex–concave zero-sum game with gradient maps $g^x,g^y$
-- statement:
--   Let $X$ and $Y$ be subsets of real normed spaces, $f:X\times Y\to\mathbb R$, and $g^x,g^y$ maps on $X\times Y$ with values in the dual spaces. The predicate says that
--
--   1. $f(\cdot,y)$ is convex on $X$ for every $y\in Y$, and $f(x,\cdot)$ is concave on $Y$ for every $x\in X$;
--   2. for every $(x,y)\in X\times Y$, $g^x(x,y)$ is the derivative of $f(\cdot,y)$ at $x$ within $X$, and $-g^y(x,y)$ is the derivative of $f(x,\cdot)$ at $y$ within $Y$.
--
--   Thus $g^x=\nabla_xf$ and $g^y=-\nabla_yf$ are the players' loss gradients: player $x$ minimizes $f$, player $y$ maximizes it.
--
--   **Formalization Note** $f$ is a function on the ambient product of which only the values on $X\times Y$ are used; the gradients are explicit fields, which asks nothing of $f$ off $X\times Y$ and is meaningful for sets with empty interior.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §2, Zero-sum games, p.3; §3, p.4

import Mathlib

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **A differentiable convex–concave zero-sum game on `X × Y`** with loss-gradient maps
`g^x = ∇_x f` and `g^y = −∇_y f`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §2 "Zero-sum games", p.3: "let `f : X × Y → ℝ` be differentiable, convex in its first
argument, and concave in its second"; §3, p.4: "let `g^x(x, y) := ∇_x f(x, y)` and
`g^y(x, y) := −∇_y f(x, y)` denote the players' loss gradients".

**Formalization Note.** `f` is a function on the ambient product whose values only on `X × Y`
are used. The gradients are explicit fields: `gx x y` is a derivative of `f(·, y)` within `X`
at `x`, and `-(gy x y)` a derivative of `f(x, ·)` within `Y` at `y`, for `(x, y) ∈ X × Y`.
This asks nothing of `f` off `X × Y` and is meaningful for sets with empty interior. -/
def IsConvexConcaveGame {EX EY : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
    [NormedAddCommGroup EY] [NormedSpace ℝ EY] (X : Set EX) (Y : Set EY) (f : EX → EY → ℝ)
    (gx : EX → EY → EX →L[ℝ] ℝ) (gy : EX → EY → EY →L[ℝ] ℝ) : Prop :=
  (∀ y ∈ Y, ConvexOn ℝ X (fun x => f x y)) ∧ (∀ x ∈ X, ConcaveOn ℝ Y (f x)) ∧
  ∀ x ∈ X, ∀ y ∈ Y,
    HasFDerivWithinAt (fun x' => f x' y) (gx x y) X x ∧ HasFDerivWithinAt (f x) (-(gy x y)) Y y

end DelayedGamesMAO


