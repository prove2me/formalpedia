-- Prove2me | Definitions.Def_Dubey1986_Inefficiency_Example
-- name    : Dubey1986_Inefficiency_Example
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:53.082175+00:00
-- url     : https://prove2.me/theorems/cf87c822-725d-4036-be77-a6dedf18067a
-- title:
--   pp. 8–9 — the example game $(P,Q)$ on $[0,1]^2$, its Nash and efficient points, the retraction $r_C$
-- statement:
--   The example of §3 (due to J. D. Rogawski). Two players each choose a point of $[0,1]$; a profile is $(x_1,x_2)\in X=[0,1]\times[0,1]$. For $P=(a,b)\in\mathbb R^2$ let
--   $$u_P(x,y)=-\big[(x-a)^2+(y-b)^2\big],$$
--   the negative squared Euclidean distance to $P$. The game $(P,Q)$ gives player 1 the payoff $u_P$ and player 2 the payoff $u_Q$, $Q=(c,d)$.
--
--   A point $z\in X$ is a **Nash equilibrium** of $(P,Q)$ if player 1 cannot raise $u_P$ by changing $z_1$ within $[0,1]$ and player 2 cannot raise $u_Q$ by changing $z_2$ within $[0,1]$. It is **efficient** if no $w\in X$ has $u_P(w)\ge u_P(z)$, $u_Q(w)\ge u_Q(z)$ with one inequality strict. For a closed convex $C\subseteq\mathbb R^2$ and $M\in\mathbb R^2$, the **retraction** $r_C(M)$ is the point of $C$ closest to $M$ in Euclidean distance; for a set $L$, $r_C(L)=\{r_C(M):M\in L\}$.
--
--   **Formalization Note** Distances are written out as $(z_1-m_1)^2+(z_2-m_2)^2$ rather than with Mathlib's `dist` on `ℝ × ℝ`, which is the sup metric. The retraction is encoded as the relation "$z\in C$ is a closest point of $C$ to $M$"; for closed convex $C$ the closest point is unique.
-- source:
--   Dubey, Inefficiency of Nash Equilibria, IIASA WP-83-74 (July 1983), pp. 8–9 (§3)

import Mathlib

namespace Dubey1986.Inefficiency

/-- The squared Euclidean distance on `ℝ²` (not Mathlib's sup metric on `ℝ × ℝ`). -/
def sqDist (z m : ℝ × ℝ) : ℝ :=
  (z.1 - m.1) ^ 2 + (z.2 - m.2) ^ 2

/-- `u_P(x,y) = −[(x−a)² + (y−b)²]` for `P = (a,b)` (p. 8). -/
def uP (P z : ℝ × ℝ) : ℝ :=
  -sqDist z P

/-- The square `X = [0,1] × [0,1]` of strategy pairs (p. 8). -/
def Xsq : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- `z = (x₁, x₂)` is a Nash equilibrium of the game `(P,Q)`: player 1 (payoff `u_P`,
controls `x₁`) and player 2 (payoff `u_Q`, controls `x₂`) cannot gain by a unilateral
deviation in `[0,1]`. -/
def IsNashPQ (P Q z : ℝ × ℝ) : Prop :=
  z ∈ Xsq ∧ (∀ x ∈ Set.Icc (0 : ℝ) 1, uP P (x, z.2) ≤ uP P z) ∧
    (∀ y ∈ Set.Icc (0 : ℝ) 1, uP Q (z.1, y) ≤ uP Q z)

/-- `z` is efficient in the game `(P,Q)`: no `w ∈ X` with `u_P(w) ≥ u_P(z)`,
`u_Q(w) ≥ u_Q(z)` and one of them strict. -/
def IsEfficientPQ (P Q z : ℝ × ℝ) : Prop :=
  z ∈ Xsq ∧ ¬ ∃ w ∈ Xsq, uP P z ≤ uP P w ∧ uP Q z ≤ uP Q w ∧
    (uP P z < uP P w ∨ uP Q z < uP Q w)

/-- `z = r_C(M)`: `z` is a closest point of `C` to `M` in Euclidean distance (p. 9). -/
def IsRetraction (C : Set (ℝ × ℝ)) (M z : ℝ × ℝ) : Prop :=
  z ∈ C ∧ ∀ w ∈ C, sqDist z M ≤ sqDist w M

/-- `r_C(L) = {r_C(M) : M ∈ L}`. -/
def retractionImage (C L : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {z | ∃ M ∈ L, IsRetraction C M z}

end Dubey1986.Inefficiency


