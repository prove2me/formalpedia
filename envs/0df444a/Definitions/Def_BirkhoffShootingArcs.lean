-- Prove2me | Definitions.Def_BirkhoffShootingArcs
-- name    : BirkhoffShootingArcs
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-09-25T09:16:18.281856+00:00
-- url     : https://prove2.me/theorems/b78a7042-024e-4a93-bf65-9af6b805dcb4
-- title:
--   Birkhoff's perpendicular starts and shooting arcs
-- statement:
--   This file fixes the two families of perpendicular starts in Birkhoff's shooting argument, and the notion of a shooting arc, for $0<\mu<1$ and the Levi-Civita energy level $K_{\mu,c}=0$. Points are $s=(z,w)\in\mathbb R^4$, and $x=2z^2$ is the position relative to the primary $P$ of mass $1-\mu$.
--
--   1. **Near starts.** For $r\ge0$, the state $N_{\mu,c}(r)$ has $z=(r,0)$ and $w=(0,w_2)$, where
--   $$
--   w_2=\sqrt{(1-\mu)+r^2\Bigl((2r^2-\mu)^2+\tfrac{2\mu}{|2r^2-1|}-2c\Bigr)}\;-\;r(2r^2-\mu).
--   $$
--   It lies at distance $2r^2$ from $P$ on the side facing the other primary. Its Jacobi velocity is vertical and points upward, and $K_{\mu,c}(N_{\mu,c}(r))=0$ whenever the radicand is nonnegative. The formula is the energy relation $|v|^2=2(\Omega-c)$ multiplied by $r^2$, so it stays regular at $r=0$.
--   2. **Far starts.** For $r\ge0$, the state $F_{\mu,c}(r)$ has $z=(0,r)$, $w=(w_1,0)$ with
--   $$
--   w_1=r(2r^2+\mu)-\sqrt{(1-\mu)+r^2\Bigl((2r^2+\mu)^2+\tfrac{2\mu}{1+2r^2}-2c\Bigr)} .
--   $$
--   It lies at distance $2r^2$ from $P$ on the side away from the other primary, and its vertical velocity points downward.
--   3. **Near shooting arc of length $\tau$.** For $-\tau<t<0$, the backward trajectory $\varphi_t s$ lies in the open quadrant $\{x_1>0,\ x_2<0\}$. At $t=-\tau$ it lies on the line $x_1=0$ with $x_2<0$.
--   4. **Far shooting arc of length $\tau$.** For $0<u<\tau$, the forward trajectory $\varphi_u s$ lies strictly below the axis, and its horizontal Jacobi velocity is positive for $0<u\le\tau$. At $u=\tau$ it lies on the line $x_1=0$ with $x_2<0$.
--
--   These are the objects of Birkhoff's two shooting families. The crossing coordinates of the arcs trace the curves $\Gamma_2$ (near) and $\Gamma_1$ (far) in Liu–Salomão's proof of Theorem 5.1.
-- source:
--   Liu--Salomao, Finite energy foliations in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Section 5, proof of Theorem 5.1 (pp. 30-31); G. D. Birkhoff, The restricted problem of three bodies, Rend. Circ. Mat. Palermo 39 (1915), Section 18.

import Definitions.Def_BirkhoffShootingCoordinates

namespace BirkhoffGlobalSection

noncomputable section

/-- The Levi-Civita state on the near half-axis `z = (r,0)` whose velocity is perpendicular
to the axis and points upward (`v₂ > 0`), normalized to the energy level `K = 0`:
`w = (0, √(2 r² (Ω - c)) - r (2r² - μ))`, written in a form regular at `r = 0`. -/
def nearShootingStart (μ c r : ℝ) : Phase :=
  ![r, 0, 0,
    Real.sqrt ((1 - μ) + r ^ 2 * ((2 * r ^ 2 - μ) ^ 2 + 2 * μ / |2 * r ^ 2 - 1| - 2 * c))
      - r * (2 * r ^ 2 - μ)]

/-- The Levi-Civita state on the far half-axis `z = (0,r)` whose velocity is perpendicular
to the axis and points downward (`v₂ < 0`), normalized to the energy level `K = 0`. -/
def farShootingStart (μ c r : ℝ) : Phase :=
  ![0, r,
    r * (2 * r ^ 2 + μ)
      - Real.sqrt ((1 - μ) + r ^ 2 * ((2 * r ^ 2 + μ) ^ 2 + 2 * μ / (1 + 2 * r ^ 2) - 2 * c)),
    0]

/-- A near shooting arc of backward length `τ`: going backward from `x`, the trajectory stays
in the open quadrant `{x₁ > 0, x₂ < 0}` and then reaches the vertical line `x₁ = 0`
strictly below the axis. -/
def IsNearShootingArc {μ c : ℝ} (φ : Flow ℝ (LeftEnergyState μ c))
    (x : LeftEnergyState μ c) (τ : ℝ) : Prop :=
  0 < τ ∧
  (∀ t ∈ Set.Ioo (-τ) 0,
    0 < relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0 ∧
    relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
  relativePosition μ ((φ (-τ) x : LeftEnergyState μ c) : Phase) 1 < 0 ∧
  relativePosition μ ((φ (-τ) x : LeftEnergyState μ c) : Phase) 0 = 0

/-- A far shooting arc of length `τ`: going forward from `x`, the trajectory stays strictly
below the axis, moves with positive horizontal velocity after time `0`, and reaches the
vertical line `x₁ = 0` at time `τ`. -/
def IsFarShootingArc {μ c : ℝ} (φ : Flow ℝ (LeftEnergyState μ c))
    (x : LeftEnergyState μ c) (τ : ℝ) : Prop :=
  0 < τ ∧
  (∀ u ∈ Set.Ioo 0 τ,
    relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
  relativePosition μ ((φ τ x : LeftEnergyState μ c) : Phase) 1 < 0 ∧
  relativePosition μ ((φ τ x : LeftEnergyState μ c) : Phase) 0 = 0 ∧
  ∀ u ∈ Set.Ioc 0 τ,
    0 < jacobiVelocity (leviCivitaToJacobi μ ((φ u x : LeftEnergyState μ c) : Phase)) 0

end

end BirkhoffGlobalSection


