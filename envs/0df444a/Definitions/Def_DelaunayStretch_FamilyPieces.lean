-- Prove2me | Definitions.Def_DelaunayStretch_FamilyPieces
-- name    : DelaunayStretch_FamilyPieces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T03:03:36.518072+00:00
-- url     : https://prove2.me/theorems/49f8b61e-9541-4618-b9c7-3bdfded883ff
-- title:
--   Pieces of the family $\mathcal H$: extended B-splines, $\widehat H$, $H^c$, $H^\pm$ and their gradients
-- statement:
--   Auxiliary objects of Definition 5.5 (p.34) of Mo–Cheng–Ding for a member $H$ of the family $\mathcal H$ of Definition 5.2, given by its rational coefficients $V_{ijl},R_{ijl},B_l,D_l$.
--
--   1. **Extended B-splines.** Each clamped cubic B-spline $N_l$ on $[0,1]$ is continued to $\tau<0$ by the cubic polynomial it equals on $[0,\tfrac1{32}]$. The coefficient functions $V,R,B,D$ built from these extended splines are then defined for all $\gamma\in(-\tfrac\pi2,\tfrac\pi2)$.
--   2. **The polynomial $\widehat H$.** For $|\gamma|<\tfrac\pi2$ and $a,b,\xi\in\mathbb R$,
--   $$
--   \widehat H(\gamma,a,b,\xi)=\cos^2\gamma\,V(\gamma,a,b)+\sigma(\gamma)\,\xi+\cos^2\gamma\Big[\big(B(\gamma)+R(\gamma,a,b)\big)(\xi-\xi^3)+D(\gamma)(\xi^3-\xi^5)\Big],
--   $$
--   where $\sigma(\gamma)=\gamma-\cos^2\gamma\,V(\gamma,0,1)$. This is the right-hand side of (5.2) with $\hat\xi$ replaced by $\xi$.
--   3. **Coordinates.** The positions are $a=\frac{\theta-\varphi+\gamma}{\pi+2\gamma}$ and $b=\frac{\theta+\varphi-\gamma}{\pi-2\gamma}$ of (5.5), and the rescaled balance variable is $\xi=\psi/k(\gamma)$ with $k(\gamma)=\tfrac\pi2-\cos\gamma$.
--   4. **Piece functions** (5.7). On the central piece, $H^c(\gamma,\varphi,\theta,\psi)=\widehat H(\gamma,a,b,\psi/k(\gamma))$. On the outer pieces, $H^\pm=\widehat H(\gamma,a,b,\pm1)$.
--   5. **Gradients of the pieces.** At a point $z\in\Omega\times\mathbb R$ with $\gamma\ge0$, a gradient of the pieces is the gradient at $z$ of $H^c$ if $|\xi|\le1$, of $H^+$ if $\xi\ge1$, and of $H^-$ if $\xi\le-1$.
--   6. **The reflection** $\rho_1(\gamma,\varphi,\theta,\psi)=(-\gamma,-\varphi,\theta,-\psi)$ of Lemma 5.4.
--
--   These objects let the conditions (H2) and (H4) on $H_\star$ be stated for the explicit pieces with $\gamma\ge0$, as in Lemma 5.7.
--
--   **Formalization Note** The extension of the B-splines is obtained by running the Cox–de Boor recursion from degree-0 splines in which the indicator of $[0,\tfrac1{32})$ is continued by $1$ to $\tau<0$. Gradients are Fréchet gradients in $\mathbb R^4$.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, arXiv:2609.07979v6, Definition 5.5 (p.34), Lemma 5.3 (5.5) (p.32), Lemma 5.4 (5.6) (p.33)

import Mathlib
import Definitions.Def_DelaunayStretch_potential
import Definitions.Def_DelaunayStretch_InFamilyH

namespace DelaunayStretch

/-- Degree-`0` B-splines extended to `τ < 0`: for `τ < 0` the indicator of the first nonempty
knot interval `[t₃, t₄) = [0, 1/32)` is continued by `1`, so that the Cox–de Boor recursion below
continues every B-spline `N_l` to `τ < 0` by the polynomial that it equals on `[0, 1/32]`
(Definition 5.5, p.34). For `τ ≥ 0` this is `bsplineDeg0`. -/
noncomputable def bsplineDeg0Ext (j : ℕ) (τ : ℝ) : ℝ :=
  if τ < 0 then (if j = 3 then 1 else 0) else bsplineDeg0 j τ

/-- The Cox–de Boor recursion on the knots `splineKnot` started from `bsplineDeg0Ext`. -/
noncomputable def bsplineBasisExt : ℕ → ℕ → ℝ → ℝ
  | 0, j, τ => bsplineDeg0Ext j τ
  | p + 1, j, τ =>
      (τ - splineKnot j) / (splineKnot (j + p + 1) - splineKnot j) * bsplineBasisExt p j τ +
        (splineKnot (j + p + 2) - τ) / (splineKnot (j + p + 2) - splineKnot (j + 1)) *
          bsplineBasisExt p (j + 1) τ

/-- **Extended B-spline** (Definition 5.5, p.34): the clamped cubic B-spline `N_l` on `[0, 1]`,
extended to `τ < 0` by the cubic polynomial that it equals on `[0, 1/32]`. -/
noncomputable def bsplineExt (l : ℕ) (τ : ℝ) : ℝ := bsplineBasisExt 3 l τ

/-- `V(γ, a, b)` with the extended B-splines (Definition 5.5). -/
noncomputable def familyVExt (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (γ a b : ℝ) : ℝ :=
  ∑ i : Fin 12, ∑ j : Fin 12, ∑ l : Fin 35,
    (V i j l : ℝ) * bernstein 11 i a * bernstein 11 j b * bsplineExt l (2 * γ / Real.pi)

/-- `R(γ, a, b)` with the extended B-splines (Definition 5.5). -/
noncomputable def familyRExt (R : Fin 6 → Fin 6 → Fin 35 → ℚ) (γ a b : ℝ) : ℝ :=
  ∑ i : Fin 6, ∑ j : Fin 6, ∑ l : Fin 35,
    (R i j l : ℝ) * bernstein 5 i a * bernstein 5 j b * bsplineExt l (2 * γ / Real.pi)

/-- `B(γ)`, `D(γ)` with the extended B-splines (Definition 5.5). -/
noncomputable def familySplineExt (c : Fin 35 → ℚ) (γ : ℝ) : ℝ :=
  ∑ l : Fin 35, (c l : ℝ) * bsplineExt l (2 * γ / Real.pi)

/-- `Ĥ(γ, a, b, ξ)` (Definition 5.5, p.34): the right-hand side of (5.2) with `ξ̂` replaced by
`ξ`, for `|γ| < π/2` and `a, b, ξ ∈ ℝ`:
`cos²γ V + σ ξ + cos²γ [(B + R)(ξ − ξ³) + D(ξ³ − ξ⁵)]`, `σ(γ) = γ − cos²γ V(γ, 0, 1)`. -/
noncomputable def familyHhat (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (γ a b ξ : ℝ) : ℝ :=
  Real.cos γ ^ 2 * familyVExt V γ a b + (γ - Real.cos γ ^ 2 * familyVExt V γ 0 1) * ξ +
    Real.cos γ ^ 2 * ((familySplineExt Bc γ + familyRExt R γ a b) * (ξ - ξ ^ 3) +
      familySplineExt Dc γ * (ξ ^ 3 - ξ ^ 5))

/-- The position `a = (θ − φ + γ)/(π + 2γ)` of (5.5) (Lemma 5.3, p.32). -/
noncomputable def posA (z : R4) : ℝ := (z.2.2.1 - z.2.1 + z.1) / (Real.pi + 2 * z.1)

/-- The position `b = (θ + φ − γ)/(π − 2γ)` of (5.5) (Lemma 5.3, p.32). -/
noncomputable def posB (z : R4) : ℝ := (z.2.2.1 + z.2.1 - z.1) / (Real.pi - 2 * z.1)

/-- The rescaled balance variable `ξ = ψ/k(γ)`, `k(γ) = π/2 − cos γ` (Definition 5.2). -/
noncomputable def balanceXi (z : R4) : ℝ := z.2.2.2 / (Real.pi / 2 - Real.cos z.1)

/-- The function `H^c` of the central piece (5.7): `Ĥ(γ, a, b, ψ/k(γ))`. -/
noncomputable def pieceHc (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (z : R4) : ℝ :=
  familyHhat V R Bc Dc z.1 (posA z) (posB z) (balanceXi z)

/-- The functions `H^±` of the outer pieces (5.7): `Ĥ(γ, a, b, ±1)`; `s = 1` gives `H⁺`,
`s = −1` gives `H⁻`. -/
noncomputable def pieceHout (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (s : ℝ) (z : R4) : ℝ :=
  familyHhat V R Bc Dc z.1 (posA z) (posB z) s

/-- **Gradients of the pieces** (Definition 5.5, p.34): `g` is a gradient of the pieces at `z`
if `z ∈ Ω × ℝ`, `γ ≥ 0`, and `g` is the gradient at `z` of the function of a piece containing
`z`: `H^c` if `|ξ| ≤ 1`, `H⁺` if `ξ ≥ 1`, `H⁻` if `ξ ≤ −1`. -/
def IsPieceGradient (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (z g : R4) : Prop :=
  z ∈ OmegaTimesR ∧ 0 ≤ z.1 ∧
    ((|balanceXi z| ≤ 1 ∧ g = gradient4 (pieceHc V R Bc Dc) z) ∨
      (1 ≤ balanceXi z ∧ g = gradient4 (pieceHout V R Bc Dc 1) z) ∨
      (balanceXi z ≤ -1 ∧ g = gradient4 (pieceHout V R Bc Dc (-1)) z))

/-- The reflection `ρ₁(γ, φ, θ, ψ) = (−γ, −φ, θ, −ψ)` (Lemma 5.4, (5.6), p.33). -/
def reflect1 (z : R4) : R4 := (-z.1, -z.2.1, z.2.2.1, -z.2.2.2)

end DelaunayStretch


