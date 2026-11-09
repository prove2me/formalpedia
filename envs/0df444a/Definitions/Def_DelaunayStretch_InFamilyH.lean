-- Prove2me | Definitions.Def_DelaunayStretch_InFamilyH
-- name    : DelaunayStretch_InFamilyH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:53:32.635286+00:00
-- url     : https://prove2.me/theorems/2a69af46-da0f-408c-ac8c-ce7a9b073128
-- title:
--   The family $\mathcal H$ of Definition 5.2 (B-splines, Bernstein polynomials, coefficient symmetries)
-- statement:
--   Let $N_0,\dots,N_{34}$ be the clamped uniform cubic B-splines on $[0,1]$ with knots $(0,0,0,0,\frac1{32},\frac2{32},\dots,\frac{31}{32},1,1,1,1)$, and $\mathcal B^d_i(x)=\binom di x^i(1-x)^{d-i}$ the Bernstein polynomials. For rational numbers $V_{ijl}$ ($0\le i,j\le11$), $R_{ijl}$ ($0\le i,j\le5$), $B_l$, $D_l$ ($0\le l\le34$), $\gamma\in[0,\pi/2]$, $a,b\in\mathbb R$ and $\tau=2\gamma/\pi$, let
--
--   $$
--   V(\gamma,a,b)=\sum_{i,j,l}V_{ijl}\,\mathcal B^{11}_i(a)\mathcal B^{11}_j(b)N_l(\tau),\qquad R(\gamma,a,b)=\sum_{i,j,l}R_{ijl}\,\mathcal B^{5}_i(a)\mathcal B^{5}_j(b)N_l(\tau),
--   $$
--
--   $B(\gamma)=\sum_lB_lN_l(\tau)$, $D(\gamma)=\sum_lD_lN_l(\tau)$, $\sigma(\gamma)=\gamma-\cos^2\gamma\,V(\gamma,0,1)$ and $k(\gamma)=\frac\pi2-\cos\gamma$. For $(\gamma,\varphi,\theta,\psi)\in\Omega\times\mathbb R$ let $a=\frac{\theta-\varphi+\gamma}{\pi+2\gamma}$, $b=\frac{\theta+\varphi-\gamma}{\pi-2\gamma}$, $\xi=\psi/k(\gamma)$, $\hat\xi=\mathrm{clip}_1(\xi)$, and for $\gamma\ge0$
--
--   $$
--   H(\gamma,\varphi,\theta,\psi)=\cos^2\gamma\,V(\gamma,a,b)+\sigma(\gamma)\hat\xi+\cos^2\gamma\big[(B(\gamma)+R(\gamma,a,b))(\hat\xi-\hat\xi^3)+D(\gamma)(\hat\xi^3-\hat\xi^5)\big],
--   $$
--
--   and $H(\gamma,\varphi,\theta,\psi)=H(-\gamma,-\varphi,\theta,-\psi)$ for $\gamma<0$. The **family $\mathcal H$** consists of the functions obtained this way from coefficients with
--
--   $$
--   V_{11-i,11-j,l}=-V_{ijl},\quad R_{5-i,5-j,l}=R_{ijl},\quad R_{ijl}=0\ \text{for }(i,j)\in\{0,5\}^2,\quad V_{ij0}=V_{ji0},\quad R_{ij0}=-R_{ji0},\quad B_0=D_0=0 .
--   $$
--
--   The explicit function $H_\star$ of Theorem 5.1 is a member of $\mathcal H$.
--
--   **Formalization Note** The B-splines are defined by the Cox–de Boor recursion with the convention $0/0=0$, and the last knot interval $[31/32,1]$ is closed, so that $N_{34}(1)=1$ and the splines sum to $1$ on all of $[0,1]$. The positions $a$, $b$ are given by the closed form (5.5), which is the unique solution of (5.1) on $\Omega$ (Lemma 5.3). Membership in $\mathcal H$ asks equality on $\Omega\times\mathbb R$, the domain of these functions; values elsewhere are irrelevant.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Definition 5.2, pp.31–32 (with Lemma 5.3, eq. (5.5), p.32)

import Mathlib
import Definitions.Def_DelaunayStretch_SigmaSet

namespace DelaunayStretch

/-- The knots `(0, 0, 0, 0, 1/32, 2/32, …, 31/32, 1, 1, 1, 1)` of the clamped uniform cubic
B-splines: `t_j = min(1, max(0, (j − 3)/32))`, `j = 0, …, 38` (Definition 5.2, p.31). -/
noncomputable def splineKnot (j : ℕ) : ℝ := max 0 (min 1 (((j : ℝ) - 3) / 32))

/-- Degree-`0` B-splines: the indicator of `[t_j, t_{j+1})`, with the last nonempty interval
`[t₃₄, t₃₅] = [31/32, 1]` closed at `1`. -/
noncomputable def bsplineDeg0 (j : ℕ) (τ : ℝ) : ℝ :=
  if (splineKnot j ≤ τ ∧ τ < splineKnot (j + 1)) ∨ (j = 34 ∧ τ = 1) then 1 else 0

/-- B-splines of degree `p` on the knots `splineKnot`, by the Cox–de Boor recursion
`N_{j,p}(τ) = (τ − t_j)/(t_{j+p} − t_j) N_{j,p−1}(τ) + (t_{j+p+1} − τ)/(t_{j+p+1} − t_{j+1})
N_{j+1,p−1}(τ)`, with the convention `0/0 = 0` (Lean's `x / 0 = 0`). -/
noncomputable def bsplineBasis : ℕ → ℕ → ℝ → ℝ
  | 0, j, τ => bsplineDeg0 j τ
  | p + 1, j, τ =>
      (τ - splineKnot j) / (splineKnot (j + p + 1) - splineKnot j) * bsplineBasis p j τ +
        (splineKnot (j + p + 2) - τ) / (splineKnot (j + p + 2) - splineKnot (j + 1)) *
          bsplineBasis p (j + 1) τ

/-- The clamped uniform cubic B-spline `N_l`, `0 ≤ l ≤ 34`, on `[0, 1]` with knots
`(0, 0, 0, 0, 1/32, …, 31/32, 1, 1, 1, 1)` (Definition 5.2, p.31). -/
noncomputable def bspline (l : ℕ) (τ : ℝ) : ℝ := bsplineBasis 3 l τ

/-- The Bernstein polynomial `𝓑^d_i(x) = (d choose i) xⁱ (1 − x)^{d−i}` (Definition 5.2,
p.31). -/
noncomputable def bernstein (d i : ℕ) (x : ℝ) : ℝ := (d.choose i : ℝ) * x ^ i * (1 - x) ^ (d - i)

/-- `V(γ, a, b) = Σ_{i,j,l} V_{ijl} 𝓑¹¹ᵢ(a) 𝓑¹¹ⱼ(b) N_l(τ)`, `τ = 2γ/π` (Definition 5.2,
p.31). -/
noncomputable def familyV (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (γ a b : ℝ) : ℝ :=
  ∑ i : Fin 12, ∑ j : Fin 12, ∑ l : Fin 35,
    (V i j l : ℝ) * bernstein 11 i a * bernstein 11 j b * bspline l (2 * γ / Real.pi)

/-- `R(γ, a, b) = Σ_{i,j,l} R_{ijl} 𝓑⁵ᵢ(a) 𝓑⁵ⱼ(b) N_l(τ)` (Definition 5.2, p.31). -/
noncomputable def familyR (R : Fin 6 → Fin 6 → Fin 35 → ℚ) (γ a b : ℝ) : ℝ :=
  ∑ i : Fin 6, ∑ j : Fin 6, ∑ l : Fin 35,
    (R i j l : ℝ) * bernstein 5 i a * bernstein 5 j b * bspline l (2 * γ / Real.pi)

/-- `B(γ) = Σ_l B_l N_l(τ)`, and likewise `D(γ)` (Definition 5.2, p.31). -/
noncomputable def familySpline (c : Fin 35 → ℚ) (γ : ℝ) : ℝ :=
  ∑ l : Fin 35, (c l : ℝ) * bspline l (2 * γ / Real.pi)

/-- The right-hand side of (5.2) for `γ ≥ 0` (Definition 5.2, p.32): with
`a = (θ − φ + γ)/(π + 2γ)`, `b = (θ + φ − γ)/(π − 2γ)`, `k(γ) = π/2 − cos γ`, `ξ = ψ/k(γ)`,
`ξ̂ = clip₁(ξ)` and `σ(γ) = γ − cos²γ V(γ, 0, 1)`,
`cos²γ V(γ, a, b) + σ(γ) ξ̂ + cos²γ[(B(γ) + R(γ, a, b))(ξ̂ − ξ̂³) + D(γ)(ξ̂³ − ξ̂⁵)]`. -/
noncomputable def familyHPos (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (γ φ θ ψ : ℝ) : ℝ :=
  let a := (θ - φ + γ) / (Real.pi + 2 * γ)
  let b := (θ + φ - γ) / (Real.pi - 2 * γ)
  let ξ := ψ / (Real.pi / 2 - Real.cos γ)
  let ξh := clip 1 ξ
  let σ := γ - Real.cos γ ^ 2 * familyV V γ 0 1
  Real.cos γ ^ 2 * familyV V γ a b + σ * ξh +
    Real.cos γ ^ 2 * ((familySpline Bc γ + familyR R γ a b) * (ξh - ξh ^ 3) +
      familySpline Dc γ * (ξh ^ 3 - ξh ^ 5))

/-- The function `H` of Definition 5.2 built from the coefficients `V, R, B, D`: (5.2) for
`γ ≥ 0`, and `H(γ, φ, θ, ψ) = H(−γ, −φ, θ, −ψ)` for `γ < 0` (p.32). -/
noncomputable def familyH (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (z : R4) : ℝ :=
  if 0 ≤ z.1 then familyHPos V R Bc Dc z.1 z.2.1 z.2.2.1 z.2.2.2
  else familyHPos V R Bc Dc (-z.1) (-z.2.1) z.2.2.1 (-z.2.2.2)

/-- The coefficient conditions (5.3) and (5.4) (Definition 5.2, p.32):
`V_{11−i,11−j,l} = −V_{ijl}`, `R_{5−i,5−j,l} = R_{ijl}`, `R_{ijl} = 0` for `(i, j) ∈ {0, 5}²`,
`V_{ij0} = V_{ji0}`, `R_{ij0} = −R_{ji0}`, `B₀ = D₀ = 0`. -/
def FamilyCoeffConditions (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) : Prop :=
  (∀ i j l, V (Fin.rev i) (Fin.rev j) l = -V i j l) ∧
  (∀ i j l, R (Fin.rev i) (Fin.rev j) l = R i j l) ∧
  (∀ i j l, (i = 0 ∨ i = 5) → (j = 0 ∨ j = 5) → R i j l = 0) ∧
  (∀ i j, V i j 0 = V j i 0) ∧
  (∀ i j, R i j 0 = -R j i 0) ∧
  Bc 0 = 0 ∧ Dc 0 = 0

/-- **The family `𝓗`** (Definition 5.2, pp.31–32): `H ∈ 𝓗` if `H` is obtained by (5.2) (and
the reflection for `γ < 0`) from rational coefficients `V_{ijl}` (`0 ≤ i, j ≤ 11`), `R_{ijl}`
(`0 ≤ i, j ≤ 5`), `B_l`, `D_l` (`0 ≤ l ≤ 34`) satisfying (5.3) and (5.4).

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026),
Definition 5.2, pp.31–32.

**Formalization Note** `N₀, …, N₃₄` are defined by the Cox–de Boor recursion on the knot vector
`(0, 0, 0, 0, 1/32, …, 31/32, 1, 1, 1, 1)`, with the last interval closed so that they sum to
`1` on all of `[0, 1]`. The positions `a`, `b` are the closed-form solution (5.5) of (5.1)
(Lemma 5.3, p.32), which is the unique solution on `Ω`. `H` is a total function on `ℝ⁴`; its
values off `Ω × ℝ` (where (5.5) may divide by `0`) are never read by the conditions (H0)–(H4).
Membership asks `H = familyH …` on `Ω × ℝ`, the domain of the functions of `𝓗`. -/
def InFamilyH (H : R4 → ℝ) : Prop :=
  ∃ (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ) (Bc Dc : Fin 35 → ℚ),
    FamilyCoeffConditions V R Bc Dc ∧ ∀ z ∈ OmegaTimesR, H z = familyH V R Bc Dc z

end DelaunayStretch


