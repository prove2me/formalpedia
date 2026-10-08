-- Prove2me | Definitions.Def_CosmoConstCentury_Defs
-- name    : CosmoConstCentury_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-04T23:16:11.807799+00:00
-- url     : https://prove2.me/theorems/35e32286-7d93-4aed-890f-f82689bf457b
-- title:
--   Friedmann–Lemaître dust equations, Hubble and deceleration parameters, critical density, density parameters, Laplacian on $\mathbb R^3$
-- statement:
--   This definition file fixes the notation of the review for the whole mission.
--
--   1. **Einstein's constant** $\kappa = \dfrac{8\pi G}{c^2}$.
--   2. **Friedmann–Lemaître dust solution.** Given constants $G$, $c$, $\Lambda$, a curvature index $k$, a set of times $I\subseteq\mathbb R$, a scale factor $R$ and a density $\rho$, the pair $(R,\rho)$ is a solution on $I$ if for every $t\in I$: $R(t)>0$, $R$ is twice continuously differentiable near $t$, and
--   $$\frac{3R'(t)^2}{R(t)^2}+\frac{3kc^2}{R(t)^2}-\Lambda=\kappa c^2\rho(t),\qquad \frac{R'(t)^2}{R(t)^2}+\frac{2R''(t)}{R(t)}+\frac{kc^2}{R(t)^2}-\Lambda=0 .$$
--   For $k=1$ these are the review's equations (15) and (16).
--   3. **Hubble parameter** $H(t)=R'(t)/R(t)$.
--   4. **Deceleration parameter** (eq. 26) $q(t)=-\dfrac{1}{H(t)^2}\dfrac{R''(t)}{R(t)}$.
--   5. **Critical density** $\rho_c(H)=\dfrac{3H^2}{8\pi G}$ (Section 5.1).
--   6. **Density parameters** $\Omega_M(t)=\rho(t)/\rho_c(H(t))$ and $\Omega_\Lambda(t)=\Lambda/(3H(t)^2)$ (Section 5.1).
--   7. **Laplacian** on Euclidean three-space: $\nabla^2\Phi=\partial_1^2\Phi+\partial_2^2\Phi+\partial_3^2\Phi$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Derivatives are Lean's `deriv`; the Laplacian is written with iterated Fréchet derivatives along the standard basis vectors. Lean's division returns $0$ on a zero denominator, so expressions such as $q$ or $\Omega_M$ carry junk values when $H=0$ or $G=0$; the theorems exclude these cases where they matter.
-- source:
--   C. O'Raifeartaigh, M. O'Keeffe, W. Nahm, S. Mitton, "One hundred years of the cosmological constant: from 'superfluous stunt' to dark energy", Eur. Phys. J. H 43, 73-117 (2018), https://doi.org/10.1140/epjh/e2017-80061-7; eqs. (15), (16) p. 82; eq. (26) p. 92; critical density and density parameters, Section 5.1 p. 85; Laplacian in eqs. (3), (4), (11).

import Mathlib

/-!
Definitions for the mission "One Hundred Years of the Cosmological Constant"
(O'Raifeartaigh, O'Keeffe, Nahm, Mitton, Eur. Phys. J. H 43, 73–117 (2018)).

All cosmological quantities follow the paper's own conventions: the scale factor
(radius of the cosmos) is `R`, the mean matter density is `ρ`, the cosmological constant
is `Λ` (the paper's `λ`), `c` is the speed of light, `G` is Newton's constant and
`κ = 8πG/c²` is Einstein's constant.
-/

namespace CosmoConstCentury

/-- Einstein's constant `κ = 8πG/c²` (the paper's convention: eq. (18) together with
`ρ_c = 3H₀²/(8πG)` forces `κ c² = 8πG`). -/
noncomputable def einsteinKappa (G c : ℝ) : ℝ := 8 * Real.pi * G / c ^ 2

/-- The Friedmann–Lemaître equations for a pressure-free (dust) universe with curvature
index `k`, cosmological constant `Λ`, scale factor `R` and matter density `ρ`, holding at
every time `t` of the time set `I`. For `k = 1` these are exactly the paper's equations
(15) and (16):

* (15) `3 R'²/R² + 3 k c²/R² − Λ = κ c² ρ`,
* (16) `R'²/R² + 2 R''/R + k c²/R² − Λ = 0`,

together with the requirement that `R` is positive and twice continuously differentiable
near every `t ∈ I`. Derivatives are with respect to the time `t`. -/
def IsFriedmannSolution (G c Λ k : ℝ) (I : Set ℝ) (R ρ : ℝ → ℝ) : Prop :=
  ∀ t ∈ I, 0 < R t ∧ ContDiffAt ℝ 2 R t ∧
    3 * deriv R t ^ 2 / R t ^ 2 + 3 * k * c ^ 2 / R t ^ 2 - Λ
        = einsteinKappa G c * c ^ 2 * ρ t ∧
    deriv R t ^ 2 / R t ^ 2 + 2 * deriv (deriv R) t / R t + k * c ^ 2 / R t ^ 2 - Λ = 0

/-- The Hubble parameter `H(t) = R'(t)/R(t)`. -/
noncomputable def hubbleParam (R : ℝ → ℝ) (t : ℝ) : ℝ := deriv R t / R t

/-- The deceleration parameter, eq. (26): `q = −(1/H²)·(R''/R)`. -/
noncomputable def decelParam (R : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(1 / hubbleParam R t ^ 2) * (deriv (deriv R) t / R t)

/-- The critical density `ρ_c = 3H²/(8πG)` (Section 5, from eq. (18)). -/
noncomputable def criticalDensity (G H : ℝ) : ℝ := 3 * H ^ 2 / (8 * Real.pi * G)

/-- The matter density parameter `Ω_M = ρ/ρ_c = (8πG/(3H²))·ρ` at time `t`. -/
noncomputable def omegaMatter (G : ℝ) (R ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ρ t / criticalDensity G (hubbleParam R t)

/-- The cosmological-constant density parameter `Ω_Λ = Λ/(3H²)` at time `t`. -/
noncomputable def omegaLambda (Λ : ℝ) (R : ℝ → ℝ) (t : ℝ) : ℝ :=
  Λ / (3 * hubbleParam R t ^ 2)

/-- The Laplacian `∇²Φ = ∂²Φ/∂x₁² + ∂²Φ/∂x₂² + ∂²Φ/∂x₃²` of a function on Euclidean
three-space, written with iterated Fréchet derivatives along the standard basis. -/
noncomputable def laplacian3 (Φ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ Φ y (EuclideanSpace.single i 1)) x
    (EuclideanSpace.single i 1)

end CosmoConstCentury


