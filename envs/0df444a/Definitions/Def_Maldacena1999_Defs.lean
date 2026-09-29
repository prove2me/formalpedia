-- Prove2me | Definitions.Def_Maldacena1999_Defs
-- name    : Maldacena1999_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T17:03:22.099593+00:00
-- url     : https://prove2.me/theorems/2a842945-2250-4124-ac83-17981a7c2f7f
-- title:
--   Maldacena (1999): AdS hyperboloid, Poincaré coordinates, D3-brane metric
-- statement:
--   This file fixes the objects used by every statement of the mission.
--
--   1. **Ambient space.** $\mathbb R^{2,p+1}$ with coordinates $X_{-1},X_0,X_1,\dots,X_p,X_{p+1}$ and flat metric $\eta=\mathrm{diag}(-1,-1,1,\dots,1)$; the quadratic form is
--   $$\langle X,X\rangle_\eta=-X_{-1}^2-X_0^2+X_1^2+\cdots+X_p^2+X_{p+1}^2 .$$
--   2. **Anti-de Sitter space** $\mathrm{AdS}_{p+2}$ of "radius" $R$ is the hyperboloid (eq. (A.1))
--   $$\mathrm{AdS}_{p+2}(R)=\{X\in\mathbb R^{2,p+1} : \langle X,X\rangle_\eta=-R^2\}.$$
--   3. **Worldvolume Minkowski form** on $\mathbb R^{1,p}$: $x^2=-x_0^2+x_1^2+\cdots+x_p^2$.
--   4. **Poincaré coordinates** (eq. (A.2)): for $U\neq 0$ and $x\in\mathbb R^{1,p}$ put $V=x^2U/R^2+R^2/U$ and
--   $$X_{-1}=\tfrac{U+V}{2},\qquad X_{p+1}=\tfrac{U-V}{2},\qquad X_\alpha=\frac{x_\alpha U}{R}\quad(\alpha=0,\dots,p),$$
--   so that $U=X_{-1}+X_{p+1}$, $V=X_{-1}-X_{p+1}$ and $x_\alpha=X_\alpha R/U$.
--   5. **D3-brane harmonic function** (eq. (2.2)): $f(r)=1+\dfrac{4\pi gN\alpha'^2}{r^4}$ for string coupling $g$, number of branes $N$ and string scale $\alpha'$.
--   6. **D3-brane metric** (eq. (2.2)): at radius $r$, on a tangent vector with worldvolume part $\delta x\in\mathbb R^{1,3}$, radial part $\delta r$ and five-sphere part $\delta\omega$,
--   $$ds^2=f^{-1/2}\,\delta x^2+f^{1/2}\big(\delta r^2+r^2\,\|\delta\omega\|^2\big),$$
--   where $\|\delta\omega\|^2$ is the round metric $d\Omega_5^2$ of the unit five-sphere $S^5\subset\mathbb R^6$ evaluated on the tangent vector $\delta\omega$.
--
--   These are the objects whose relations (the near-horizon limit and the geometry of AdS) are the content of the mission.
--
--   **Formalization Note** Coordinates of $\mathbb R^{2,p+1}$ are indexed by $\{0,\dots,p+2\}$: index $0$ is $X_{-1}$, index $1$ is $X_0$ and index $k+1$ is $X_k$. Worldvolume coordinates are indexed by $\{0,\dots,p\}$ with index $0$ timelike. Division and square roots are Lean's total versions; every theorem restricts to $U>0$, $R>0$, $g>0$, $N\ge1$, where no junk value occurs.
-- source:
--   J. Maldacena, The Large-N Limit of Superconformal Field Theories and Supergravity, Int. J. Theor. Phys. 38 (1999) 1113-1133, https://doi.org/10.1023/A:1026654312961 (arXiv:hep-th/9711200), Section 2, eqs. (2.2)-(2.3); Appendix, eqs. (A.1)-(A.3)

import Mathlib

/-!
# Maldacena (1999): definitions

Definitions for the geometric statements of
J. Maldacena, *The Large-N Limit of Superconformal Field Theories and Supergravity*,
Int. J. Theor. Phys. 38 (1999) 1113–1133, Section 2 and the Appendix.
-/

namespace Maldacena1999

open scoped BigOperators

/-- Signature of the flat ambient space `ℝ^{2,p+1}` of the Appendix, eq. (A.1), with metric
`η = diag(-1,-1,1,…,1)`.  Coordinates are indexed by `Fin (p+3)`:
index `0` is `X_{-1}`, index `1` is `X_0`, and index `k+1` is `X_k` for `k = 1, …, p+1`. -/
def ambientSign (p : ℕ) (i : Fin (p + 3)) : ℝ :=
  if i.val < 2 then -1 else 1

/-- The ambient quadratic form `-X_{-1}² - X_0² + X_1² + ⋯ + X_p² + X_{p+1}²` on `ℝ^{2,p+1}`. -/
def ambientForm (p : ℕ) (X : Fin (p + 3) → ℝ) : ℝ :=
  ∑ i, ambientSign p i * X i ^ 2

/-- The anti-de Sitter hyperboloid `AdS_{p+2}` of "radius" `R`, eq. (A.1):
`-X_{-1}² - X_0² + X_1² + ⋯ + X_p² + X_{p+1}² = -R²`. -/
def AdS (p : ℕ) (R : ℝ) : Set (Fin (p + 3) → ℝ) :=
  {X | ambientForm p X = -R ^ 2}

/-- The Minkowski quadratic form `x² = -x_0² + x_1² + ⋯ + x_p²` on the brane worldvolume
`ℝ^{1,p}` (coordinates indexed by `Fin (p+1)`, index `0` is time). -/
def minkowskiForm (p : ℕ) (x : Fin (p + 1) → ℝ) : ℝ :=
  ∑ a, (if a.val = 0 then (-1 : ℝ) else 1) * x a ^ 2

/-- The Poincaré coordinates of the Appendix, eq. (A.2), written as a map
`(U, x) ↦ X` into `ℝ^{2,p+1}`:
`X_{-1} = (U + V)/2`, `X_{p+1} = (U - V)/2`, `X_α = x_α U / R` (`α = 0, …, p`),
where `V = x² U / R² + R² / U`.  Equivalently `U = X_{-1} + X_{p+1}`,
`V = X_{-1} - X_{p+1}`, `x_α = X_α R / U`. -/
noncomputable def poincareEmbedding (p : ℕ) (R : ℝ) (q : ℝ × (Fin (p + 1) → ℝ)) :
    Fin (p + 3) → ℝ :=
  fun i =>
    if i.val = 0 then
      (q.1 + (minkowskiForm p q.2 * q.1 / R ^ 2 + R ^ 2 / q.1)) / 2
    else if h : i.val ≤ p + 1 then
      q.2 ⟨i.val - 1, by omega⟩ * q.1 / R
    else
      (q.1 - (minkowskiForm p q.2 * q.1 / R ^ 2 + R ^ 2 / q.1)) / 2

/-- The harmonic function of the D3-brane supergravity solution, eq. (2.2):
`f(r) = 1 + 4π g N α'² / r⁴`. -/
noncomputable def harmonicFn (g : ℝ) (N : ℕ) (α' r : ℝ) : ℝ :=
  1 + 4 * Real.pi * g * N * α' ^ 2 / r ^ 4

/-- The D3-brane metric of eq. (2.2),
`ds² = f^{-1/2} dx_∥² + f^{1/2} (dr² + r² dΩ₅²)`,
evaluated at radial position `r` on a tangent vector with worldvolume component `δx`,
radial component `δr`, and five-sphere component `δω`; the round metric `dΩ₅²` of the unit
five-sphere is the Euclidean squared norm `‖δω‖²` of a vector tangent to the unit sphere
in `ℝ⁶`. -/
noncomputable def d3Metric (g : ℝ) (N : ℕ) (α' r : ℝ) (δx : Fin 4 → ℝ) (δr : ℝ)
    (δω : EuclideanSpace ℝ (Fin 6)) : ℝ :=
  minkowskiForm 3 δx / Real.sqrt (harmonicFn g N α' r) +
    Real.sqrt (harmonicFn g N α' r) * (δr ^ 2 + r ^ 2 * ‖δω‖ ^ 2)

end Maldacena1999


