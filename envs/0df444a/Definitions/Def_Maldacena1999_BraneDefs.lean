-- Prove2me | Definitions.Def_Maldacena1999_BraneDefs
-- name    : Maldacena1999_BraneDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T01:02:32.259061+00:00
-- url     : https://prove2.me/theorems/bfef2a58-90c9-497c-b9ad-135f16687e32
-- title:
--   Maldacena (1999): M5-, M2- and D1–D5-brane metrics, eqs. (3.1), (3.3), (4.2)
-- statement:
--   Supergravity metrics of the brane systems of Sections 3 and 4 of Maldacena (1999), each evaluated at a radial position $r$ on a tangent vector $(\delta x,\delta r,\delta\omega)$, where $\delta x$ is the worldvolume component (with Minkowski square $\delta x^2=-\delta x_0^2+\delta x_1^2+\cdots$), $\delta r$ the radial component, and $\delta\omega\in\mathbb R^{n+1}$ the sphere component, with $d\Omega_n^2=\|\delta\omega\|^2$.
--
--   1. **M5-branes**, eq. (3.1): $f(r)=1+\dfrac{\pi N l_p^3}{r^3}$ and
--   $$ds^2=f^{-1/3}\,\delta x^2+f^{2/3}\left(\delta r^2+r^2\|\delta\omega\|^2\right),\qquad \delta x\in\mathbb R^{1,5},\ \delta\omega\in\mathbb R^5.$$
--   2. **M2-branes**, eq. (3.3): $f(r)=1+\dfrac{2^5\pi^2 N l_p^6}{r^6}$ and
--   $$ds^2=f^{-2/3}\,\delta x^2+f^{1/3}\left(\delta r^2+r^2\|\delta\omega\|^2\right),\qquad \delta x\in\mathbb R^{1,2},\ \delta\omega\in\mathbb R^8.$$
--   3. **D1–D5 system**, eq. (4.2): $f_1(r)=1+\dfrac{g\alpha' Q_1}{v r^2}$, $f_5(r)=1+\dfrac{g\alpha' Q_5}{r^2}$ and
--   $$ds^2=f_1^{-1/2}f_5^{-1/2}\,\delta x^2+f_1^{1/2}f_5^{1/2}\left(\delta r^2+r^2\|\delta\omega\|^2\right),\qquad \delta x\in\mathbb R^{1,1},\ \delta\omega\in\mathbb R^4.$$
--
--   Here $N$ is the number of branes, $l_p$ the eleven-dimensional Planck length, $g$ the string coupling, $\alpha'$ the string length squared, $v=V_4/((2\pi)^4\alpha'^2)$ the volume of $M^4$ in string units, and $Q_1,Q_5$ the numbers of D1- and D5-branes. These metrics are the starting point of the near-horizon limits (3.2), the limit of (3.3), and (4.3).
--
--   **Formalization Note** The Minkowski form `minkowskiForm` is imported from the published definition file `Maldacena1999_Defs`. Fractional powers are real powers `Real.rpow` of the (positive) harmonic functions. $N,Q_1,Q_5$ are natural numbers. Only the six-dimensional part of the D1–D5 metric is modelled (the compact $M^4$ factor is omitted).
-- source:
--   J. Maldacena, The Large-N Limit of Superconformal Field Theories and Supergravity, Int. J. Theor. Phys. 38 (1999) 1113-1133, https://arxiv.org/abs/hep-th/9711200, pp. 1122-1124, eqs. (3.1), (3.3), (4.2)

import Mathlib
import Definitions.Def_Maldacena1999_Defs

/-!
# Maldacena (1999): brane metrics of Sections 3 and 4

Supergravity metrics of coincident M5-branes (eq. 3.1), M2-branes (eq. 3.3) and the
D1–D5 system (eq. 4.2) from
J. Maldacena, *The Large-N Limit of Superconformal Field Theories and Supergravity*,
Int. J. Theor. Phys. 38 (1999) 1113–1133 (hep-th/9711200).
The worldvolume Minkowski form `minkowskiForm` comes from `Maldacena1999_Defs`.
-/

namespace Maldacena1999

/-- Harmonic function of the M5-brane solution, eq. (3.1): `f(r) = 1 + π N l_p³ / r³`. -/
noncomputable def m5HarmonicFn (N : ℕ) (lp r : ℝ) : ℝ :=
  1 + Real.pi * N * lp ^ 3 / r ^ 3

/-- The M5-brane metric of eq. (3.1),
`ds² = f^{-1/3} dx_∥² + f^{2/3} (dr² + r² dΩ₄²)`,
evaluated at radial position `r` on a tangent vector with worldvolume component
`δx ∈ ℝ^{1,5}`, radial component `δr` and four-sphere component `δω ∈ ℝ⁵`; the round metric
`dΩ₄²` of the unit four-sphere is the Euclidean squared norm `‖δω‖²` of a vector tangent to
the unit sphere in `ℝ⁵`. -/
noncomputable def m5Metric (N : ℕ) (lp r : ℝ) (δx : Fin 6 → ℝ) (δr : ℝ)
    (δω : EuclideanSpace ℝ (Fin 5)) : ℝ :=
  m5HarmonicFn N lp r ^ (-(1 / 3 : ℝ)) * minkowskiForm 5 δx +
    m5HarmonicFn N lp r ^ (2 / 3 : ℝ) * (δr ^ 2 + r ^ 2 * ‖δω‖ ^ 2)

/-- Harmonic function of the M2-brane solution, eq. (3.3):
`f(r) = 1 + 2⁵ π² N l_p⁶ / r⁶`. -/
noncomputable def m2HarmonicFn (N : ℕ) (lp r : ℝ) : ℝ :=
  1 + 2 ^ 5 * Real.pi ^ 2 * N * lp ^ 6 / r ^ 6

/-- The M2-brane metric of eq. (3.3),
`ds² = f^{-2/3} dx_∥² + f^{1/3} (dr² + r² dΩ₇²)`,
evaluated at radial position `r` on a tangent vector with worldvolume component
`δx ∈ ℝ^{1,2}`, radial component `δr` and seven-sphere component `δω ∈ ℝ⁸`
(`dΩ₇² = ‖δω‖²` for `δω` tangent to the unit sphere in `ℝ⁸`). -/
noncomputable def m2Metric (N : ℕ) (lp r : ℝ) (δx : Fin 3 → ℝ) (δr : ℝ)
    (δω : EuclideanSpace ℝ (Fin 8)) : ℝ :=
  m2HarmonicFn N lp r ^ (-(2 / 3 : ℝ)) * minkowskiForm 2 δx +
    m2HarmonicFn N lp r ^ (1 / 3 : ℝ) * (δr ^ 2 + r ^ 2 * ‖δω‖ ^ 2)

/-- Harmonic function `f₁(r) = 1 + g α' Q₁ / (v r²)` of the D1–D5 solution, eq. (4.2). -/
noncomputable def d1HarmonicFn (g v : ℝ) (Q1 : ℕ) (α' r : ℝ) : ℝ :=
  1 + g * α' * Q1 / (v * r ^ 2)

/-- Harmonic function `f₅(r) = 1 + g α' Q₅ / r²` of the D1–D5 solution, eq. (4.2). -/
noncomputable def d5HarmonicFn (g : ℝ) (Q5 : ℕ) (α' r : ℝ) : ℝ :=
  1 + g * α' * Q5 / r ^ 2

/-- The six-dimensional D1–D5 metric of eq. (4.2),
`ds² = f₁^{-1/2} f₅^{-1/2} dx_∥² + f₁^{1/2} f₅^{1/2} (dr² + r² dΩ₃²)`,
evaluated at radial position `r` on a tangent vector with worldvolume component
`δx ∈ ℝ^{1,1}` (`dx_∥² = -dt² + dx²`), radial component `δr` and three-sphere component
`δω ∈ ℝ⁴` (`dΩ₃² = ‖δω‖²` for `δω` tangent to the unit sphere in `ℝ⁴`). -/
noncomputable def d1d5Metric (g v : ℝ) (Q1 Q5 : ℕ) (α' r : ℝ) (δx : Fin 2 → ℝ) (δr : ℝ)
    (δω : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  d1HarmonicFn g v Q1 α' r ^ (-(1 / 2 : ℝ)) * d5HarmonicFn g Q5 α' r ^ (-(1 / 2 : ℝ)) *
      minkowskiForm 1 δx +
    d1HarmonicFn g v Q1 α' r ^ (1 / 2 : ℝ) * d5HarmonicFn g Q5 α' r ^ (1 / 2 : ℝ) *
      (δr ^ 2 + r ^ 2 * ‖δω‖ ^ 2)

end Maldacena1999


