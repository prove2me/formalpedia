-- Prove2me | Definitions.Def_ChatterjeeQFT_MassShell
-- name    : ChatterjeeQFT_MassShell
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T20:43:13.186745+00:00
-- url     : https://prove2.me/theorems/dc5b3a9c-776d-467d-9627-cf743687ee7e
-- title:
--   Mass shell $X_m$, the invariant measure $\lambda_m$, and the boson space $L^2(X_m, d\lambda_m)$
-- statement:
--   For a mass $m$, the **mass shell** is the set of admissible four-momenta
--
--   $$X_m \;=\; \{\, p \in \mathbb{R}^{1,3} \;:\; p^2 = m^2, \; p^0 \ge 0 \,\},$$
--
--   with $p^2 = (p,p)$ the Minkowski square. Writing $\omega_q = \sqrt{m^2 + |q|^2}$ for the
--   relativistic energy of a three-momentum $q \in \mathbb{R}^3$, the map $q \mapsto (\omega_q, q)$
--   parametrises $X_m$ by $\mathbb{R}^3$.
--
--   The **Lorentz-invariant measure** $\lambda_m$ on $X_m$ is defined, as in eq. (10.1) of the
--   source, by transporting the weighted Lebesgue measure $d^3q / ((2\pi)^3 \, 2\omega_q)$ along this
--   parametrisation, so that for integrable $f$,
--
--   $$\int_{X_m} f \, d\lambda_m \;=\; \int_{\mathbb{R}^3} \frac{d^3 q}{(2\pi)^3 \, 2\omega_q} \, f(\omega_q, q).$$
--
--   Here $\lambda_m$ is realised as a Borel measure on all of $\mathbb{R}^{1,3}$ that is carried by
--   $X_m$. The **one-particle Hilbert space of a massive scalar boson** is then
--   $\mathcal{H} = L^2(X_m, d\lambda_m)$, the complex $L^2$ space of that measure, and the Poincaré
--   group acts on wave functions by
--
--   $$(U(a, L)\psi)(p) \;=\; e^{i(a,p)} \, \psi(L^{-1} p), \qquad a \in \mathbb{R}^{1,3}, \; L \in SO^{\uparrow}(1,3).$$
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 9 §9.5 p. 40 (mass shell), Lecture 10 §10.1-§10.2 pp. 41-42 (Hilbert space and the measure, eq. (10.1)), Lecture 11 §11.3 p. 45 (the representation).

import Mathlib
import Definitions.Def_ChatterjeeQFT_Minkowski

/-!
# The mass shell, the Lorentz-invariant measure, and the one-particle boson space

Following S. Chatterjee, *Lectures on Quantum Field Theory*, Lectures 9-11.
-/

open MeasureTheory Matrix

namespace ChatterjeeQFT

/-- The relativistic energy `ω_q = √(m² + |q|²)` of a three-momentum `q`. -/
noncomputable def omega (m : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (m ^ 2 + (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2))

/-- The parametrisation of the mass shell by three-momentum: `q ↦ (ω_q, q)`. -/
noncomputable def massShellEmb (m : ℝ) (q : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![omega m q, q 0, q 1, q 2]

/-- The mass shell `X_m = {p ∈ R^{1,3} : p² = m², p⁰ ≥ 0}`. -/
def massShell (m : ℝ) : Set (Fin 4 → ℝ) :=
  {p | minkowskiSq p = m ^ 2 ∧ 0 ≤ p 0}

/-- The Lorentz-invariant measure `λ_m` on the mass shell `X_m`, viewed as a Borel measure on
`R^{1,3}` carried by `X_m`.  It is the push-forward under `q ↦ (ω_q, q)` of the measure
`d³q / ((2π)³ 2ω_q)` on `R³`, so that
`∫_{X_m} f dλ_m = ∫_{R³} f(ω_q, q) d³q / ((2π)³ 2ω_q)`. -/
noncomputable def massShellMeasure (m : ℝ) : Measure (Fin 4 → ℝ) :=
  Measure.map (massShellEmb m)
    ((volume : Measure (Fin 3 → ℝ)).withDensity fun q =>
      ENNReal.ofReal (1 / ((2 * Real.pi) ^ 3 * (2 * omega m q))))

/-- The one-particle Hilbert space of a massive scalar boson of mass `m`:
`H = L²(X_m, dλ_m)`. -/
noncomputable abbrev bosonSpace (m : ℝ) : Type := Lp ℂ 2 (massShellMeasure m)

/-- The Poincaré action on scalar wave functions on the mass shell:
`(U(a, L)ψ)(p) = e^{i(a,p)} ψ(L⁻¹p)`. -/
noncomputable def bosonAction (a : Fin 4 → ℝ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (ψ : (Fin 4 → ℝ) → ℂ) : (Fin 4 → ℝ) → ℂ :=
  fun p => Complex.exp (Complex.I * (minkowskiInner a p : ℂ)) * ψ (L⁻¹ *ᵥ p)

end ChatterjeeQFT


