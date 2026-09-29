-- Prove2me | Definitions.Def_DiracEquation_fields
-- name    : DiracEquation_fields
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T19:40:21.223717+00:00
-- url     : https://prove2.me/theorems/035a4075-f5d1-48c8-866d-dd7771e9572b
-- title:
--   Spinor fields on $\mathbb{R}^4$: partial derivatives, the Dirac equation, the Klein--Gordon equation and plane waves
-- statement:
--   The differential layer of the Dirac equation, built on the algebraic layer.
--
--   A **Dirac spinor field** is a map $\psi : \mathbb{R}^4 \to \mathbb{C}^4$ on Minkowski spacetime
--   with coordinates $x = (x^0,x^1,x^2,x^3)$. Its partial derivatives $\partial_\mu\psi$ are taken
--   coordinatewise in the $\mu$-th coordinate direction, and $\partial_\nu\partial_\mu\psi$ denotes
--   the derivative in the direction $\nu$ of the field $\partial_\mu\psi$.
--
--   In natural units $\hbar = c = 1$ and for a real mass $m$, the field $\psi$ **solves the Dirac
--   equation** for a family of gamma matrices $\gamma$ when
--
--   $$\bigl(i\gamma^\mu\partial_\mu - m\bigr)\psi(x) = 0 \qquad\text{for every } x \in \mathbb{R}^4,$$
--
--   with the repeated index $\mu$ summed over $0,1,2,3$ and each $\gamma^\mu$ acting on the spinor by
--   matrix-vector multiplication. It **solves the Klein--Gordon equation** when
--
--   $$\bigl(\partial_\mu\partial^\mu + m^2\bigr)\psi(x) = 0 \qquad\text{for every } x \in \mathbb{R}^4,
--   \qquad \partial_\mu\partial^\mu = \eta^{\mu\nu}\partial_\mu\partial_\nu
--   = \partial_0^2 - \partial_1^2 - \partial_2^2 - \partial_3^2 .$$
--
--   Finally, for a real covector $p = (p_\mu)$ and a constant polarization $u \in \mathbb{C}^4$, the
--   **positive-frequency plane wave** is the field
--
--   $$\psi(x) = u\, e^{i p_\mu x^\mu}, \qquad p_\mu x^\mu = \sum_{\mu=0}^{3} p_\mu x^\mu .$$
--
--   Together with the algebraic layer these definitions are what the goal theorem and the milestones
--   of the mission are stated in, and they are meant to be reused for the adjoint equation, the
--   conserved current and the non-relativistic limit.
--
--   **Formalization Note.** A partial derivative is the Fréchet derivative over $\mathbb{R}$ of the
--   field, evaluated on the standard basis vector of the $\mu$-th coordinate; no differentiability is
--   assumed in the definitions themselves, so the differentiability hypotheses appear on the
--   theorems that use them. The equations are imposed pointwise, at every point of $\mathbb{R}^4$,
--   with no decay, integrability or normalisation condition on $\psi$. Momentum components carry a
--   lower index and the phase of the plane wave is the plain sum $\sum_\mu p_\mu x^\mu$, with no
--   metric inserted.
-- source:
--   "Dirac equation", Wikipedia, https://en.wikipedia.org/wiki/Dirac_equation, sections "Formulation - Covariant formulation" (Dirac equation, Clifford relation {gamma^mu, gamma^nu} = 2 eta^{mu nu} I_4, Dirac representation of the gamma matrices, Hamiltonian form with alpha and beta) and "Properties - Plane wave solutions" (Klein-Gordon reduction, plane waves, momentum-space Dirac equation).

import Definitions.Def_DiracAlgebra_core

namespace DiracEquation

open Matrix

/-- The partial derivative `∂_μ ψ` of a four-component spinor field on `ℝ⁴`, taken in the
direction of the `μ`-th coordinate axis. -/
noncomputable def pd (psi : (Fin 4 → ℝ) → (Fin 4 → ℂ)) (mu : Fin 4) (x : Fin 4 → ℝ) :
    Fin 4 → ℂ :=
  fderiv ℝ psi x (Pi.single mu 1)

/-- The second partial derivative `∂_ν ∂_μ ψ`. -/
noncomputable def pd2 (psi : (Fin 4 → ℝ) → (Fin 4 → ℂ)) (mu nu : Fin 4) (x : Fin 4 → ℝ) :
    Fin 4 → ℂ :=
  pd (fun y => pd psi mu y) nu x

/-- `IsDiracSolution g m ψ` says that `ψ` satisfies the Dirac equation `(i γ^μ ∂_μ - m) ψ = 0`
for the gamma matrices `g` and mass `m`, in natural units `ħ = c = 1`. -/
def IsDiracSolution (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (m : ℝ)
    (psi : (Fin 4 → ℝ) → (Fin 4 → ℂ)) : Prop :=
  ∀ x, ∑ mu, Complex.I • (g mu).mulVec (pd psi mu x) = (m : ℂ) • psi x

/-- `IsKleinGordonSolution m ψ` says that every component of `ψ` satisfies the Klein–Gordon
equation `(∂_μ ∂^μ + m²) ψ = 0`, where `∂_μ ∂^μ = η^{μν} ∂_μ ∂_ν`. -/
def IsKleinGordonSolution (m : ℝ) (psi : (Fin 4 → ℝ) → (Fin 4 → ℂ)) : Prop :=
  ∀ x, (∑ mu, eta mu mu • pd2 psi mu mu x) + ((m : ℂ) ^ 2) • psi x = 0

/-- The positive-frequency plane wave `ψ(x) = u e^{i p_μ x^μ}` with polarization `u`. -/
noncomputable def planeWave (p : Fin 4 → ℝ) (u : Fin 4 → ℂ) : (Fin 4 → ℝ) → (Fin 4 → ℂ) :=
  fun x => Complex.exp (Complex.I * ∑ mu, (p mu : ℂ) * (x mu : ℂ)) • u

end DiracEquation


