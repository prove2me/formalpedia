-- Prove2me | Definitions.Def_penrose
-- name    : penrose
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-18T18:19:41.855984+00:00
-- url     : https://prove2.me/theorems/b79f116e-c3bd-432d-8909-3fbbbc4c953e
-- title:
--   Newtonian potential, field gradient, Laplacian, and Penrose's incompatibility measure
-- statement:
--   This bundle introduces the Newtonian-gravity layer used by the mission.
--
--   Given a real number $G$ (the gravitational constant) and a smooth, rapidly decreasing mass density $\rho$ on three-dimensional Euclidean space $\mathbb{R}^3$, the **Newtonian gravitational potential** of $\rho$ is
--
--   $$\Phi_\rho(x) = G \int_{\mathbb{R}^3} \frac{\rho(y)}{\|x-y\|}\,dy.$$
--
--   Its gradient is defined by the explicit integral formula
--
--   $$\nabla\Phi_\rho(x) = -G \int_{\mathbb{R}^3} \frac{\rho(y)}{\|x-y\|^3}\,(x-y)\,dy,$$
--
--   so that the physical gravitational field $f = -\nabla\Phi$ pulls test masses towards the matter. For a function $f$ on $\mathbb{R}^3$, the **Laplacian** is defined as the trace of the second Fréchet derivative,
--
--   $$\nabla^2 f(x) = \sum_{i=1}^{3} D^2 f(x)(e_i, e_i),$$
--
--   the sum of the second directional derivatives along the standard orthonormal basis $e_1, e_2, e_3$. Finally, for two mass densities $\rho, \rho'$, **Penrose's measure of incompatibility** is the squared $L^2$ norm of the difference of the two field gradients,
--
--   $$\Delta(\rho,\rho') = \int_{\mathbb{R}^3} \|\nabla\Phi_\rho(x) - \nabla\Phi_{\rho'}(x)\|^2\,dx.$$
--
--   These are the objects of Section 6 of Penrose (1996): in the Newtonian limit, the two superposed space-time geometries are described by the two potentials $\Phi_\rho$ and $\Phi_{\rho'}$, and $\Delta$ measures the mismatch of their free-fall frames that Penrose argues makes the superposed state non-stationary.
--
--   **Formalization Note** The densities are elements of Mathlib's Schwartz space over Euclidean three-space, so smoothness and decay are carried by the type; all integrals are Bochner integrals with respect to the standard volume on $\mathbb{R}^3$.
-- source:
--   Penrose 1996, On Gravity's Role in Quantum State Reduction, General Relativity and Gravitation 28(5):581-600, https://doi.org/10.1007/BF02105068, Section 6, pp. 594-595 (potential, field, and the measure of incompatibility); survey: https://en.wikipedia.org/wiki/Penrose_interpretation

import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Penrose

/-- The Newtonian gravitational potential of a Schwartz mass density on
three-dimensional Euclidean space, with gravitational constant G:
the potential at x is G times the integral of the density at y divided by
the distance between x and y. -/
noncomputable def newtonianPotential (G : ℝ) (ρ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun x => G * ∫ y, ⇑ρ y / ‖x - y‖ ∂volume

/-- The gradient of the Newtonian gravitational potential: minus G times the
integral of the density at y divided by the third power of the distance,
in the direction of x - y. -/
noncomputable def potentialGradient (G : ℝ) (ρ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ) :
    EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
  fun x => -G • ∫ y, (⇑ρ y / ‖x - y‖ ^ 3) • (x - y) ∂volume

/-- The Laplacian of a real function on three-dimensional Euclidean space:
the sum, over the standard basis vectors, of the second directional
derivatives (the trace of the second Frechet derivative). -/
noncomputable def laplacian (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i, iteratedFDeriv ℝ 2 f x (fun _ => EuclideanSpace.single i 1)

/-- Penrose's measure of incompatibility of two mass densities: the squared
L2 norm of the difference of the gradients of their Newtonian potentials. -/
noncomputable def deltaMeasure (G : ℝ)
    (ρ ρ' : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ) : ℝ :=
  ∫ x, ‖potentialGradient G ρ x - potentialGradient G ρ' x‖ ^ 2 ∂volume

end Penrose


