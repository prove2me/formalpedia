-- Prove2me | Definitions.Def_penrose_energy
-- name    : penrose_energy
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-18T18:19:53.099045+00:00
-- url     : https://prove2.me/theorems/a042036e-22fd-4094-88f1-a697b6e5dca0
-- title:
--   Gravitational self-energy and interaction energy of mass distributions
-- statement:
--   This bundle introduces the two gravitational energy functionals of the mission.
--
--   Given a real gravitational constant $G$, the **gravitational self-energy** of a smooth, rapidly decreasing mass distribution $\sigma$ on three-dimensional Euclidean space is
--
--   $$E(\sigma) = -\frac{G}{2} \iint_{\mathbb{R}^3\times\mathbb{R}^3} \frac{\sigma(x)\,\sigma(y)}{\|x-y\|}\,dx\,dy,$$
--
--   and the **gravitational interaction energy** between two mass distributions $\rho, \rho'$ is
--
--   $$I(\rho,\rho') = -G \iint_{\mathbb{R}^3\times\mathbb{R}^3} \frac{\rho(x)\,\rho'(y)}{\|x-y\|}\,dx\,dy.$$
--
--   The signs are the standard physics convention: gravity is attractive, so the binding energy of a positive mass distribution is negative. The self-energy of the difference $\sigma = \rho - \rho'$ of the two superposed mass distributions is the quantity Penrose identifies, up to the explicit constant $-8\pi G$, with his measure of incompatibility $\Delta$; the interaction energy appears in his remark that, when the two individual states have equal gravitational self-energies, either expression determines the scale of the energy uncertainty (Penrose 1996, Section 6, pp. 595–597).
--
--   **Formalization Note** The distributions are elements of Mathlib's Schwartz space over Euclidean three-space; the double integrals are nested Bochner integrals, the inner one over $y$, the outer one over $x$, both with respect to the standard volume.
-- source:
--   Penrose 1996, On Gravity's Role in Quantum State Reduction, General Relativity and Gravitation 28(5):581-600, https://doi.org/10.1007/BF02105068, Section 6, pp. 595-597 (gravitational self-energy of the difference; gravitational interaction energy); survey: https://en.wikipedia.org/wiki/Penrose_interpretation

import Mathlib

open MeasureTheory

namespace Penrose

/-- The gravitational self-energy of a Schwartz mass distribution: minus G/2
times the double integral of the product of the density at x and the density
at y, divided by their distance. -/
noncomputable def gravSelfEnergy (G : ℝ) (σ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ) : ℝ :=
  -(G / 2) * ∫ x, ∫ y, ⇑σ x * ⇑σ y / ‖x - y‖ ∂volume ∂volume

/-- The gravitational interaction energy between two Schwartz mass
distributions: minus G times the double integral of the first density at x
times the second density at y, divided by their distance. -/
noncomputable def interactionEnergy (G : ℝ)
    (ρ ρ' : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ) : ℝ :=
  -G * ∫ x, ∫ y, ⇑ρ x * ⇑ρ' y / ‖x - y‖ ∂volume ∂volume

end Penrose


