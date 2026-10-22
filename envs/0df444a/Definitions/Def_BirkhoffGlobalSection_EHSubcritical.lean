-- Prove2me | Definitions.Def_BirkhoffGlobalSection_EHSubcritical
-- name    : BirkhoffGlobalSection_EHSubcritical
-- status  : Definition
-- author  : @caleb
-- created : 2026-10-01T00:59:30.623995+00:00
-- url     : https://prove2.me/theorems/c06e2b90-fdca-40a6-9247-1b67722d108d
-- title:
--   Centered left elliptic-hyperbolic Hamiltonian and selected energy component
-- statement:
--   Use position-momentum coordinates $(x_1,x_2,y_1,y_2)$ and physical energy $h=-c$. Put
--
--   $$A=\cosh x_1,\qquad B=\cos x_2,\qquad D=A^2-B^2.$$
--
--   The regularized Hamiltonian centered at the left primary is
--
--   $$G_{\mu,c}=\frac12\left[\left(y_1+\frac{\sin 2x_2}{8}\right)^2+\left(y_2+\frac{\sinh 2x_1}{8}\right)^2\right]+\frac c4D-\frac A2-\frac{\sinh^2(2x_1)+\sin^2(2x_2)}{128}+(1-2\mu)\left[-\frac B2-\frac{(1/2-\mu-AB)D}{16}\right].$$
--
--   The selected surface is the connected component of the zero set through
--
--   $$b_\mu=(0,0,0,-\sqrt{2(1-\mu)}).$$
--
--   These definitions isolate the explicit geometry needed to compare the elliptic-hyperbolic and Levi-Civita regularizations. They assert no convexity or coordinate equivalence.
--
--   **Formalization Note.** This is the formula in Section 9.2 after translating the angular variable by $\pi$ to center the primary at $q=-\mu$, substituting $h=-c$, and placing positions before momenta. The component selection is a new interface for the platform's labeled Levi-Civita component.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S9.SS2, Section 9.2, displayed formulas for the elliptic-hyperbolic Hamiltonian and V, V-hat immediately before Section 9.3. Angular translation by pi and coordinate-order adaptation; connected-component selection is an explicit platform interface.

import Definitions.Def_BirkhoffGlobalSection_RegularizationModel

namespace BirkhoffGlobalSection

noncomputable section

/-- The elliptic-hyperbolic Hamiltonian of Liu--Salomao, Section 9.2,
with physical energy `h = -c` and angular coordinate translated by `pi`
to center the primary at `q = -mu`. The coordinate order is
`(x1, x2, y1, y2)`, with position before momentum. -/
def ehLeftHamiltonian (μ c : ℝ) (s : Phase) : ℝ :=
  let a := Real.cosh (s 0)
  let b := Real.cos (s 1)
  let D := a ^ 2 - b ^ 2
  ((s 2 + Real.sin (2 * s 1) / 8) ^ 2 +
    (s 3 + Real.sinh (2 * s 0) / 8) ^ 2) / 2 +
    c * D / 4 - a / 2 - Real.sinh (2 * s 0) ^ 2 / 128 -
    Real.sin (2 * s 1) ^ 2 / 128 +
    (1 - 2 * μ) * (-b / 2 - (1 / 2 - μ - a * b) * D / 16)

/-- A point of the left collision circle, choosing the lift compatible with
`z = i / sqrt(2) * sinh((x1 + i*x2)/2)`. -/
def ehLeftCollisionPoint (μ : ℝ) : Phase :=
  ![0, 0, 0, -Real.sqrt (2 * (1 - μ))]

/-- The selected zero-level component in the centered real EH coordinates.
No convexity, regularity, or coordinate transport is built into this definition. -/
def ehLeftEnergyComponent (μ c : ℝ) : Set Phase :=
  connectedComponentIn {s : Phase | ehLeftHamiltonian μ c s = 0}
    (ehLeftCollisionPoint μ)

end

end BirkhoffGlobalSection


