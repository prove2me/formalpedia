-- Prove2me | Definitions.Def_BirkhoffShootingCoordinates
-- name    : BirkhoffShootingCoordinates
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-09-25T07:47:37.388991+00:00
-- url     : https://prove2.me/theorems/453b1a7b-6c1e-4cdb-973f-bb2b41f63cf9
-- title:
--   Birkhoff shooting coordinates (velocity sine, depth) of a Levi-Civita state
-- statement:
--   Let $0<\mu<1$ and let a Levi-Civita state $s=(z_1,z_2,w_1,w_2)$ be mapped to the Jacobi state $(q_1,q_2,p_1,p_2)=\Phi_\mu(s)$ by the inverse Levi-Civita coordinate change (`leviCivitaToJacobi`), so that $q+\mu = 2z^2$ and $p = w/\bar z$.
--
--   1. The **Jacobi velocity** of a Jacobi state $(q_1,q_2,p_1,p_2)$ is the rotating-frame velocity
--   $$
--   v=\dot q=\frac{\partial H}{\partial p}=(p_1-q_2,\;p_2+q_1),
--   $$
--   where $H$ is the Jacobi Hamiltonian of the planar circular restricted three-body problem.
--
--   2. The **shooting coordinates** of a Levi-Civita state $s$ are the pair
--   $$
--   \sigma(s)=\frac{v_2}{\sqrt{v_1^2+v_2^2}},\qquad \eta(s)=-y_{\mathrm{rel}}(s),
--   $$
--   where $v=(v_1,v_2)$ is the Jacobi velocity of $\Phi_\mu(s)$ and $(x_{\mathrm{rel}},y_{\mathrm{rel}})=2z^2$ is the physical position relative to the primary at $(-\mu,0)$. When the orbit crosses the vertical line $x_{\mathrm{rel}}=0$ below the axis, $\sigma$ is the sine of the angle the velocity makes with the horizontal and $\eta$ is the depth of the crossing point.
--
--   These are the coordinates in which Birkhoff compares the two one-parameter families of half-orbits in his shooting proof of the existence of a retrograde periodic orbit: each family traces a curve in the rectangle $[-1,1]\times[0,1]$ of $(\sigma,\eta)$ values, and an intersection of the two curves yields a symmetric half-orbit.
--
--   **Formalization Note** The square root is Mathlib's totalized `Real.sqrt`, so $\sigma=0$ when the velocity vanishes; the definition is only used at states with nonzero horizontal velocity.
-- source:
--   Liu--Salomao, Finite energy foliations in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Section 5, proof of Theorem 5.1 (pp. 30-31): the (velocity angle, q_2) rectangle in which the curves Gamma_1, Gamma_2 are drawn; after G. D. Birkhoff, The restricted problem of three bodies, Rend. Circ. Mat. Palermo 39 (1915), Section 18.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

noncomputable section

/-- The Jacobi (rotating-frame) velocity `q̇ = (p₁ - q₂, p₂ + q₁)` of a Jacobi
state `(q₁, q₂, p₁, p₂)`, i.e. `∂H/∂p` for the Jacobi Hamiltonian. -/
def jacobiVelocity (s : Phase) : Plane :=
  ![s 2 - s 1, s 3 + s 0]

/-- Birkhoff's shooting coordinates of a Levi-Civita state: the sine of the
angle that the physical velocity makes with the `q₁`-direction, and the depth
of the physical position below the axis of the primaries. -/
def shootingCoordinates (μ : ℝ) (s : Phase) : ℝ × ℝ :=
  (jacobiVelocity (leviCivitaToJacobi μ s) 1 /
      Real.sqrt (jacobiVelocity (leviCivitaToJacobi μ s) 0 ^ 2 +
        jacobiVelocity (leviCivitaToJacobi μ s) 1 ^ 2),
    -relativePosition μ s 1)

end

end BirkhoffGlobalSection


