-- Prove2me | Definitions.Def_HodgeComputerFourPlusTwoSymmetry
-- name    : HodgeComputerFourPlusTwoSymmetry
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T08:25:16.725971+00:00
-- url     : https://prove2.me/theorems/11c51e04-6e7b-40ce-ac7a-d79140045128
-- title:
--   Bipartite sign involutions and strict core certificate predicates for four-plus-two-residual
-- statement:
--   This module defines the bipartite $(\mathbb{Z}/2 \times \mathbb{Z}/2)$ sign involutions and normalized certificate predicates on the four-variable core polynomial $H(x_0, x_1, y_0, y_1)$ of `four-plus-two-residual`.
--
--   Write $(x_0, x_1, y_0, y_1)$ for the four core coordinates `(X 0, X 1, X 2, X 3)` in $\mathbb{C}[x_0, x_1, y_0, y_1]$, where
--
--   $$
--   H(x_0, x_1, y_0, y_1) = \Bigl(x_0^6 + \frac{5}{7} x_0^5 x_1 + \frac{10}{7} x_0 x_1^5 + x_1^6\Bigr) + \Bigl(y_0^6 + \frac{5}{7} y_0^5 y_1 + \frac{15}{7} y_0 y_1^5 + y_1^6\Bigr) + \frac{5}{7} x_0 x_1 y_0 y_1 (x_0^2 + 2 y_0^2),
--   $$
--
--   and $A = x_0^3 y_0^3$. Because every monomial of $H$ has even total degree in $(x_0, x_1)$ and even total degree in $(y_0, y_1)$, the two commuting sign involutions
--
--   $$
--   \sigma_{AB}(x_0, x_1, y_0, y_1) = (-x_0, -x_1, y_0, y_1), \qquad \sigma_{CD}(x_0, x_1, y_0, y_1) = (x_0, x_1, -y_0, -y_1)
--   $$
--
--   preserve $H$ while negating $A = x_0^3 y_0^3$.
--
--   The module introduces two normalized refinements of `CoreCertificate`:
--
--   1. `StrictCoreCertificate D N`: a nonzero homogeneous denominator $D$ of degree $k + 1$ and homogeneous vector field $N = (N_0, N_1, N_2, N_3)$ of degree $k + 2$ satisfying the decoupled divergence-free system
--
--   $$
--   N \cdot \nabla H = A D \qquad \text{and} \qquad D \operatorname{div}(N) - N \cdot \nabla D = 0.
--   $$
--
--   2. `BipartiteCoreCertificate D N`: an even-degree core certificate ($\deg D = 2m + 2$, $\deg N_i = 2m + 3$) whose denominator $D$ is invariant under both $\sigma_{AB}$ and $\sigma_{CD}$, while $(N_0, N_1)$ is $\sigma_{AB}$-even and $(N_2, N_3)$ is $\sigma_{AB}$-odd.
--
--   **Formalization Note** Built on `Definitions.Def_HodgeComputerFourPlusTwoCore` using `MvPolynomial.aeval` algebra homomorphisms `flipAB` and `flipCD`.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual`, `data/four-plus-two-residual/instance.rec`, and GitHub Discussion #120 (`benediamond`, `kejace`, `DiamondJM`, `kmehltretter82`), https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoCore

set_option autoImplicit false
noncomputable section

namespace HodgeComputer.FourPlusTwoResidual

open MvPolynomial
open scoped BigOperators

/-- Sign involution `(x₀, x₁, x₂, x₃) ↦ (-x₀, -x₁, x₂, x₃)` on the four-variable core ring. -/
def flipAB : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
  aeval ![-X 0, -X 1, X 2, X 3]

/-- Sign involution `(x₀, x₁, x₂, x₃) ↦ (x₀, x₁, -x₂, -x₃)` on the four-variable core ring. -/
def flipCD : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
  aeval ![X 0, X 1, -X 2, -X 3]

/-- A strict divergence-free core certificate: `D ≠ 0` homogeneous of degree `k + 1` and
`N` homogeneous of degree `k + 2` satisfying both `N · ∇H = A D` and `D div(N) - N · ∇D = 0`. -/
def StrictCoreCertificate (D : MvPolynomial (Fin 4) ℂ)
    (N : Fin 4 → MvPolynomial (Fin 4) ℂ) : Prop :=
  D ≠ 0 ∧ (∃ k : ℕ, D.IsHomogeneous (k + 1) ∧ ∀ i, (N i).IsHomogeneous (k + 2)) ∧
    (∑ i, pderiv i core * N i = coreSource * D) ∧
    (D * (∑ i, pderiv i (N i)) - ∑ i, pderiv i D * N i = 0)

/-- An even-degree `(ℤ/2 × ℤ/2)`-equivariant core certificate: `D` has even positive degree `2m + 2`
and is invariant under both `flipAB` and `flipCD`, while `(N₀, N₁)` is `flipAB`-even and `(N₂, N₃)`
is `flipAB`-odd, satisfying the exact four-variable `CoreCertificate` differential equation. -/
def BipartiteCoreCertificate (D : MvPolynomial (Fin 4) ℂ)
    (N : Fin 4 → MvPolynomial (Fin 4) ℂ) : Prop :=
  D ≠ 0 ∧ (∃ m : ℕ, D.IsHomogeneous (2 * m + 2) ∧ ∀ i, (N i).IsHomogeneous (2 * m + 3)) ∧
    flipAB D = D ∧ flipCD D = D ∧
    flipAB (N 0) = N 0 ∧ flipAB (N 1) = N 1 ∧
    flipAB (N 2) = -N 2 ∧ flipAB (N 3) = -N 3 ∧
    2 * coreSource * D ^ 2 - 2 * D * (∑ i, pderiv i core * N i)
      + 3 * core * (D * (∑ i, pderiv i (N i)) - ∑ i, pderiv i D * N i) = 0

end HodgeComputer.FourPlusTwoResidual


