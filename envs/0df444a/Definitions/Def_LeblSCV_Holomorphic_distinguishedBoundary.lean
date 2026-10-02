-- Prove2me | Definitions.Def_LeblSCV_Holomorphic_distinguishedBoundary
-- name    : LeblSCV_Holomorphic_distinguishedBoundary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:59:30.429479+00:00
-- url     : https://prove2.me/theorems/fd23960a-bc90-432d-a5a8-bfeaf6736559
-- title:
--   Distinguished boundary $\Gamma = \partial\Delta_1 \times \cdots \times \partial\Delta_n$ of a polydisc
-- statement:
--   Let $\Delta = \Delta_\rho(a) = \Delta_1 \times \cdots \times \Delta_n$ be a polydisc, where $\Delta_k$ is the disc $\{|z_k - a_k| < \rho_k\}$ in the $k$-th coordinate. Its **distinguished boundary** is the product of the boundary circles,
--   $$\Gamma = \partial\Delta_1 \times \cdots \times \partial\Delta_n = \{ \zeta \in \mathbb{C}^n : |\zeta_k - a_k| = \rho_k \text{ for } k = 1, \dots, n \}.$$
--   It is a real $n$-dimensional torus, much smaller than the full topological boundary $\partial\Delta$ (of real dimension $2n-1$); the Cauchy integral formula recovers a holomorphic function on $\Delta$ from its values on $\Gamma$ alone.
--
--   **Formalization Note.** Center `a : Fin n → ℂ` and polyradius `ρ : Fin n → ℝ`; positivity of the radii is a hypothesis of the theorems that use $\Gamma$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), pp. 16–17 (Theorem 1.1.4 and the paragraph after Exercise 1.1.2 naming Γ the distinguished boundary)

import Mathlib

namespace LeblSCV.Holomorphic

/-- The distinguished boundary `Γ = ∂Δ_1 × ⋯ × ∂Δ_n` of the polydisc `Δ_ρ(a)` (Lebl, pp. 16–17):
the points whose every coordinate lies on the boundary circle `|ζ_k - a_k| = ρ_k`. -/
def distinguishedBoundary {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {ζ | ∀ k : Fin n, ‖ζ k - a k‖ = ρ k}

end LeblSCV.Holomorphic


