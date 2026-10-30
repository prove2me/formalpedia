-- Prove2me | Definitions.Def_KingDiagonal_tau
-- name    : KingDiagonal_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:11.417459+00:00
-- url     : https://prove2.me/theorems/6f6b80db-7fcd-4e66-81ee-7140ae949bb5
-- title:
--   The normalized matrix $\tau$ with blocks $(\alpha_i\alpha_j)^{-1/2}(\rho)_{ij}$ (eq. 11)
-- statement:
--   Let $\rho$ be a matrix on $\mathbb C^n\otimes\mathbb C^k$ with block traces $\alpha_i = \operatorname{Tr}(\rho)_{ii}$. Define the $kn\times kn$ matrix $\tau$ blockwise by
--
--   $$
--   (\tau)_{ij} = (\alpha_i\alpha_j)^{-1/2}\,(\rho)_{ij}.
--   $$
--
--   When all $\alpha_i > 0$, the diagonal blocks $(\tau)_{ii} = (\rho)_{ii}/\alpha_i$ are states on $\mathbb C^k$, and $\rho$ is the Hadamard product of $A\otimes J_k$ with $\tau$ (eq. (12)).
--
--   **Formalization Note** Entry $((i,a),(j,b))$ is $(\sqrt{\alpha_i\alpha_j})^{-1}\rho_{(i,a),(j,b)}$, with Lean's convention $0^{-1} = 0$: blocks with $\alpha_i\alpha_j = 0$ are set to $0$. The page does not treat $\alpha_i = 0$; for a state such an index has a vanishing block row and column, so no entry where the page's formula is defined changes.
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, eq. (11), p.4

import Mathlib
import Definitions.Def_KingDiagonal_alpha

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, eq. (11), p.4: the `kn × kn` matrix `τ` with blocks
`(τ)_{ij} = (α_i α_j)^{-1/2} (ρ)_{ij}`, where `α_i = Tr (ρ)_{ii}` is (10).

**Formalization Note.** Entry `((i, a), (j, b))` is `(√(α_i α_j))⁻¹ · ρ_{(i,a),(j,b)}`. The page
divides by `(α_i α_j)^{1/2}` without excluding `α_i = 0`; Lean's convention `0⁻¹ = 0` makes the
blocks with `α_i α_j = 0` zero. For a state, `α_i = 0` forces the `i`-th block row and column of
`ρ` to vanish, so this choice changes no entry where the page's formula is defined. -/
noncomputable def tau {n k : Type*} [Fintype k] (ρ : Matrix (n × k) (n × k) ℂ) :
    Matrix (n × k) (n × k) ℂ :=
  Matrix.of fun p q => (((Real.sqrt (alpha ρ p.1 * alpha ρ q.1))⁻¹ : ℝ) : ℂ) * ρ p q

end KingDiagonal


