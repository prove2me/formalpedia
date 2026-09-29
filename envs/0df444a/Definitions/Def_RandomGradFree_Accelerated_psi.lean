-- Prove2me | Definitions.Def_RandomGradFree_Accelerated_psi
-- name    : RandomGradFree_Accelerated_psi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:05:38.759736+00:00
-- url     : https://prove2.me/theorems/3350a49c-f423-46e1-b3ec-ba3f29a7936d
-- title:
--   The product $\psi_k = \prod_{i=0}^{k-1}(1-\alpha_i)$ (proof of Theorem 9)
-- statement:
--   Let $(\alpha_i)_{i \ge 0}$ be a real sequence. For $k \ge 0$ set
--
--   $$
--   \psi_k = \prod_{i=0}^{k-1} (1 - \alpha_i),
--   $$
--
--   so that $\psi_0 = 1$. For the accelerated random method $\mathcal{FG}_\mu$, where $\alpha_k$ are the step-a) coefficients, $\psi_k$ is the factor by which the initial residual is multiplied after $k$ iterations in Theorem 9.
--
--   **Formalization Note** $\psi_0 = 1$ is the empty product, matching the paper's convention "Defining $\psi_0 = 1$".
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 550, proof of Theorem 9 (definition of ψ_k)

import Mathlib

namespace RandomGradFree.Accelerated

/-- The product `ψ_k = ∏_{i=0}^{k-1} (1 - α_i)` from the proof of Theorem 9
(Nesterov–Spokoiny, p. 550), with `ψ_0 = 1` (empty product). -/
noncomputable def psi (α : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, (1 - α i)

end RandomGradFree.Accelerated


