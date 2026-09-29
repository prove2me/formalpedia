-- Prove2me | Definitions.Def_RandomGradFree_Accelerated_C
-- name    : RandomGradFree_Accelerated_C
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:06:01.669425+00:00
-- url     : https://prove2.me/theorems/c0d2c80f-087c-471b-bb03-d287cb5dde21
-- title:
--   The bias accumulation factor $C_k = 1 + \sum_{i=1}^{k-1}\prod_{j=k-i}^{k-1}(1-\alpha_j)$ (proof of Theorem 9)
-- statement:
--   Let $(\alpha_j)_{j \ge 0}$ be a real sequence. Set $C_0 = 0$ and, for $k \ge 1$,
--
--   $$
--   C_k = 1 + \sum_{i=1}^{k-1} \prod_{j=k-i}^{k-1} (1 - \alpha_j).
--   $$
--
--   For example $C_1 = 1$ and $C_2 = 2 - \alpha_1$. In Theorem 9, $C_k$ multiplies the per-iteration error that the finite-difference oracle of the accelerated random method $\mathcal{FG}_\mu$ introduces, so it measures how the oracle bias accumulates over $k$ iterations.
--
--   **Formalization Note** The case $k = 0$ is separated explicitly because the displayed formula would give $1$ at $k = 0$, while the paper defines $C_0 = 0$. The index $k - i$ is natural-number subtraction with $1 \le i \le k-1$, so it never truncates.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 550, proof of Theorem 9 (definition of C_k)

import Mathlib

namespace RandomGradFree.Accelerated

/-- The accumulation factor of the oracle bias from the proof of Theorem 9
(Nesterov–Spokoiny, p. 550): `C_0 = 0` and, for `k ≥ 1`,
`C_k = 1 + ∑_{i=1}^{k-1} ∏_{j=k-i}^{k-1} (1 - α_j)`. -/
noncomputable def C (α : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0
  else 1 + ∑ i ∈ Finset.Ico 1 k, ∏ j ∈ Finset.Ico (k - i) k, (1 - α j)

end RandomGradFree.Accelerated


