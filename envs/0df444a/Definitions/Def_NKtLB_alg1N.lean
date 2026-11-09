-- Prove2me | Definitions.Def_NKtLB_alg1N
-- name    : NKtLB_alg1N
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:56:39.131941+00:00
-- url     : https://prove2.me/theorems/f6cb67df-9a16-427f-abc6-0a751903b9b8
-- title:
--   The lengths $N_i$ of Algorithm 1
-- statement:
--   For $\gamma\in(1/2,1)$ and $n\in\mathbb N$, let $\gamma'=(\gamma+1/2)/2$, $N_1=n$ and $\theta_1=\gamma n$. For $i\ge2$,
--   $$
--   m_{i,1}=\lceil\gamma' n/\gamma\rceil,\quad m_{i,2}=\lceil\gamma'\theta_{i-1}/\gamma\rceil,\quad N_i=m_{i,1}+m_{i,2},\quad \theta_i=\gamma N_i .
--   $$
--   $N_i$ is the length of the string $s_i$ built in round $i$.
--
--   **Formalization Note** $N_0=n$ is a placeholder; the algorithm has no $N_0$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Algorithm 1, p.75, lines 2, 7, 9–11

import Mathlib

namespace NKtLB

/-- **The lengths `N_i` of Algorithm 1** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Algorithm 1, p.75, lines 2, 7, 9–11):
`N₁ := n`, `θ₁ := γn`, `γ′ := (γ + 1/2)/2`, and for `i ≥ 2`
`m_{i,1} := ⌈γ′n/γ⌉`, `m_{i,2} := ⌈γ′θ_{i−1}/γ⌉`, `N_i := m_{i,1} + m_{i,2}`, `θ_i := γN_i`.

**Formalization Note.** `N_0 := n` is a placeholder (the algorithm has no `N_0`). -/
noncomputable def alg1N (γ : ℝ) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | 1 => n
  | i + 2 => ⌈(γ + 1 / 2) / 2 * n / γ⌉₊ + ⌈(γ + 1 / 2) / 2 * (γ * alg1N γ n (i + 1)) / γ⌉₊

end NKtLB


