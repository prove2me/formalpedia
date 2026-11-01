-- Prove2me | Definitions.Def_DuanEP_Pure_pairCoeff
-- name    : DuanEP_Pure_pairCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:48.056597+00:00
-- url     : https://prove2.me/theorems/fd8714da-e527-4ced-adb1-8fef530ad745
-- title:
--   Two-mode squeezed state $|\Psi\rangle_{A_iB_i}$, Eq. (1)
-- statement:
--   Let $r\in\mathbb R$ be the squeezing parameter and $\lambda=\tanh r$. The **two-mode squeezed state** of a pair of modes $A_i,B_i$ is, in the number (Fock) basis,
--
--   $$
--   |\Psi\rangle_{A_iB_i}=\sqrt{1-\lambda^2}\sum_{n=0}^{\infty}\lambda^n\,|n\rangle_{A_i}|n\rangle_{B_i}.
--   $$
--
--   It is represented by its coefficient function $c_r:\mathbb N\times\mathbb N\to\mathbb C$, where $c_r(n,n')$ is the coefficient of $|n\rangle_{A_i}|n'\rangle_{B_i}$: $c_r(n,n)=\sqrt{1-\lambda^2}\,\lambda^n$ and $c_r(n,n')=0$ for $n\neq n'$.
--
--   This is the resource state of the purification protocol: every pair shared by the two distant sides is in this state.
--
--   **Formalization Note** At $r=0$ the convention $0^0=1$ makes $c_0$ the vacuum $|0\rangle|0\rangle$. The paper takes $r\ge 0$; the definition accepts every real $r$.
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 1, Eq. (1)

import Mathlib

namespace DuanEP.Pure

/-- The two-mode squeezed state `|Ψ⟩_{AᵢBᵢ} = √(1 − λ²) ∑ₙ λⁿ |n⟩_{Aᵢ} |n⟩_{Bᵢ}` with
`λ = tanh r` (Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, Eq. (1), p. 1), as its coefficient function on Fock labels:
`pairCoeff r (n, n')` is the coefficient of `|n⟩_A |n'⟩_B`.

**Formalization Note** The state is a coefficient function `ℕ × ℕ → ℂ` (first label: mode `Aᵢ`,
second: mode `Bᵢ`); its normalization is proved in `pair_entanglement`, not typed. The squeezing
parameter `r` ranges over all of `ℝ` (the paper has `r ≥ 0`). At `r = 0` the coefficient
`tanh 0 ^ 0 = 0 ^ 0 = 1` gives the vacuum `|0⟩|0⟩`. -/
noncomputable def pairCoeff (r : ℝ) : ℕ × ℕ → ℂ := fun p =>
  if p.1 = p.2 then ((Real.sqrt (1 - Real.tanh r ^ 2) * Real.tanh r ^ p.1 : ℝ) : ℂ) else 0

end DuanEP.Pure


