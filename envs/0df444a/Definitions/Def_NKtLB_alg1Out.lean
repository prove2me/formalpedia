-- Prove2me | Definitions.Def_NKtLB_alg1Out
-- name    : NKtLB_alg1Out
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:07:34.800239+00:00
-- url     : https://prove2.me/theorems/88fb6628-c11c-4c02-b59e-6008fa4cbbfa
-- title:
--   The output of Algorithm 1
-- statement:
--   The output of Algorithm 1 on $(\gamma,1^n)$ with oracle $L$ is $s_{i_0}$ for the first $i_0\ge2$ with $\theta_{i_0}>n/(2-2\gamma')$, where $\gamma'=(\gamma+1/2)/2$. It is $\bot$ if no such $i_0$ exists or if $s_{i_0}=\bot$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Algorithm 1, p.75, lines 19–22

import Mathlib
import Definitions.Def_NKtLB_alg1
import Definitions.Def_NKtLB_alg1Theta

namespace NKtLB

/-- **The output of Algorithm 1** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Algorithm 1, p.75, lines 19–22): `s_{i₀}` for the first
`i₀ ≥ 2` with `θ_{i₀} > n/(2 − 2γ′)`, `γ′ = (γ + 1/2)/2`; `none` (`⊥`) if there is no such `i₀` or
`s_{i₀} = ⊥`. -/
noncomputable def alg1Out (F : PRGFamily) (L : Set (List Bool)) (γ : ℝ) (b n : ℕ) :
    Option (List Bool) := by
  classical
  exact if h : ∃ i : ℕ, 2 ≤ i ∧ (n : ℝ) / (2 - 2 * ((γ + 1 / 2) / 2)) < alg1Theta γ n i then
    alg1 F L γ b n (Nat.find h) else none

end NKtLB


