-- Prove2me | Definitions.Def_OracleRO_ApproxFPL_FPL
-- name    : OracleRO_ApproxFPL_FPL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:10:59.959921+00:00
-- url     : https://prove2.me/theorems/71db8072-3fd1-4463-8cb8-b78f2951fefd
-- title:
--   Follow the Approximate Perturbed Leader (13): cumulative rewards $f_{1:t}$, the uniform perturbation on $[0,1/\eta]^n$, and the expected reward
-- statement:
--   Fix a dimension $n$ and reward vectors $f_1, f_2, \ldots \in \mathbb R^n$, chosen in advance (an *oblivious* reward sequence). This definition file fixes three objects used throughout §3.3.
--
--   1. The **cumulative reward** $f_{1:t} = \sum_{\tau=1}^t f_\tau$, with $f_{1:0} = 0$.
--   2. The **perturbation law** $\mu_\eta$: for $\eta > 0$, the uniform probability distribution on the cube $[0, 1/\eta]^n$, i.e. Lebesgue measure restricted to the cube and divided by its volume $\eta^{-n}$.
--   3. The **expected total reward** of Follow the Approximate Perturbed Leader. Given a map $M:\mathbb R^n\to\mathbb R^n$ (in the theorems, an $\epsilon$-approximate linear optimization procedure over $\mathcal K$), the algorithm (13) plays at round $t$ the decision
--   $$
--   x_t = M\big(f_{1:t-1} + p_t\big), \qquad p_t \sim \mu_\eta ,
--   $$
--   and its expected total reward over $T$ rounds is
--   $$
--   \mathbf E\Big[\sum_{t=1}^T f_t \cdot x_t\Big] \;=\; \sum_{t=1}^T \int f_t \cdot M\big(f_{1:t-1} + p\big)\, d\mu_\eta(p) .
--   $$
--
--   These objects let the regret bound of Theorem 6 and its supporting lemmas be stated without restating the algorithm each time.
--
--   **Formalization Note** By linearity of expectation, $\mathbf E[\sum_t f_t\cdot x_t] = \sum_t \mathbf E[f_t\cdot x_t]$, and $x_t$ depends only on its own perturbation $p_t$; so the expected reward is the same whether the $p_t$ are independent or all equal, as the paper notes at the start of the proof of Theorem 6 (p. 13). The printed rule (13) reads $x_{t+1} = M_\epsilon(\sum_{\tau=1}^t f_t + p_t)$: the summand is $f_\tau$, and the decision of round $t$ uses $f_{1:t-1}$, which is how the proof of Theorem 6 uses it. The uniform law is `ProbabilityTheory.cond volume` of the cube (Lebesgue measure conditioned on the cube). Vectors are `Fin n → ℝ` and $\cdot$ is `dotProduct`.
-- source:
--   Ben-Tal, Hazan, Koren, Mannor, Oracle-Based Robust Optimization via Online Learning, arXiv:1402.6361v1, p. 11, §3.3, (13) and the notation f_{1:t}; p. 13, proof of Theorem 6 (p_1 = … = p_T = p)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace OracleRO.ApproxFPL

/-- The cumulative reward vector `f_{1:t} = ∑_{τ=1}^t f_τ` of §3.3 (arXiv:1402.6361v1, p. 11).
Rewards are indexed from `1`; `prefixSum f 0 = 0`. -/
def prefixSum {n : ℕ} (f : ℕ → Fin n → ℝ) (t : ℕ) : Fin n → ℝ :=
  ∑ τ ∈ Finset.Icc 1 t, f τ

/-- The law of the perturbation `p` of (13) (arXiv:1402.6361v1, p. 11): the uniform distribution
on the cube `[0, 1/η]ⁿ`, i.e. Lebesgue measure conditioned on the cube. For `η > 0` it is a
probability measure. -/
noncomputable def perturbLaw (n : ℕ) (η : ℝ) : Measure (Fin n → ℝ) :=
  volume[|Set.Icc (0 : Fin n → ℝ) (fun _ => η⁻¹)]

/-- The expected total reward `E[∑_{t=1}^T f_t · x_t]` of the Follow the Approximate Perturbed
Leader algorithm (13) (arXiv:1402.6361v1, p. 11) against a fixed (oblivious) reward sequence
`f_1, …, f_T`: at round `t` the decision is `x_t = M(f_{1:t-1} + p_t)` with `p_t` uniform on
`[0, 1/η]ⁿ`.

Formalization Note: by linearity of expectation `E[∑_t f_t · x_t] = ∑_t E[f_t · x_t]`, and each
`x_t` depends on its own perturbation `p_t` only, so the expected total reward is the sum over
`t` of a single integral against the uniform law. This is the same number whether the `p_t` are
independent or all equal (the paper notes this at the start of the proof of Theorem 6, p. 13).
The printed rule (13) reads `x_{t+1} = M_ε(∑_{τ=1}^t f_t + p_t)`; the summand is `f_τ`, and the
decision of round `t` uses `f_{1:t-1}`, as in the proof of Theorem 6. -/
noncomputable def fplExpectedReward {n : ℕ} (M : (Fin n → ℝ) → (Fin n → ℝ))
    (f : ℕ → Fin n → ℝ) (η : ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ∫ p, f t ⬝ᵥ M (prefixSum f (t - 1) + p) ∂(perturbLaw n η)

end OracleRO.ApproxFPL


