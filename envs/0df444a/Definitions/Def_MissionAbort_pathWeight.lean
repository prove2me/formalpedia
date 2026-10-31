-- Prove2me | Definitions.Def_MissionAbort_pathWeight
-- name    : MissionAbort_pathWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:57.547415+00:00
-- url     : https://prove2.me/theorems/618310ab-a8ee-43b6-9357-07ec1dd9538d
-- title:
--   Finite-dimensional weight of a continuous-time chain
-- statement:
--   For a finite state space, an initial vector $\pi_0$, a rate matrix $Q$, times $0=t_0\le t_1\le\dots\le t_k$ and states $s_0,\dots,s_k$, the weight
--   $$
--   \pi_0(s_0)\prod_{i=0}^{k-1}\big[e^{(t_{i+1}-t_i)Q}\big]_{s_is_{i+1}}.
--   $$
--   It is the probability that a continuous-time Markov chain with these data visits the given states at the given times.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4.1, p.14 (the rate matrix of the surrogate)

import Mathlib

namespace MissionAbort

/-- The finite-dimensional weight of a continuous-time Markov chain with initial law `π₀` and rate
matrix `Q`: for times `0 = t₀ ≤ t₁ ≤ ⋯ ≤ t_k` and states `s₀, …, s_k`,
`π₀(s₀) ∏ᵢ [exp((t_{i+1} − tᵢ) Q)]_{sᵢ s_{i+1}}`. This is the standard transition function of a
finite CTMC (Sun, Hu & Ye, arXiv:2505.03225v1, §4.1, p.14, defines `Q` by its instantaneous rates). -/
noncomputable def pathWeight {ι : Type*} [Fintype ι] [DecidableEq ι] (π₀ : ι → ℝ)
    (Q : Matrix ι ι ℝ) {k : ℕ} (t : Fin (k + 1) → ℝ) (s : Fin (k + 1) → ι) : ℝ :=
  π₀ (s 0) * ∏ i : Fin k,
    (NormedSpace.exp ((t i.succ - t i.castSucc) • Q)) (s i.castSucc) (s i.succ)

end MissionAbort


