-- Prove2me | Definitions.Def_BorelRobustMDP_Policy
-- name    : BorelRobustMDP_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:12:01.252203+00:00
-- url     : https://prove2.me/theorems/f5dd4609-6ef2-4788-b775-ceb1280ee8cc
-- title:
--   Randomized policies $\Pi^R$
-- statement:
--   A **randomized policy** is a sequence $\pi=(\pi_0,\dots,\pi_{N-1})$ of stochastic kernels from histories to the action space with $\pi_n(D_n(x_n)\mid h_n)=1$ for $h_n\in\mathcal H_n$.
--
--   This is the class over which the controller minimizes.
--
--   **Formalization Note.** The kernels are on raw histories, and the constraint is at feasible ones. The helper `Policy.act` returns the law of the action at time $k$, and $0$ beyond the horizon, where it is unused.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, Definition 2.2 (i), p.3

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BorelRobustMDP_DecisionModel
import Definitions.Def_BorelRobustMDP_Feasible

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (Hist histState)

namespace BorelRobustMDP

universe u v

variable {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A] [MeasurableSpace Z]
  {N : ℕ}

/-- A randomized policy `π = (π_0, …, π_{N−1}) ∈ Π^R` (Bäuerle & Glauner, arXiv:2007.13103v1,
Definition 2.2 (i), p.3): stochastic kernels `π_n` from histories to `A` with
`π_n(D_n(x_n) | h_n) = 1` for `h_n ∈ 𝓗_n`.

**Formalization Note.** The kernels are defined on raw histories and the constraint is at feasible
ones. `𝓗_n` is measurable in `Hist E A n`, so a kernel on `𝓗_n` extends to a Markov kernel, and only
feasible histories are ever reached from a feasible one. -/
structure Policy (M : DecisionModel E A Z N) where
  kernel : (n : Fin N) → Kernel (Hist E A n) A
  isMarkovKernel : ∀ n, IsMarkovKernel (kernel n)
  constraint : ∀ (n : Fin N) (h : Hist E A n), M.Feasible n h →
    kernel n h (M.sec n (histState n h)) = 1

/-- The law of the action at time `k` given the history, `0` beyond the horizon, where it is never
used. -/
noncomputable def Policy.act {M : DecisionModel E A Z N} (π : Policy M) (k : ℕ)
    (h : Hist E A k) : Measure A :=
  if hk : k < N then π.kernel ⟨k, hk⟩ h else 0

end BorelRobustMDP


