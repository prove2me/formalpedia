-- Prove2me | Definitions.Def_SparseBatchBandit_reward
-- name    : SparseBatchBandit_reward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:01.600049+00:00
-- url     : https://prove2.me/theorems/897754e5-3f0b-43cc-809d-2799076fe577
-- title:
--   Observed reward
-- statement:
--   Under Model-C the reward observed at round $t$ is
--
--   $$
--   r_{t,a_t}=x_{t,a_t}^\top\theta^\star+\xi_t.
--   $$
--
--   The noise $\xi_t$ does not depend on the arm.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, §2.1, p.5

import Mathlib
open Matrix

namespace SparseBatchBandit

/-- The observed reward `r_{t,a_t} = x_{t,a_t}⊤θ⋆ + ξ_t` under Model-C, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, §2.1, p.5 (PDF 5). The
noise `ξ_t` does not depend on the arm. -/
def reward {T K d : ℕ} (c : Fin T → Fin K → Fin d → ℝ) (e : Fin T → ℝ) (θstar : Fin d → ℝ)
    (a : Fin T → Fin K) (t : Fin T) : ℝ :=
  c t (a t) ⬝ᵥ θstar + e t

end SparseBatchBandit


