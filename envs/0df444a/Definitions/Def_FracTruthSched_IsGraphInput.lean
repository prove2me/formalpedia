-- Prove2me | Definitions.Def_FracTruthSched_IsGraphInput
-- name    : FracTruthSched_IsGraphInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:54.700666+00:00
-- url     : https://prove2.me/theorems/9e448769-b262-4fdb-a5b1-8e1b22135012
-- title:
--   Graph input of $MC_\ell$
-- statement:
--   A **graph input** of $MC_\ell$ specifies the two endpoint values of every edge and the owner value of every self-loop, all nonnegative, and no other values. Each machine's values are those on the core tasks of which it is an endpoint or the owner.
--
--   **Formalization Note.** A graph input is encoded as a real matrix indexed by machines and core tasks that is nonnegative and equal to $0$ at every pair (machine, task) where the machine is neither an endpoint nor the owner. A machine's cost $\sum_e t_{ie}x_{ie}$ is then its cost on its incident tasks.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Definition 3, p.9

import Mathlib
import Definitions.Def_FracTruthSched_incident

set_option autoImplicit false

namespace FracTruthSched

/-- A **graph input** of `MC_ℓ` (Anastasiadis et al., arXiv:2611.06642v1, Definition 3, p.9: "A graph
input specifies the two endpoint values of every edge of MC_ℓ and the owner value of every
self-loop, all nonnegative, and no other values").

**Formalization Note.** A graph input is encoded as an `n × (core tasks)` real matrix that is
nonnegative and **zero** at every pair `(i, e)` where `i` is neither an endpoint nor the owner of
`e`. A machine's cost `Σ_e t_ie x_ie` is then its cost on its incident tasks, which is what (1)
charges once the allocation is eligible, and a report of machine `i` within this domain changes
only its incident entries. The optimum `C` is taken over eligible allocations only (`C`). -/
def IsGraphInput {n ℓ : ℕ} (t : Fin n → CoreTask n ℓ → ℝ) : Prop :=
  ∀ i e, 0 ≤ t i e ∧ (¬ incident i e → t i e = 0)

end FracTruthSched


