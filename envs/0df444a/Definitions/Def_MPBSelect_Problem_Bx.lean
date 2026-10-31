-- Prove2me | Definitions.Def_MPBSelect_Problem_Bx
-- name    : MPBSelect_Problem_Bx
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:18.650973+00:00
-- url     : https://prove2.me/theorems/eec802b8-4366-4b58-85ab-0845a56bfd20
-- title:
--   Parameters $\theta_b$ that carry a pair of $\Xi$
-- statement:
--   Let
--   $$
--   B_\Xi=\{\theta_b:\ (i,\theta_b)\in\Xi\ \text{for some } i\}
--   $$
--   be the set of parameters at which some solution is neither the MPB $i^*$ nor the conditional optimum $i^b$. Every $\theta_b\in\Theta_{i^*}$ is in $B_\Xi$, and when $k\ge3$ every $\theta_b$ is. Only for $k=2$ can a parameter $\theta_b\notin\Theta_{i^*}$ lie outside $B_\Xi$; then the two solutions are $i^b$ and $i^*$, and $\alpha_{i^b}(\theta_b)$ enters no term of the objective of (20).
--
--   This set is not a symbol of the paper. It is the set on which the corrected positivity and KKT steps of the proof of Theorem 3 state their conditions on $\alpha_{i^b}(\theta_b)$.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, proof of Theorem 3, p.ec9 (correction of the positivity and KKT steps)

import Mathlib
import Definitions.Def_MPBSelect_Problem
import Definitions.Def_MPBSelect_Problem_Xi

namespace MPBSelect

open Finset

/-- **Parameters that carry a pair of `Ξ`.**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, proof of Theorem 3,
p.ec9 (used in the corrected positivity and KKT steps).

`Bx = {b | ∃ i, (i, θ_b) ∈ Ξ}` is the set of parameters `θ_b` at which some solution `i` is
neither the MPB `i*` nor the conditional optimum `i^b`. Every `θ_b ∈ Θ_{i*}` is in `Bx`; when
`k ≥ 3` every `θ_b` is. Only when `k = 2` can a `θ_b ∉ Θ_{i*}` lie outside `Bx`: then the two
solutions are `i^b` and `i*`, and `α_{i^b}(θ_b)` enters no term of the objective of (20).

**Formalization Note** Not a symbol of the paper; it names the set over which the corrected
milestones `theorem_3_positivity` and `theorem_3_kkt` state positivity of `α_{i^b}(θ_b)` and
the condition (EC.20). -/
def Problem.Bx {k B : ℕ} (P : Problem k B) : Finset (Fin B) :=
  univ.filter (fun b => ∃ i : Fin k, (i, b) ∈ P.Xi)

end MPBSelect


