-- Prove2me | Definitions.Def_StochDepartSec_BestSoFar
-- name    : StochDepartSec_BestSoFar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:12.753821+00:00
-- url     : https://prove2.me/theorems/37845ea9-8f2a-4da3-862e-12c241b9aa7a
-- title:
--   Best-so-far candidate at time $t$
-- statement:
--   Candidate $i$ is the **best-so-far** at time $t$ in outcome $\omega$ if it has arrived by $t$ ($a_i\le t$) and is better than every other candidate $j$ that has arrived by $t$: $\sigma(i)<\sigma(j)$ whenever $a_j\le t$, $j\ne i$.
--
--   Departed candidates are part of the comparison. Since $\sigma$ is injective, there is at most one best-so-far candidate at any time.
--
--   **Formalization Note** The paper defines the best-so-far as $\max\{i : A_i\le t,\ R_i=1\}$, the last arrival that was better than all earlier ones; this is the best among the arrived candidates.
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, §2, p.5

import Mathlib
import Definitions.Def_StochDepartSec_Outcome

namespace StochDepartSec

/-- Candidate `i` is the best-so-far at time `t`: it has arrived by `t` and is better (smaller
overall rank) than every other candidate that has arrived by `t`.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, §2, p.5: "At time t, we call the candidate max{i : A_i ≤ t, R_i = 1} the best-so-far."

**Formalization Note** The last arrival with relative rank 1 is the best among the arrived
candidates, which is what this definition says directly. Departed candidates are compared too.
Since `σ` is injective there is at most one best-so-far at any time. -/
def BestSoFar {n : ℕ} (ω : Outcome n) (t : ℝ) (i : Fin n) : Prop :=
  arrival ω i ≤ t ∧ ∀ j, arrival ω j ≤ t → j ≠ i → rank ω i < rank ω j

end StochDepartSec


