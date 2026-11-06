-- Prove2me | Definitions.Def_FirstOrderFG_Qobs
-- name    : FirstOrderFG_Qobs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:22.661679+00:00
-- url     : https://prove2.me/theorems/ae519d21-f35b-4834-bfcd-dcbb8361e6fe
-- title:
--   Observation probability $Q_i^G(q)$
-- statement:
--   Throughout, $G=(V,E)$ is a directed graph on the arms $V=[K]$; the edge $i\to j$ means that playing arm $i$ reveals the loss of arm $j$.
--
--   For a distribution $q$ on the arms, the probability that the loss of arm $i$ is observed when the played arm is drawn from $q$ is
--   $$
--   Q_i^G(q)=\sum_{j\in V:\ j\to i} q_j ,
--   $$
--   the total mass of the in-neighbours of $i$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3

import Mathlib

namespace FirstOrderFG

/-- **Observation probability `Q_i^G(q)`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3: "For a distribution `q ∈ ∆_K`,
denote by `Q_i^G(q)` the probability of observing the loss of action `i`, that is,
`Q_i^G(q) ≜ ∑_{j ∈ V : j → i} q_j`."

**Formalization Note.** The sum runs over the in-neighbours `j` of `i` (`E j i`). -/
def Qobs {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (q : Fin K → ℝ) (i : Fin K) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => E j i), q j

end FirstOrderFG


