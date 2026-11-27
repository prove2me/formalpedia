-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Supplement_Algorithm3
-- name    : OnlineMatchFrameworks_Supplement_Algorithm3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:20:14.400856+00:00
-- url     : https://prove2.me/theorems/a4447c36-a54a-42c4-b4b8-82427a4ac415
-- title:
--   Algorithm 3: policy rounding with simulated probes
-- statement:
--   **Algorithm 3** is Algorithm 2 without the skipping rule. At each time an arrival of type $v$ receives a policy $\pi$ drawn with probability $x_v(\pi)/q_v$, and every item of $\pi$ is attempted in order, by a real probe if it is unmatched and by a simulated probe otherwise. Its expected reward is
--
--   $$
--   \mathrm{ALG}(G)=\mathrm{alg}_{\,\mathrm{keep}(v,\pi)=\pi}\bigl((1,\dots,T),U\bigr).
--   $$
--
--   It is the algorithm of the guarantees for IID arrivals and for vertex weights.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §4.3, p.20; Algorithm 3, p.21

import Definitions.Def_OnlineMatchFrameworks_Supplement_Algorithm2

open scoped BigOperators

namespace OnlineMatchFrameworks.Supplement

namespace ProphetInstance

variable {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V]

/-- **`ALG(G)` of Algorithm 3.** arXiv:1907.03963v6, Algorithm 3, p.21: Algorithm 2 without the skipping
rule (§4.3, p.20). Every item of the sampled policy is probed, really if it is unmatched and in
simulation otherwise. -/
noncomputable def ALG3 (G : ProphetInstance U V) (x : V → OnlineMatchFrameworks.Policy U → ℝ) : ℝ :=
  G.roundingFrom x (fun _ l => l) (List.finRange G.horizon) Finset.univ

end ProphetInstance

end OnlineMatchFrameworks.Supplement


