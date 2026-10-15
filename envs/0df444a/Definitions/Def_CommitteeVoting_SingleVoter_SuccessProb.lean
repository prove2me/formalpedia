-- Prove2me | Definitions.Def_CommitteeVoting_SingleVoter_SuccessProb
-- name    : CommitteeVoting_SingleVoter_SuccessProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:47.245831+00:00
-- url     : https://prove2.me/theorems/cc9a3ff3-ef1f-40d3-9055-ce6628fca69b
-- title:
--   (3) and (6), p. 11 — the success probability Pr[𝕋 = H | s] of a single voter's ballot
-- statement:
--   A single voter observes signals and computes, for each candidate $c_j$, the **posterior probability** of honesty $s_j = \Pr[c_j = H \mid s^*_j]$ ((3)). Given the signals, the candidates' types are independent, $c_j$ being honest with probability $s_j$. The voter's objective (6) with $n = 1$ is the **success probability** of the ballot $\mathcal C$,
--
--   $$
--   \Pr[\mathbb T = H \mid s] \;=\; \sum_{\mathrm{Hon}\,:\ \mathbb T = H} \ \prod_{j \in \mathrm{Hon}} s_j \prod_{j \notin \mathrm{Hon}} (1 - s_j),
--   $$
--
--   the sum running over the sets $\mathrm{Hon}$ of honest candidates for which every admissible committee under the scores of $\mathcal C$ has at least $\lceil (1-p)k \rceil$ honest members (Definition 3).
--
--   It is the quantity a single voter maximises in Proposition 2.
--
--   **Formalization Note** The posteriors $s : \{0,\dots,m-1\} \to \mathbb R$ are taken as given; the Gaussian signal model (2)–(4) that produces them is not formalized. Conditional independence of the types given the signals is built into the product weights (each producer is honest independently a priori, p. 16, and signals are independent across producers). The filter over honest sets uses classical decidability.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 11, (3) and (6); pp. 10–11, Definition 3

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial
import Definitions.Def_CommitteeVoting_SingleVoter_Committee

namespace CommitteeVoting.SingleVoter

open Classical in
/-- Success probability `Pr[𝕋 = H | s]` ((6), p. 11, with `n = 1`) of the ballot `C` of a single
voter whose posterior probabilities of honesty ((3), p. 11) are `s j`: the candidates' types are
independent given the signals, candidate `j` honest with probability `s j`, so the probability of a
realised honest set `Hon` is `∏_{j ∈ Hon} s j ∏_{j ∉ Hon} (1 - s j)`, and the success probability
is the total weight of the honest sets for which every admissible committee is honest. -/
noncomputable def successProb {m : ℕ} (k : ℕ) (p : ℝ) (s : Fin m → ℝ) (C : Finset (Fin m)) : ℝ :=
  ∑ Hon ∈ (Finset.univ : Finset (Fin m)).powerset.filter
      (fun Hon => CommitteeVoting.ExpConv.IsHonestOutcome k p Hon (singleScore C)),
    pbWeight s Finset.univ Hon

end CommitteeVoting.SingleVoter


