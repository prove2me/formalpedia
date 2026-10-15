-- Prove2me | Definitions.Def_CommitteeVoting_SingleVoter_Committee
-- name    : CommitteeVoting_SingleVoter_Committee
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:00.69697+00:00
-- url     : https://prove2.me/theorems/46c17336-fabe-4e8d-881b-a5b83988de4b
-- title:
--   Definition 1, p. 8 — approval scores, and the scores of a single voter's ballot
-- statement:
--   There are $m$ candidates $c_1, \dots, c_m$ and $n$ voters $v_1,\dots,v_n$; voter $v_i$ approves a set $\mathcal C_{v_i}$ of candidates. The **score** of candidate $c_j$ (Definition 1, (1)) is the number of voters approving it,
--
--   $$
--   \mathrm{score}(c_j) = |\{ i : c_j \in \mathcal C_{v_i} \}| .
--   $$
--
--   With a single voter approving $\mathcal C$, the score of $c_j$ is $1$ if $c_j \in \mathcal C$ and $0$ otherwise.
--
--   The $k$ candidates with the highest scores are elected to the committee $\mathbb T$; if fewer than $k$ candidates have non-zero score the committee is filled adversarially, and ties at the lowest elected score are broken adversarially (Definition 3). Accordingly, a set $T$ of candidates is an **admissible committee** if
--
--   $$
--   |T| = k \quad\text{and}\quad \mathrm{score}(b) \le \mathrm{score}(a) \ \text{ for all } a \in T,\ b \notin T ;
--   $$
--
--   these are exactly the committees the rule can produce under some tie-breaking and filling. Given the realised set $\mathrm{Hon}$ of honest candidates and a tolerance $p$, the committee is **honest**, $\mathbb T = H$, if it has at least $\lceil (1-p)\,k\rceil$ honest members. Because the adversary chooses after the types are realised, the event $\mathbb T = H$ is: every admissible committee $T$ satisfies $|T \cap \mathrm{Hon}| \ge \lceil (1-p)\,k \rceil$.
--
--   This is the success event of the single-voter mission; its probability is the voter's objective.
--
--   **Formalization Note** Candidates are `Fin m` and voters `Fin n`, 0-based (the paper's $c_j$ is index $j-1$). The worst-case reading of "filled adversarially" and "broken adversarially" is encoded by quantifying over all admissible committees; the adversary sees the types (proof of Proposition 5, p. 46). The threshold is the integer ceiling `Int.ceil` compared with the integer cast of the cardinality. The cap $|\mathcal C_v| \le t$ of Definition 2 is not part of the definitions. This module defines only the scores (`score`, `singleScore`); the admissible committees and the event $\mathbb T = H$ are `CommitteeVoting.ExpConv.Admissible` and `CommitteeVoting.ExpConv.IsHonestOutcome` of the shared module `Def_CommitteeVoting_ExpConv_Committee`, which this module imports and the success probability uses.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 8, Definition 1 (1); p. 9, Definition 2; pp. 10–11, Definition 3

import Mathlib
import Definitions.Def_CommitteeVoting_ExpConv_Committee

namespace CommitteeVoting.SingleVoter

/-- Approval score (Definition 1, (1), p. 8): with `n` voters, voter `i` approving the set
`ballot i` of the `m` candidates, the score of candidate `j` is the number of voters approving it,
`score(j) = |{i : j ∈ ballot i}|`. Candidates and voters are 0-based (the paper's `c_j` is index `j` minus one). -/
def score {n m : ℕ} (ballot : Fin n → Finset (Fin m)) (j : Fin m) : ℕ :=
  (Finset.univ.filter fun i => j ∈ ballot i).card

/-- The scores produced by a single voter (`n = 1`) who approves the set `C`: candidate `j` scores
`1` if `j ∈ C` and `0` otherwise. -/
def singleScore {m : ℕ} (C : Finset (Fin m)) : Fin m → ℕ :=
  score (fun _ : Fin 1 => C)

end CommitteeVoting.SingleVoter


