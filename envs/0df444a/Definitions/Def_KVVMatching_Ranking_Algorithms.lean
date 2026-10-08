-- Prove2me | Definitions.Def_KVVMatching_Ranking_Algorithms
-- name    : KVVMatching_Ranking_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:41:34.70512+00:00
-- url     : https://prove2.me/theorems/110b5de7-1285-4c86-97b8-f20638b91534
-- title:
--   RANKING, its rows-arrive dual, EARLY, and uniform expectations
-- statement:
--   **RANKING** assigns a uniformly random priority order to the boys. Girls arrive in the fixed order $n,n-1,\ldots,1$ and each takes the highest-priority adjacent unmatched boy, if one exists. In the dual picture, rows arrive in a specified order and each takes the highest-ranked eligible column, with column $n$ highest. **EARLY** uses that rows-arrive rule but declines row $i$ whenever column $i$ was already matched by EARLY itself.
--
--   $$\mathbb E|M_{\mathrm{RANKING}}|=\frac{1}{n!}\sum_{\pi\in S_n}|M_{\mathrm{RANKING}}(B,\pi)|.$$
--
--   The uniform finite averages make the paper's performance quantities available for the goal and milestones. For a matching $M$, $D(M)$ is the set of indices whose row and column are both covered.
--
--   **Formalization Note** Indices in Lean start at zero; column $n-1$ has the highest rank. The girls-arrive matching is returned as (boy, girl) pairs. Both expectation definitions average over all $n!$ permutations, including the unique empty permutation when $n=0$.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, pp. 352–354, Problem Statement, RANKING algorithm, Duality Principle, and EARLY paragraph before Lemma 5

import Definitions.Def_KVVMatching_Ranking_GreedyRun

namespace KVVMatching.Ranking

/-- The paper's RANKING matching: girls arrive in reverse index order, and
`boyRank r` is the boy of priority `r`, with priority zero highest. -/
noncomputable def rankingMatching {n : ℕ} (adj : Fin n → Fin n → Prop)
    (boyRank : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  (greedyRun (fun g b => adj b g) Fin.revPerm boyRank (fun _ _ _ => false)).image Prod.swap

/-- The dual rows-arrive version of RANKING, with the largest column index highest. -/
noncomputable def rowRankingMatching {n : ℕ} (adj : Fin n → Fin n → Prop)
    (rowOrder : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  greedyRun adj rowOrder Fin.revPerm (fun _ _ _ => false)

/-- EARLY: decline row `i` if column `i` was already matched by this run. -/
noncomputable def earlyMatching {n : ℕ} (adj : Fin n → Fin n → Prop)
    (rowOrder : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) := by
  classical
  exact greedyRun adj rowOrder Fin.revPerm
    (fun _ M i => decide (secondMatched M i))

/-- Uniform expected cardinality over the random ranking of boys. -/
noncomputable def rankingExpectation {n : ℕ} (adj : Fin n → Fin n → Prop) : ℝ :=
  ((n.factorial : ℝ)⁻¹) *
    ∑ π : Equiv.Perm (Fin n), ((rankingMatching adj π).card : ℝ)

/-- Uniform expected cardinality in the dual rows-arrive picture. -/
noncomputable def rowRankingExpectation {n : ℕ} (adj : Fin n → Fin n → Prop) : ℝ :=
  ((n.factorial : ℝ)⁻¹) *
    ∑ σ : Equiv.Perm (Fin n), ((rowRankingMatching adj σ).card : ℝ)

/-- Uniform expected cardinality for EARLY over row arrival orders. -/
noncomputable def earlyExpectation {n : ℕ} (adj : Fin n → Fin n → Prop) : ℝ :=
  ((n.factorial : ℝ)⁻¹) *
    ∑ σ : Equiv.Perm (Fin n), ((earlyMatching adj σ).card : ℝ)

/-- Indices whose row and column are both covered by a matching. -/
noncomputable def doubleCovered {n : ℕ} (M : Finset (Fin n × Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => firstMatched M i ∧ secondMatched M i)

end KVVMatching.Ranking


