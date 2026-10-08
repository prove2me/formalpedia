-- Prove2me | Definitions.Def_KVVMatching_UpperBound_OnlineAlg
-- name    : KVVMatching_UpperBound_OnlineAlg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:48:22.191785+00:00
-- url     : https://prove2.me/theorems/c692eec4-dc87-4064-a378-92d6ac04f082
-- title:
--   On-line matching algorithms and matching size
-- statement:
--   A deterministic on-line algorithm receives the columns of an $n\times n$ bipartite graph in the order $n,n-1,\ldots,1$. On each arrival it sees the neighborhoods of the columns received so far, including the current one, and chooses one row or declines the match. A proposed row is matched only if it is adjacent to the current column and has not already been matched. The matching size is the number of matched rows after all columns have arrived.
--
--   A randomized algorithm is a probability distribution $A$ over these deterministic rules. Its expected size on a fixed graph $G$ is
--
--   $$\mathbb E_A[|M(G)|]=\sum_a A(a)|M_a(G)|.$$
--
--   A deterministic rule is greedy if, on every input and at every arrival with at least one eligible row, it chooses an eligible row. This model supports both the greedy hypothesis of Lemma 13 and the unrestricted algorithm class of Lemma 14 and Theorem 2.
--
--   **Formalization Note** The finite distribution over deterministic rules represents all internal coin flips, including fresh choices at successive steps. An unrevealed future column appears as absent from the history.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 352, Section 2 (Problem Statement); p. 357, Lemma 13

import Mathlib
import Definitions.Def_KVVMatching_UpperBound_Graph

namespace KVVMatching.UpperBound

/-- At arrival `k`, entries through `k` are the revealed row-neighbourhoods in arrival order.
Later entries are `none`, so an algorithm cannot inspect later columns. -/
abbrev History (n : ℕ) := Fin n → Option (Finset (Fin n))

/-- A deterministic online matching rule. Invalid or already used proposals are declined. -/
abbrev DetAlg (n : ℕ) := Fin n → History n → Option (Fin n)

/-- All and only the columns revealed through arrival `k`, from highest to lowest index. -/
noncomputable def revealedHistory {n : ℕ} (G : Graph n) (k : Fin n) : History n := by
  classical
  exact fun j =>
    if j ≤ k then
      some (Finset.univ.filter (fun r => (r, Fin.rev j) ∈ G))
    else none

/-- Rows adjacent to the current column and not yet used. -/
noncomputable def eligibleRows {n : ℕ} (G : Graph n) (S : Finset (Fin n))
    (c : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun r => (r, c) ∈ G ∧ r ∉ S)

/-- Matched rows after `k` arrivals, with columns arriving in reverse index order. -/
noncomputable def matchedRows {n : ℕ} (G : Graph n) (a : DetAlg n) : ℕ → Finset (Fin n)
  | 0 => ∅
  | k + 1 =>
      let S := matchedRows G a k
      if h : k < n then
        let j : Fin n := ⟨k, h⟩
        match a j (revealedHistory G j) with
        | none => S
        | some r =>
            if r ∈ eligibleRows G S (Fin.rev j) then insert r S else S
      else S

/-- Cardinality of the matching produced by the deterministic algorithm. -/
noncomputable def matchingSize {n : ℕ} (G : Graph n) (a : DetAlg n) : ℕ :=
  (matchedRows G a n).card

/-- Every offered column is matched when some unused adjacent row exists. -/
def IsGreedy {n : ℕ} (a : DetAlg n) : Prop :=
  ∀ (G : Graph n) (k : Fin n),
    (eligibleRows G (matchedRows G a k.val) (Fin.rev k)).Nonempty →
      ∃ r ∈ eligibleRows G (matchedRows G a k.val) (Fin.rev k),
        a k (revealedHistory G k) = some r

/-- A randomized online algorithm is a mixture of deterministic online rules. -/
abbrev RandomAlg (n : ℕ) := PMF (DetAlg n)

/-- Expected matching size under the algorithm's internal randomness. -/
noncomputable def expectedSize {n : ℕ} (G : Graph n) (A : RandomAlg n) : ℝ := by
  classical
  exact ∑ a : DetAlg n, (A a).toReal * (matchingSize G a : ℝ)

end KVVMatching.UpperBound


