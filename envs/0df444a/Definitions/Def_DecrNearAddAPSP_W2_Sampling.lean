-- Prove2me | Definitions.Def_DecrNearAddAPSP_W2_Sampling
-- name    : DecrNearAddAPSP_W2_Sampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:07:46.879656+00:00
-- url     : https://prove2.me/theorems/44e5e970-b296-498d-bcdd-16afc1c0ab0d
-- title:
--   The Bernoulli(q) sample S, edges ever in E_S(u) over a deletion sequence, and distance updates between u and S
-- statement:
--   Let $G_0,G_1,\dots,G_T$ be the graphs produced from $G_0$ by a sequence of $T$ legal **edge deletions** (a **deletion sequence**).
--
--   **The sample.** "$S\subseteq V$ is formed by selecting each vertex independently with probability $q$": the set $S$ has probability $q^{|S|}(1-q)^{n-|S|}$, and the expectation of a quantity $X(S)$ is
--   $$
--   \mathbb E_S[X]=\sum_{S\subseteq V}q^{|S|}(1-q)^{n-|S|}\,X(S).
--   $$
--
--   **Edges ever in $E_S(u)$.** With $E_{S,t}(u)$ the set $E_S(u)$ of $G_t$, the number of edges ever in $E_S(u)$ is the number of distinct $v$ such that $(u,v)\in E_{S,t}(u)$ for some $0\le t\le T$, the edges present at time $0$ included.
--
--   **Distance updates.** The number of distance updates between $u$ and $S$ is the number of $t<T$ with $\delta_{G_{t+1}}(u,S)\ne\delta_{G_t}(u,S)$. Under deletions distances never decrease, so this is the number of times $\delta(u,S)$ increases.
--
--   These are the quantities of Lemma 5.3 and Corollary 5.4 (pp. 26–27).
--
--   **Formalization Note** The expectation over $S$ is a finite sum over `Finset (Fin n)`, so no measurability or integrability question arises.
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), pp. 26–27, §5.1, Lemma 5.3 and Corollary 5.4

import Mathlib
import Definitions.Def_DecrNearAddAPSP_W2_Graphs
import Definitions.Def_DecrNearAddAPSP_W2_Dynamic

namespace DecrNearAddAPSP.W2

/-! # The sampled set `S` and the edges ever in `E_S(u)` over a deletion sequence

Koveshi, Roditty, Sapir, *First Near-Additive All-Pairs Approximate Shortest Paths in Decremental
Weighted Graphs*, arXiv:2611.04635 (PDF sha256 6bb2b230…), §5.1, pp. 26–27 (PDF 28–29), Lemma 5.3
and Corollary 5.4.

**Formalization Note.**
* "`S` is formed by selecting each vertex independently with probability `q`": the law of `S` gives
  the finite set `S ⊆ Fin n` probability `q^{|S|}(1 − q)^{n − |S|}`, and an expectation over `S` is
  the finite sum `Σ_S q^{|S|}(1 − q)^{n − |S|}·X(S)`.
* A deletion sequence is a list of legal edge deletions; `G_0, …, G_T` are the graphs it produces
  (`T` = its length).
* `E_{S,t}(u)` is the set `E_S(u)` of `G_t`, recorded by the other endpoints `v`. The edges ever in
  `E_S(u)` are the distinct `v` with `(u, v) ∈ E_{S,t}(u)` for some `0 ≤ t ≤ T` (initial members
  included).
* The number of distance updates between `u` and `S` is the number of `t < T` with
  `δ_{t+1}(u, S) ≠ δ_t(u, S)`. -/

/-- A legal deletion sequence from `G`: every update deletes an edge present in the graph it
meets. -/
def IsDelSeq {n : ℕ} : WGraph (Fin n) → List (Upd n) → Prop
  | _, [] => True
  | G, .del u v :: σ => G.adj.Adj u v ∧ IsDelSeq ((Upd.del u v).apply G) σ
  | _, .inc _ _ _ :: _ => False

/-- The probability `q^{|S|}(1 − q)^{n − |S|}` that independent sampling with probability `q`
selects exactly the set `S ⊆ Fin n`. -/
noncomputable def sampleProb {n : ℕ} (q : ℝ) (S : Finset (Fin n)) : ℝ :=
  q ^ S.card * (1 - q) ^ (n - S.card)

/-- The expectation `E_S[X(S)] = Σ_S q^{|S|}(1 − q)^{n − |S|}·X(S)` over the sampled set `S`. -/
noncomputable def sampleExp {n : ℕ} (q : ℝ) (X : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), sampleProb q S * X S

open Classical in
/-- The number of distinct edges `(u, v)` that belong to `E_S(u)` of `G_t` for some time
`0 ≤ t ≤ |σ|`. -/
noncomputable def everInHier {n : ℕ} (G₀ : WGraph (Fin n)) (σ : List (Upd n))
    (S : Finset (Fin n)) (u : Fin n) : ℕ :=
  (Finset.univ.filter fun v : Fin n =>
    ∃ t ≤ σ.length, s(u, v) ∈ (graphAt G₀ σ t).hierEdgesAt S u).card

open Classical in
/-- The number of distance updates between `u` and `S`: the number of times `t < |σ|` with
`δ_{t+1}(u, S) ≠ δ_t(u, S)`. -/
noncomputable def distUpdates {n : ℕ} (G₀ : WGraph (Fin n)) (σ : List (Upd n))
    (S : Finset (Fin n)) (u : Fin n) : ℕ :=
  ((Finset.range σ.length).filter fun t =>
    (graphAt G₀ σ (t + 1)).distTo u S ≠ (graphAt G₀ σ t).distTo u S).card

end DecrNearAddAPSP.W2


