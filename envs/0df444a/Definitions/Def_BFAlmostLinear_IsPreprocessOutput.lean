-- Prove2me | Definitions.Def_BFAlmostLinear_IsPreprocessOutput
-- name    : BFAlmostLinear_IsPreprocessOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:26.43855+00:00
-- url     : https://prove2.me/theorems/33b4c675-1928-4ab2-bf67-3a6fcd047f4b
-- title:
--   Correct output of the preprocessing of Lemma 1.2
-- statement:
--   Let $G$ be a directed multigraph on $V=\{0,\dots,n-1\}$ with $m$ arcs and real weights $w$, and let $k$ be its number of **negative vertices** (tails of arcs of negative weight). A machine state holds a correct output of Lemma 1.2 if it holds a weighted graph $G'$ on $V'=\{0,\dots,n+2k-1\}\supseteq V$ such that
--
--   1. $d^h_{G'}(s,t)=d^h_G(s,t)$ for all $s,t\in V$ and every hop bound $h$, where hops are arcs of negative weight;
--   2. every vertex of $G'$ is incident to at most one arc of negative weight; the tail of such an arc has no other outgoing arc and its head no other incoming arc;
--   3. $G'$ has exactly $k$ negative vertices.
--
--   **Output layout.** Integer cell $-1$ holds the number $m'$ of arcs of $G'$; for $j<m'$, integer cells $-2-2j$ and $-3-2j$ hold the tail and head of arc $j$, and real cell $-1-j$ its weight.
--
--   **Formalization Note** $V$ is the first $n$ vertices of $V'$, so $V'\supseteq V$ and $|V'|=|V|+2k$ hold by the type. Item 2 is invariant (I1) for a graph without auxiliary arcs. The construction on p.2 is not hard-coded: any $G'$ with items 1–3 is a correct output.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Lemma 1.2, p.2

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph_I1

namespace BFAlmostLinear

open AtomicDynRouting.ResidenceTime

/-- The state `σ` holds a graph `G′` as Lemma 1.2, p.2 asks, for the input `(G, w)` with `k` negative vertices.

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Lemma 1.2, p.2.

**Formalization Note.**
* **Output layout.** Integer cell `−1` is the number `m′` of arcs. For `j < m′`, integer cell `−2 − 2j` is the
  tail of arc `j`, integer cell `−3 − 2j` is its head, and real cell `−1 − j` is its weight.
* `V′ = Fin (n + 2k)`, and `V` embeds as the first `n` vertices. So `V′ ⊇ V` and `|V′| = |V| + 2k` are in the type.
* Negative means `w < 0` in both graphs. The construction on p.2 is not hard-coded: any `G′` with items 1–3
  is an output. -/
def IsPreprocessOutput {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ)
    (σ : Machine.State) : Prop :=
  let G₀ := WGraph.ofWeights G w
  let k := G₀.negVertices.card
  ∃ (m' : ℕ) (G' : Network (Fin (n + 2 * k)) (Fin m')) (w' : Fin m' → ℝ),
    σ.imem (-1) = (m' : ℤ) ∧
    (∀ j : Fin m',
      σ.imem (-2 - 2 * ((j : ℕ) : ℤ)) = ((G'.tail j : ℕ) : ℤ) ∧
      σ.imem (-3 - 2 * ((j : ℕ) : ℤ)) = ((G'.head j : ℕ) : ℤ) ∧
      σ.rmem (-1 - ((j : ℕ) : ℤ)) = w' j) ∧
    (∀ (s t : Fin n) (h : ℕ),
      (WGraph.ofWeights G' w').dH h (Fin.castAdd (2 * k) s) (Fin.castAdd (2 * k) t) =
        G₀.dH h s t) ∧
    (WGraph.ofWeights G' w').I1 ∧
    (WGraph.ofWeights G' w').negVertices.card = k

end BFAlmostLinear


