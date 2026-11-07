-- Prove2me | Definitions.Def_RGMISFast_Y
-- name    : RGMISFast_Y
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:35.329205+00:00
-- url     : https://prove2.me/theorems/f4113170-08e5-4367-ba95-ffd085828411
-- title:
--   Counts $Y_k(t)$, $N_k(A;G_a)$ and $\sum_W d_s(W)$
-- statement:
--   Let $G$ be a finite simple graph with root $u^*$ and ranks $r$.
--
--   1. $Y_k(t)$ is the number of root-connected sets active at time $t$ with exactly $k$ vertices other than $u^*$.
--   2. For a vertex set $A$, $N_k(A;G_a)$ is the number of $k$-sets $W\subseteq V(G)\setminus A$ attached to $A$ for which $A\cup W$ is active at time $a$.
--   3. For the proof of Lemma 5.2: the sets $W\not\ni u^*$ with $|W|=k$ for which $\{u^*\}\cup W$ is counted by $Y_k(s)$, and
--   $$
--   \sum_W d_s(W),
--   $$
--   where $d_s(W)$ is $d(W)$ computed in the active graph $G_s$.
--
--   These counts are the random variables of the expectation bounds of §5.
--
--   **Formalization Note** $d_s(W)$ is computed in the graph keeping the edges of $G$ between vertices active at $s$, so it counts the active vertices other than $u^*$ that lie in $W$ or are adjacent to $\{u^*\}\cup W$.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), §5.1, p.18 (PDF p.20) (Y_k(t)); Lemma 5.3, p.20 (PDF p.22) (N_k(A; G_a)); Proof of Lemma 5.2, p.19 (PDF p.21) (d_s(W))

import Mathlib
import Definitions.Def_RGMISFast_tau
import Definitions.Def_RGMISFast_IsRootConnected

set_option autoImplicit false

namespace RGMISFast

open Classical in
/-- `Y_k(t)` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast
at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), §5.1, p.18): "the number of
root-connected sets active at time t with exactly k vertices other than u∗", i.e. the number of
root-connected `A` with `|A| = k + 1` and `t ≤ τ(v)` for all `v ∈ A`. -/
noncomputable def Y {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : V) (k : ℕ) (t : ℝ) (r : V → ℝ) : ℕ :=
  ((Finset.univ : Finset (Finset V)).filter
    (fun A => IsRootConnected G u A ∧ A.card = k + 1 ∧ ActiveAt G r t A)).card

open Classical in
/-- `N_k(A; G_a)` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is
Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), Lemma 5.3, p.20): "the
number of k-sets W ⊆ V(G) \ A attached to A for which A ∪ W is active at time a".

**Formalization Note** Attachment is taken in `G`; since `A ∪ W` is required to be active at `a`,
its induced subgraph in `G_a` is the one in `G`. -/
noncomputable def Ncount {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) (k : ℕ) (a : ℝ) (r : V → ℝ) : ℕ :=
  ((Finset.univ : Finset (Finset V)).filter
    (fun W => W.card = k ∧ IsAttached G A W ∧ ActiveAt G r a (A ∪ W))).card

open Classical in
/-- The `k`-sets `W ∌ u` for which `{u∗} ∪ W` is counted by `Y_k(s)` (root-connected and active at
`s`); the range of the sums in eq. (20) (Dalirrooyfard, Makarychev, Mitrović, Ramachandran,
*Randomized Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256
e93cdfec…), Proof of Lemma 5.2, p.19). -/
noncomputable def countedW {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ) (r : V → ℝ) : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter
    (fun W => u ∉ W ∧ W.card = k ∧ IsRootConnected G u (insert u W) ∧
      ActiveAt G r s (insert u W))

/-- `Σ_W d_s(W)` of eq. (20) (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized
Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), Proof of
Lemma 5.2, p.19): the sum over the sets `W` counted by `Y_k(s)` of `d_s(W)`, "the quantity d(W)
from Lemma 5.1 computed in G_s".

**Formalization Note** `G_s` is represented by `restrictTo G {x | s ≤ τ(x)}`, the graph keeping
the edges between active vertices; `d` computed there counts the active vertices `x ≠ u∗` that lie
in `W` or are adjacent to `{u∗} ∪ W`. -/
noncomputable def dsSum {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ) (r : V → ℝ) : ℕ :=
  ∑ W ∈ countedW G u k s r, dW (restrictTo G {x | s ≤ tau G r x}) u W

end RGMISFast


