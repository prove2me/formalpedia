-- Prove2me | Definitions.Def_BollobasChromatic_Main_Setting
-- name    : BollobasChromatic_Main_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:53:25.799039+00:00
-- url     : https://prove2.me/theorems/b05f2571-688d-441d-8180-fc3a2d496941
-- title:
--   §0–§2, pp. 49–53 — the random graph G(n,p), 'almost every', E(n,r), the packing numbers X and X', s₀ and s₁
-- statement:
--   This file fixes the objects of B. Bollobás, *The chromatic number of random graphs* (1988).
--
--   **The random graph.** Let $n\ge 0$, let $V=[n]$ be a set of $n$ vertices and let $N=\binom n2$. For a real $p$, the random graph $G_p=G_{n,p}$ chooses each of the $N$ pairs of vertices as an edge independently with probability $p$. A fixed graph $G$ on $V$ with $e(G)$ edges therefore has probability
--   $$
--   \mathbb P(G_p=G)=p^{e(G)}(1-p)^{N-e(G)} .
--   $$
--   For a property $P$ of graphs on $V$ we write $\mathbb P(G_p \text{ has } P)=\sum_{G\,:\,P(G)}\mathbb P(G_p=G)$, and for a real function $X$ of graphs we write $\mathbb E(X)=\sum_G \mathbb P(G_p=G)\,X(G)$.
--
--   **Almost every.** For a sequence of properties $P_n$ of graphs on $[n]$, "almost every $G_p$ has $P_n$" means $\mathbb P(G_{n,p}\text{ has }P_n)\to 1$ as $n\to\infty$, with $p$ fixed.
--
--   **Expected clique counts.** $E(n,r)=\binom nr p^{\binom r2}$ is the expected number of complete $r$-graphs ($r$-cliques) in $G_{n,p}$; with $q=1-p$ in place of $p$, $E_q(n,r)=\binom nr q^{\binom r2}$.
--
--   **Packing numbers.** For a graph $G$ and $r\ge 0$:
--   1. $X(G)$ is the maximal number of pairwise edge-disjoint $K^r$ subgraphs of $G$; two $r$-cliques share no edge exactly when they have at most one common vertex;
--   2. $X'(G)$ is the number of $K^r$ subgraphs of $G$ that share no edge with any other $K^r$ subgraph of $G$;
--   3. $W=[r]$ is the set of the first $r$ vertices, and $Z_l(G)$ is the number of $K^r$ subgraphs of $G$ having exactly $l$ vertices in $W$.
--
--   **The clique sizes $s_0$, $s_1$.** For $0<p<1$ put $q=1-p$ and $d=1/q$. Then
--   $$
--   s_0=\bigl[\,2\log_d n-\log_d\log_d n+2\log_d(e/2)+1\,\bigr],\qquad s_1=s_0-\lfloor 5\log_d\log n\rfloor ,
--   $$
--   where $[x]$ and $\lfloor x\rfloor$ denote the integer part and $\log$ is the natural logarithm.
--
--   These are the objects in terms of which Theorem 2, Corollary 3 and Theorem 4 of the paper, and the displays of their proofs, are stated.
--
--   **Formalization Note** Vertices are `Fin n`, graphs are `SimpleGraph (Fin n)`. Probabilities and expectations in $G(n,p)$ are finite sums over all graphs on `Fin n`; the subtraction $N-e(G)$ is in $\mathbb N$ and exact, because $e(G)\le\binom n2$. "Almost every" is the limit statement `Tendsto … atTop (𝓝 1)`. $X$ is the largest cardinality of a family of $r$-cliques that pairwise meet in at most one vertex. $s_0$ and $s_1$ are integers (`Int.floor`); for small $n$ the logarithms take Lean's junk values, which no statement of the mission depends on since every statement is asymptotic.
-- source:
--   Bollobás, The chromatic number of random graphs, Combinatorica 8 (1988), pp. 49–53: §0 p. 49 (model); §1 p. 50 (Y_r, E(n,r)); proof of Theorem 2 p. 51 (X, X', K_0, A, Z_l); Theorem 4 p. 52 (s_0); proof of Theorem 4 p. 53 (s_1)

import Mathlib

namespace BollobasChromatic.Main

open Filter Topology
open scoped Classical

/-- The probability of a single graph `G` on `[n] = Fin n` in the random graph `G(n,p)`:
each of the `N = C(n,2)` pairs is an edge independently with probability `p`, so
`P(G_p = G) = p ^ e(G) * (1 - p) ^ (N - e(G))`. The natural-number subtraction is exact
because `e(G) ≤ C(n,2)`. -/
noncomputable def gnpWeight (n : ℕ) (p : ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  p ^ G.edgeFinset.card * (1 - p) ^ (n.choose 2 - G.edgeFinset.card)

/-- `P(G_p has property P)` in `G(n,p)`: a finite sum of the graph weights. -/
noncomputable def gnpProb (n : ℕ) (p : ℝ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  ∑ G : SimpleGraph (Fin n), if P G then gnpWeight n p G else 0

/-- The expectation `E(X(G_p))` of a real random variable `X` on `G(n,p)`. -/
noncomputable def gnpExp (n : ℕ) (p : ℝ) (X : SimpleGraph (Fin n) → ℝ) : ℝ :=
  ∑ G : SimpleGraph (Fin n), gnpWeight n p G * X G

/-- "Almost every `G_p` has property `P n`": `P(G_p has P n) → 1` as `n → ∞`. -/
def AlmostEvery (p : ℝ) (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) : Prop :=
  Tendsto (fun n => gnpProb n p (P n)) atTop (𝓝 1)

/-- `E(n,r) = C(n,r) p ^ C(r,2)`, the expected number of complete `r`-graphs in `G(n,p)`.
With `1 - p` in place of `p` it is `E_q(n,r)`. -/
noncomputable def expCliques (n : ℕ) (p : ℝ) (r : ℕ) : ℝ :=
  (n.choose r : ℝ) * p ^ r.choose 2

/-- `X(G)`: the maximal number of edge-disjoint `K^r` subgraphs of `G`. Two `r`-cliques
share no edge iff they have at most one common vertex. -/
noncomputable def packingNum {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ :=
  ((G.cliqueFinset r).powerset.filter
    (fun F : Finset (Finset (Fin n)) =>
      (↑F : Set (Finset (Fin n))).Pairwise (fun s t => (s ∩ t).card ≤ 1))).sup
    Finset.card

/-- `X'(G)`: the number of `K^r` subgraphs of `G` sharing no edge with another `K^r`. -/
noncomputable def isolatedCliqueCount {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ :=
  ((G.cliqueFinset r).filter
    (fun s => ∀ t ∈ G.cliqueFinset r, t ≠ s → (s ∩ t).card ≤ 1)).card

/-- `W = [r]`, the first `r` vertices of `[n]` (the vertex set of `K_0`). -/
def baseSet (n r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v.val < r)

/-- `Z_l(G)`: the number of `K^r` subgraphs of `G` having exactly `l` vertices in `W = [r]`. -/
noncomputable def cliquesMeeting {n : ℕ} (G : SimpleGraph (Fin n)) (r l : ℕ) : ℕ :=
  ((G.cliqueFinset r).filter (fun t => (t ∩ baseSet n r).card = l)).card

/-- `s₀ = [2 log_d n − log_d log_d n + 2 log_d (e/2) + 1]` with `d = 1/(1 − p)`
(Theorem 4); `[·]` is the integer part. -/
noncomputable def s0 (p : ℝ) (n : ℕ) : ℤ :=
  ⌊2 * Real.logb (1 / (1 - p)) n - Real.logb (1 / (1 - p)) (Real.logb (1 / (1 - p)) n)
    + 2 * Real.logb (1 / (1 - p)) (Real.exp 1 / 2) + 1⌋

/-- `s₁ = s₀ − ⌊5 log_d log n⌋` with `d = 1/(1 − p)` (proof of Theorem 4). -/
noncomputable def s1 (p : ℝ) (n : ℕ) : ℤ :=
  s0 p n - ⌊5 * Real.logb (1 / (1 - p)) (Real.log n)⌋

end BollobasChromatic.Main


