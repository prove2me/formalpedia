-- Prove2me | Definitions.Def_HypClass1_Supplement_binomProbK
-- name    : HypClass1_Supplement_binomProbK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:01:51.791247+00:00
-- url     : https://prove2.me/theorems/ba113bea-5344-45bb-a15a-9ad3e92e4cad
-- title:
--   Binomial random $k$-graph $H^{(k)}_{n,p}$
-- statement:
--   Fix integers $k$ and $n$ and a number $p$. The **binomial random $k$-graph** $H^{(k)}_{n,p}$ is the random hypergraph on the vertex set $[n]$ obtained by keeping each edge of the complete $k$-graph $K^{(k)}_n$ (all $k$-element subsets of $[n]$) independently with probability $p$. For a property $E$ of $k$-graphs on $[n]$,
--   $$
--   \mathbb P\big[E(H^{(k)}_{n,p})\big]=\sum_{H\subseteq K^{(k)}_n} [E(H)]\; p^{|H|}(1-p)^{\binom nk-|H|}.
--   $$
--
--   This is the probability space of Appendix C, where the degree gap of the maximum-degree vertex is proved for every uniformity $k\ge 3$; at $k=3$ it is the mission's $H^{(3)}_{n,p}$.
--
--   **Formalization Note** The vertex set is `Fin n`. The sum is the mission's published random-subset probability `HypClass1.randSubProb` on the ground set of all $k$-subsets with constant weight $p$; at $k=3$ the definition agrees definitionally with the published `HypClass1.binomProb`.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1, p.2 (definition of H^{(k)}_{n,p}); Appendix C, p.63

import Mathlib
import Definitions.Def_HypClass1_randSubProb

namespace HypClass1.Supplement

/-- **Binomial random `k`-graph** `H^{(k)}_{n,p}`: `binomProbK k n p E` is the probability that
`H ∼ H^{(k)}_{n,p}` has property `E`. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform
Hypergraph is Class 1*, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…),
§1 p.2: "the binomial random hypergraph H^{(k)}_{n,p}, i.e., the hypergraph obtained by selecting each
edge of the complete k-graph on n vertices independently at random with probability p"; Appendix C,
p.63 ("the binomial random k-uniform hypergraph H^{(k)}_{n,p} with k ≥ 3").

**Formalization Note.** Vertex set `Fin n`; the ground set is the complete `k`-graph, all `k`-element
subsets of `Fin n`; the probability is the finite sum
`Σ_{H ⊆ K^{(k)}_n} [E(H)] p^{|H|} (1 − p)^{C(n,k) − |H|}` (the published `HypClass1.randSubProb` with
constant weight `p`). At `k = 3` it is definitionally the published `HypClass1.binomProb`. -/
noncomputable def binomProbK (k n : ℕ) (p : ℝ) (E : Finset (Finset (Fin n)) → Prop) : ℝ :=
  HypClass1.randSubProb ((Finset.univ : Finset (Fin n)).powersetCard k) (fun _ => p) E

end HypClass1.Supplement


