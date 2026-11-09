-- Prove2me | Definitions.Def_HypClass1_binomProb
-- name    : HypClass1_binomProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:24:48.662292+00:00
-- url     : https://prove2.me/theorems/1665682e-f3ce-44be-96b2-44f7548f1a90
-- title:
--   Binomial random 3-graph $H^{(3)}_{n,p}$
-- statement:
--   The **binomial random 3-graph** $H^{(3)}_{n,p}$ is obtained by selecting each edge of the complete 3-graph $K^{(3)}_n$ on $n$ vertices independently with probability $p$. For a property $E$ of 3-graphs on $[n]$,
--   $$
--   \mathbb P_{n,p}[E] = \sum_{H \subseteq K^{(3)}_n} [E(H)]\, p^{|H|} (1-p)^{\binom n3 - |H|}.
--   $$
--
--   **Formalization Note** Vertex set `Fin n`; this is the random inhomogeneous subset of $K^{(3)}_n$ with constant weight $p$.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1 p.2, §4 p.10

import Mathlib
import Definitions.Def_HypClass1_K3
import Definitions.Def_HypClass1_randSubProb

namespace HypClass1

/-- **Binomial random 3-graph** `H^{(3)}_{n,p}`: `binomProb n p E` is the probability that
`H ∼ H^{(3)}_{n,p}` has property `E`. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1 p.2: "the binomial random hypergraph H^{(k)}_{n,p}, i.e.,
the hypergraph obtained by selecting each edge of the complete k-graph on n vertices independently
at random with probability p"; §4 p.10: "`H^{(3)}_{n,p} = (K^{(3)}_n)_p`".

**Formalization Note.** Vertex set `Fin n`; the probability is the finite sum
`Σ_{H ⊆ K^{(3)}_n} [E(H)] p^{|H|} (1 − p)^{C(n,3) − |H|}` (`randSubProb` with constant weight `p`). -/
noncomputable def binomProb (n : ℕ) (p : ℝ) (E : Finset (Finset (Fin n)) → Prop) : ℝ :=
  randSubProb (K3 (Fin n)) (fun _ => p) E

end HypClass1


