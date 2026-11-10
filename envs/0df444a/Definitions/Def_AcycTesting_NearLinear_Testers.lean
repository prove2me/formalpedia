-- Prove2me | Definitions.Def_AcycTesting_NearLinear_Testers
-- name    : AcycTesting_NearLinear_Testers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:35:00.804495+00:00
-- url     : https://prove2.me/theorems/2c17c962-3f9b-497e-b57a-7d00e139f12f
-- title:
--   Whole-vertex and indexed oracles; randomized adaptive two-sided ε-testers for acyclicity on 𝒢(n, d)
-- statement:
--   Let $G$ be a digraph on $[n]$. The *whole-vertex oracle* answers a query $u\in[n]$ with the set $N^+(u)$ of outneighbours of $u$ (the empty set for a sink). The *indexed oracle* (bounded-degree incidence lists, unidirectional model) for the degree bound $d$ answers a query $(u,i)$ with $u\in[n]$ and $i\in[d]$ by the $i$-th outneighbour of $u$, the outneighbours being listed in increasing ID order, or by the symbol $\perp$ if $u$ has fewer than $i$ outneighbours.
--
--   A randomized adaptive tester with at most $q$ queries is an arbitrary probability distribution, fixed independently of the input, over adaptive query trees of depth at most $q$: each node either stops with *accept* or *reject*, or asks one query and branches on the answer. Repeated queries are allowed and counted, and the cap $q$ bounds every run. $\Pr[\text{accept on }G]$ is the probability that the sampled tree, run against the oracle of $G$, accepts. This is the published `GraphIsoTesting.FixedGraph.RandomizedTester`.
--
--   Such a tester is a *two-sided $\varepsilon$-tester for acyclicity on $\mathcal G(n,d)$* if for every $G\in\mathcal G(n,d)$:
--   $$G\ \text{acyclic}\ \Rightarrow\ \Pr[\text{accept on }G]\ge \tfrac23,\qquad \mathrm{fas}(G)\ge\varepsilon d n\ \Rightarrow\ \Pr[\text{reject on }G]\ge\tfrac23 .$$
--   Inputs that are neither acyclic nor $\varepsilon$-far, and inputs outside $\mathcal G(n,d)$, carry no requirement.
--
--   **Formalization Note.** Indexed queries are $0$-based: the query `(u, i)` with `i : Fin d` returns the entry at position `i` of the increasingly sorted outneighbour list, or `none` for $\perp$. Accept is the Boolean output `true`; probabilities are `ENNReal`.
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), pp. 1–2 (PDF 4–5), §1, §1.1 and footnote 1; p. 14 (PDF 17), §3.1

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_QueryModel
import Definitions.Def_AcycTesting_NearLinear_Digraphs

namespace AcycTesting.NearLinear

open GraphIsoTesting.FixedGraph

/-- Whole-vertex oracle: a query to `u` returns the set of outneighbours of `u`. -/
def wholeVertexOracle {n : ℕ} (G : OutGraph (Fin n)) : Fin n → Finset (Fin n) :=
  fun u => G u

/-- Indexed (incidence-list) oracle for degree bound `d`: the query `(u, i)` returns the
`i`-th outneighbour of `u` in increasing ID order (`i` counted from `0`), or `none` (`⊥`) if
`u` has at most `i` outneighbours. -/
def indexedOracle {n d : ℕ} (G : OutGraph (Fin n)) : Fin n × Fin d → Option (Fin n) :=
  fun q => ((G q.1).sort (· ≤ ·))[q.2.val]?

/-- A randomized adaptive tester `T` (an input-independent law on query trees with at most
`q` queries) is a two-sided `ε`-tester for acyclicity on `𝒢(n, d)` with respect to the oracle
`oracle`: every acyclic `G ∈ 𝒢(n, d)` is accepted (`true`) with probability at least `2/3`, and
every `G ∈ 𝒢(n, d)` with `fas G ≥ ε d n` is rejected (`false`) with probability at least `2/3`.
Nothing is required on other inputs. -/
def IsTwoSidedTester {n : ℕ} {Q R : Type} {q : ℕ} (oracle : OutGraph (Fin n) → Q → R)
    (d : ℕ) (ε : ℝ) (T : RandomizedTester Q R q) : Prop :=
  ∀ G : OutGraph (Fin n), InClass n d G →
    (IsAcyclic G → (2 / 3 : ENNReal) ≤ outputProbability T (oracle G) true) ∧
    (IsFar ε d G → (2 / 3 : ENNReal) ≤ outputProbability T (oracle G) false)

end AcycTesting.NearLinear


