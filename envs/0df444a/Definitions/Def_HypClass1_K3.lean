-- Prove2me | Definitions.Def_HypClass1_K3
-- name    : HypClass1_K3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:44.337379+00:00
-- url     : https://prove2.me/theorems/cc0aa0d4-ad05-482a-9109-11aef488ef7c
-- title:
--   The complete 3-graph $K^{(3)}_n$
-- statement:
--   Let $V$ be a finite vertex set. The **complete 3-graph** on $V$ is the family of all three-element subsets of $V$,
--   $$
--   K^{(3)}_V = V^{(3)} = \{e \subseteq V : |e| = 3\}.
--   $$
--   A **3-graph** on $V$ is a subset $H \subseteq K^{(3)}_V$; its members are the edges. For $V = [n]$ this is $K^{(3)}_n$, the ground set of the binomial random 3-graph $H^{(3)}_{n,p} = (K^{(3)}_n)_p$.
--
--   **Formalization Note** The vertex set $[n]$ is `Fin n`; a 3-graph is a `Finset (Finset V)` contained in `K3 V`.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1 p.2 and §4 p.10

import Mathlib

namespace HypClass1

/-- **The complete 3-graph** `K^{(3)}_V = V^{(3)}`: all three-element subsets of a finite vertex
set `V`. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1 p.2 ("the complete k-graph on n vertices") and §4 p.10
("`H^{(3)}_{n,p} = (K^{(3)}_n)_p`").

**Formalization Note.** A 3-graph on the vertex set `V` is a `Finset (Finset V)` contained in
`K3 V`, i.e. a set of three-element subsets ("edges"). The paper's vertex set `[n]` is `Fin n`. -/
def K3 (V : Type*) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  (Finset.univ : Finset V).powersetCard 3

end HypClass1


