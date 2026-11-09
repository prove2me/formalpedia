-- Prove2me | Definitions.Def_HypClass1_codeg
-- name    : HypClass1_codeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:55.215338+00:00
-- url     : https://prove2.me/theorems/e1411b27-b8ff-490f-aec1-55fb7e346055
-- title:
--   Codegree $\deg_H(u,v)$
-- statement:
--   For a set $H$ of edges and vertices $u, v$, the **codegree** of the pair is the number of edges containing both,
--   $$
--   \deg_H(u, v) = |\{e \in H : u \in e,\ v \in e\}|.
--   $$
--   Codegree conditions (concentrated or bounded) are the pseudorandomness hypotheses of the whole paper.
--
--   **Formalization Note** Defined for every pair; every statement of the mission quantifies over distinct $u \ne v$.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1 p.2, Definition 4.4 (B1) p.10

import Mathlib

namespace HypClass1

/-- **Codegree** `deg_H(u, v)`: the number of edges of `H` containing both vertices `u` and `v`.
Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1 p.2 ("the maximum deg_H(u, v)"), Definition 4.4 (B1) p.10.

**Formalization Note.** Defined for every pair `u, v`; every statement of the mission that uses it
quantifies over distinct `u ≠ v`, as the paper's "pair {u, v}" does. -/
def codeg {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (u v : V) : ℕ :=
  (H.filter (fun e => u ∈ e ∧ v ∈ e)).card

end HypClass1


