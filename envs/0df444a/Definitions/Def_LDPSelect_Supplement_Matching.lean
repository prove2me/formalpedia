-- Prove2me | Definitions.Def_LDPSelect_Supplement_Matching
-- name    : LDPSelect_Supplement_Matching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:01:16.756704+00:00
-- url     : https://prove2.me/theorems/1c0d5d10-23a8-4448-a55f-d3f7fb5c2ae9
-- title:
--   The matching family of a graph under edge arrival
-- statement:
--   Let $J$ be a finite simple graph whose edges are the users, arriving in the order $e_1,\dots,e_m$. In **edge-arrival matching** a set of edges is feasible when it is a matching: no two distinct chosen edges share an endpoint. These are exactly the independent sets of the line graph of $J$.
--
--   This family is the constraint in the matching clause of Theorem 3.
--
--   **Formalization Note** The enumeration $e$ is a bijection from `Fin m` onto the edge set of $J$; position $i$ holds edge $e_i$. Theorem 3 quantifies over every enumeration.
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 3, p.2 (pdf p.3); §4, p.9 (pdf p.10)

import Mathlib
import Definitions.Def_LDPSelect_Family

namespace LDPSelect.Supplement

/-!
# The matching family of a graph under edge arrival

Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local
Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 3, p.2; §4, p.9.

**Formalization Note.** The users are the edges of `J`, and `e : Fin m ≃ J.edgeSet` lists them in
arrival order. A set of edges is feasible when it is a matching: two distinct edges share no endpoint.
These are the independent sets of the line graph of `J` (p.9).
-/

open LDPSelect

/-- Edge-arrival matching on `J`: a set of positions is feasible when the edges at those positions are
pairwise vertex-disjoint (Theorem 3, p.2). -/
def matchFam {V : Type*} {m : ℕ} (J : SimpleGraph V) (e : Fin m ≃ J.edgeSet) : Family m :=
  {S | ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ v : V, v ∈ (e i : Sym2 V) → v ∉ (e j : Sym2 V)}

end LDPSelect.Supplement


