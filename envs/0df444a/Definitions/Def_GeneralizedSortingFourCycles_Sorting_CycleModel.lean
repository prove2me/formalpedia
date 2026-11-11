-- Prove2me | Definitions.Def_GeneralizedSortingFourCycles_Sorting_CycleModel
-- name    : GeneralizedSortingFourCycles_Sorting_CycleModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:35:52.963185+00:00
-- url     : https://prove2.me/theorems/5b2962e8-34e4-46b8-ae17-6b62de817e04
-- title:
--   Distinct bipartite four-cycles and directed witnesses
-- statement:
--   For a bipartite edge set $E\subseteq\{0,\ldots,a-1\}\times\{0,\ldots,b-1\}$, a four-cycle is a pair of distinct left vertices and a pair of distinct right vertices with all four cross edges present. Increasing labels on each side count each such cycle exactly once.
--
--   For a set $S$ of predicted directed edges and a fixed edge $e=(u,v)$, the witness set is
--   $$\{(a,b):a\ne u,\ b\ne v,\ (u,v),(a,v),(u,b),(a,b)\in S\}.$$
--   Its cardinality is the paper's $w_S(e)$. The witness definition accepts arbitrary directed sets; its intended use is with a loopless, single orientation. A cardinality here establishes no certification or algorithmic guarantee.
-- source:
--   Soheil Behnezhad, Shane Ferrante, STOC 2027 submission #1354 (October 2026), §5, printed p. 8 (PDF p. 9); Claim 1, printed p. 11 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1354.pdf

import Mathlib

namespace GeneralizedSortingFourCycles.Sorting

/-- Distinct unordered bipartite four-cycles: increasing pairs of labels on each side.
Every choice is counted once, independently of a starting edge or traversal direction. -/
noncomputable def fourCycles {a b : ℕ} (E : Finset (Fin a × Fin b)) :
    Finset ((Fin a × Fin a) × (Fin b × Fin b)) := by
  classical
  exact Finset.univ.filter fun p =>
    p.1.1 < p.1.2 ∧ p.2.1 < p.2.2 ∧
    (p.1.1, p.2.1) ∈ E ∧ (p.1.1, p.2.2) ∈ E ∧
    (p.1.2, p.2.1) ∈ E ∧ (p.1.2, p.2.2) ∈ E

/-- Exactly the witness pairs (a,b) for a fixed predicted directed edge (u,v), §5.
For a loopless single orientation, all four vertices in such a witness are distinct. -/
noncomputable def witnesses {n : ℕ} (S : Finset (Fin n × Fin n))
    (e : Fin n × Fin n) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun p => p.1 ≠ e.1 ∧ p.2 ≠ e.2 ∧
    e ∈ S ∧ (p.1, e.2) ∈ S ∧ (e.1, p.2) ∈ S ∧ p ∈ S

end GeneralizedSortingFourCycles.Sorting


