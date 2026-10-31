-- Prove2me | Definitions.Def_CombOpt_MatroidPolytope_rankPolytope
-- name    : CombOpt_MatroidPolytope_rankPolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:26.082995+00:00
-- url     : https://prove2.me/theorems/51577ced-b95d-49e1-9697-10cb4812bd2e
-- title:
--   The rank polyhedron $\{x\ge 0 : x(A)\le r(A)\ \forall A\subseteq S\}$
-- statement:
--   For a family $\mathcal I$ of subsets of $S$ with rank function $r$, let
--   $$P=\{x\in\mathbb R^S : x_e\ge 0 \text{ for all } e\in S,\ x(A)\le r(A)\text{ for all }A\subseteq S\},$$
--   where $x(A)=\sum_{e\in A}x_e$. This is the feasible region of the linear program (8.1) and the right-hand side of Edmonds' Matroid Polytope Theorem.
--
--   **Formalization Note** The rank (a natural number) is cast to a real number; the constraint is imposed for every finite subset of the ground type, i.e. every $A\subseteq S$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, (8.1), p. 278 (PDF p. 285), and Theorem 8.5, p. 279 (PDF p. 286)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_rank

namespace CombOpt.MatroidPolytope

/-- **The feasible region of the linear program (8.1).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, p. 278 (PDF p. 285), (8.1): "x(A) ≤ r(A), for all A ⊆ S; x_e ≥ 0, for all e ∈ S",
where `x(A) = Σ_{e ∈ A} x_e`; and Theorem 8.5, p. 279: the set
`{x ∈ ℝ^S : x ≥ 0, x(A) ≤ r(A) for all A ⊆ S}`.

`rankPolytope I` is the set of `x : α → ℝ` with `x_e ≥ 0` for every `e` and
`Σ_{e ∈ A} x_e ≤ r(A)` for every subset `A` of the ground set, with `r = rank I`.

**Formalization Note.** The rank (a natural number) is cast to `ℝ`. -/
def rankPolytope {α : Type*} (I : Finset α → Prop) : Set (α → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ ∀ A : Finset α, ∑ e ∈ A, x e ≤ (rank I A : ℝ)}

end CombOpt.MatroidPolytope


