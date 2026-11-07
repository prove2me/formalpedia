-- Prove2me | Definitions.Def_QuasiStrictNE_IsPolyhedralComplex
-- name    : QuasiStrictNE_IsPolyhedralComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:29.907651+00:00
-- url     : https://prove2.me/theorems/1cbea635-5f9a-4ce0-a4d6-2016255c8e08
-- title:
--   Polyhedral complex
-- statement:
--   A **polyhedral complex** $C$ in $\mathbb R^d$ is a finite collection of convex polytopes such that
--
--   1. every face of a polytope of $C$ is in $C$;
--   2. any two polytopes of $C$ are disjoint or intersect in a face of each of them.
--
--   **Formalization Note** The paper's clause 2 reads "the intersection of any two polytopes of C is a face of each of them". Faces are nonempty (Definition 3), so the literal clause would forbid two disjoint members, such as two vertices of a simplex; the paper itself only treats nonempty intersections (p.10). The clause is therefore read "empty or a face of each". Convex polytopes are the public `CombOpt.MatchingPolytope.IsPolytope` (a polyhedron $\{x : Ax\le b\}$ contained in a box), which is Definition 3's notion: an equality is two inequalities, and a subset of $\mathbb R^d$ is bounded iff it lies in a box.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 3, pp.5–6

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsPolytope
import Definitions.Def_ProxFlatIP_Spindle

namespace QuasiStrictNE

/-- **Polyhedral complex** (Hansen & Nie, *On Existence and Computational Complexity of Quasi-strict
Equilibria*, arXiv:2611.06350, Definition 3, pp.5–6: "A polyhedral complex C is a finite collection
of convex polytopes in R^d such that: 1. Every face of a polytope of C is in C. 2. The intersection of
any two polytopes of C is a face of each of them").

`IsPolyhedralComplex C` holds iff `C` is a finite set of polytopes of `ℝ^d`, every face of a member is
a member, and any two members are either disjoint or meet in a common face of both.

**Formalization Note** Clause 2 is read "the intersection is empty or a face of each": faces are
nonempty (Definition 3), so the literal clause would forbid two disjoint members (two vertices of a
simplex), and the paper itself only treats nonempty intersections (p.10, "If Pj ∩ Pℓ ≠ ∅, their
intersection … is a face of both"). Convex polytopes (Definition 3, "a bounded subset of R^d which is
the solution set of a finite number of linear equalities and inequalities") are the public
`CombOpt.MatchingPolytope.IsPolytope`: a polyhedron `{x | Ax ≤ b}` contained in a box, which is the
same notion (an equality is two inequalities; bounded sets of `ℝ^d` are those in a box). Faces are the
public `ProxFlatIP.IsFace`: nonempty exposed subsets (Mathlib `IsExposed`, the zero functional exposing
`P` itself), which for a polytope given by linear inequalities are exactly the nonempty sets obtained
by turning some inequalities into equalities, whatever description is used. -/
def IsPolyhedralComplex {d : ℕ} (C : Set (Set (Fin d → ℝ))) : Prop :=
  C.Finite ∧ (∀ P ∈ C, CombOpt.MatchingPolytope.IsPolytope P) ∧
    (∀ P ∈ C, ∀ F, ProxFlatIP.IsFace P F → F ∈ C) ∧
    ∀ P ∈ C, ∀ Q ∈ C, P ∩ Q = ∅ ∨ (ProxFlatIP.IsFace P (P ∩ Q) ∧ ProxFlatIP.IsFace Q (P ∩ Q))

end QuasiStrictNE


