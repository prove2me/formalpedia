-- Prove2me | Definitions.Def_MaxLatticeFree_Inequalities_LatticeFree
-- name    : MaxLatticeFree_Inequalities_LatticeFree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:42:18.493839+00:00
-- url     : https://prove2.me/theorems/6f90e952-f71d-495a-a7f2-066c02946150
-- title:
--   Lattice-free and maximal lattice-free convex sets in $f+W$
-- statement:
--   Let $f\in\mathbb R^q$ and $W\subseteq\mathbb R^q$ a linear subspace. A set $B\subseteq\mathbb R^q$ is a **lattice-free convex set in $f+W$** if
--
--   1. $B\subseteq f+W$,
--   2. $B$ is convex, and
--   3. $B$ has no integral point in its interior with respect to the topology induced on $f+W$ by $\mathbb R^q$:
--   $$\operatorname{int}_{f+W}(B)\cap\mathbb Z^q=\emptyset .$$
--
--   It is a **maximal lattice-free convex set in $f+W$** if in addition it is inclusionwise maximal with these three properties: every lattice-free convex set $B'$ in $f+W$ with $B\subseteq B'$ equals $B$.
--
--   Maximal lattice-free convex sets with $f$ in their interior are the geometric objects that generate the minimal valid inequalities of $R_f(W)$ (Theorem 3).
--
--   **Formalization Note** The interior is relative to $f+W$, not to $\mathbb R^q$: with the ambient interior every subset of a proper affine space would be lattice-free.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 2 (definition of a maximal lattice-free convex set in W), applied to the affine space f + W as on p. 4

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel

namespace MaxLatticeFree.Inequalities

/-- A lattice-free convex set in `f + W` (arXiv:1701.06543v1, p. 2): `B ⊆ f + W`, `B` is convex,
and `B` has no integral point in its interior relative to `f + W`. -/
noncomputable def IsLatticeFree {q : ℕ} (f : EuclideanSpace ℝ (Fin q))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (B : Set (EuclideanSpace ℝ (Fin q))) : Prop :=
  B ⊆ affSpace f W ∧ Convex ℝ B ∧ ∀ x ∈ intRel (affSpace f W) B, x ∉ integralPoints q

/-- A maximal lattice-free convex set in `f + W` (arXiv:1701.06543v1, p. 2): lattice-free in
`f + W` and inclusionwise maximal with that property. -/
noncomputable def IsMaximalLatticeFree {q : ℕ} (f : EuclideanSpace ℝ (Fin q))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (B : Set (EuclideanSpace ℝ (Fin q))) : Prop :=
  IsLatticeFree f W B ∧ ∀ B' : Set (EuclideanSpace ℝ (Fin q)), IsLatticeFree f W B' → B ⊆ B' → B' = B

end MaxLatticeFree.Inequalities


