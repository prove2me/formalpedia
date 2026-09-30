-- Prove2me | Definitions.Def_ConeLifts_StableSet_IsSlackMatrix
-- name    : ConeLifts_StableSet_IsSlackMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:16:30.197368+00:00
-- url     : https://prove2.me/theorems/1cc7568a-e0ca-4c1c-b372-ce6c71c6b07e
-- title:
--   Slack matrices of a polytope: the canonical one $(1 - \langle p, y\rangle)$ with positively scaled columns
-- statement:
--   Let $P \subseteq \mathbb R^n$ be a polytope with the origin in its interior, with vertices $p_1,\dots,p_v$ and facets $F_1,\dots,F_f$. Each facet $F_j$ is $\{x \in P : h_j(x) = 0\}$ for an affine function $h_j$, unique up to a positive scalar, with $h_j \ge 0$ on $P$, and $P = \{x : h_1(x) \ge 0, \dots, h_f(x) \ge 0\}$. A **slack matrix** of $P$ is the nonnegative $v \times f$ matrix with entries $h_j(p_i)$.
--
--   Normalizing $h_j(0) = 1$ gives the **canonical slack matrix** $S_P$. The facets of $P$ are in bijection with the extreme points $y$ of the polar $P^\circ$, with $h(x) = 1 - \langle x, y\rangle$, so
--
--   $$
--   (S_P)_{p,y} = 1 - \langle p, y\rangle, \qquad p \in \mathrm{ext}(P),\ y \in \mathrm{ext}(P^\circ),
--   $$
--
--   and every slack matrix is $S_P$ with its columns multiplied by positive scalars $w_y > 0$.
--
--   **Formalization Note** Two declarations: `canonicalSlackMatrix P`, the matrix $(1-\langle p,y\rangle)$ with rows indexed by the extreme points of $P$ and columns by the extreme points of `polar P`; and `IsSlackMatrix P M`, which says $M_{p,y} = w_y (1 - \langle p, y\rangle)$ for some positive weights $w$. This encodes Definition 3.1 through the identification the paper makes on p. 9 (facets of $P$ correspond to extreme points of $P^\circ$, and any slack matrix is the canonical one times a diagonal matrix) instead of defining facets and inequality representations; rows and columns are indexed by these sets rather than by $1,\dots,v$ and $1,\dots,f$, which does not affect factorizability. The definition is meaningful only for polytopes with the origin in the interior; the theorems using it assume this.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 9, Definition 3.1 and the paragraphs before and after it (canonical inequality representation; slack operator = canonical slack matrix; scaling by a diagonal nonnegative matrix)

import Mathlib
import Definitions.Def_ConeLifts_Shared_polar

open scoped InnerProductSpace

namespace ConeLifts.StableSet

/-- The **canonical slack matrix** `S_P` of a polytope `P ⊆ ℝⁿ` with the origin in its interior
(Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, §3, p. 9, Definition 3.1 and the paragraph after
it): rows are indexed by the vertices `ext(P)`, columns by `ext(P°)` (which are in bijection with
the facets of `P`), and the entry at `(p, y)` is `h_y(p) = 1 - ⟨p, y⟩`, the value at `p` of the
canonical (normalized `h(0) = 1`) facet inequality attached to `y`. -/
noncomputable def canonicalSlackMatrix {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) :
    Matrix (Set.extremePoints ℝ P) (Set.extremePoints ℝ (ConeLifts.Shared.polar P)) ℝ :=
  fun p y => 1 - ⟪(p : EuclideanSpace ℝ (Fin n)), (y : EuclideanSpace ℝ (Fin n))⟫_ℝ

/-- `M` is **a slack matrix** of the polytope `P` (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
Definition 3.1, p. 9): the matrix `(h_j(p_i))` of a facet inequality representation
`P = {x : h₁(x) ≥ 0, …, h_f(x) ≥ 0}`. Each facet inequality is determined up to a positive
scalar (p. 9), so the slack matrices of `P` are exactly the canonical slack matrix with every
column multiplied by a positive scalar ("any slack matrix of P can be obtained from the canonical
one by multiplication by a diagonal nonnegative matrix", p. 9); rows and columns are indexed by
the vertices of `P` and the extreme points of `P°` instead of by `1, …, v` and `1, …, f`. -/
def IsSlackMatrix {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (M : Matrix (Set.extremePoints ℝ P) (Set.extremePoints ℝ (ConeLifts.Shared.polar P)) ℝ) : Prop :=
  ∃ w : Set.extremePoints ℝ (ConeLifts.Shared.polar P) → ℝ, (∀ y, 0 < w y) ∧
    ∀ p y, M p y = w y * canonicalSlackMatrix P p y

end ConeLifts.StableSet


