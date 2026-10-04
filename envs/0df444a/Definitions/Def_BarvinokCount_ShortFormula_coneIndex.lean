-- Prove2me | Definitions.Def_BarvinokCount_ShortFormula_coneIndex
-- name    : BarvinokCount_ShortFormula_coneIndex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:50:26.768988+00:00
-- url     : https://prove2.me/theorems/f54f489e-a710-4f7a-a0ca-31ee860e2785
-- title:
--   Ind K — the number of integral points in the half-open parallelepiped of the generators (Definition 5.1)
-- statement:
--   Let $u_1,\dots,u_k\in\mathbb{Z}^d$ be integral vectors. The **semi-open parallelepiped** spanned by them is
--   $$\Pi=\Bigl\{x=\sum_{i=1}^k\alpha_i u_i : 0\le\alpha_i<1\Bigr\}\subseteq\mathbb{R}^d .$$
--   The **index** of the cone $K=\operatorname{co}\{u_1,\dots,u_k\}$ given by these generators is the number of integral points in $\Pi$:
--   $$\operatorname{Ind}K=\#(\Pi\cap\mathbb{Z}^d).$$
--   For $k=0$, $\Pi=\{0\}$ and $\operatorname{Ind}K=1$.
--
--   The index measures how far the generators are from being primitive: for linearly independent generators, $\operatorname{Ind}K=1$ exactly when they are primitive generators. Barvinok's decomposition lowers the index from $\operatorname{Ind}K$ to at most $(\operatorname{Ind}K)^{(d-1)/d}$ at each step.
--
--   **Formalization Note** The definition applies to every generator list; the paper uses it for linearly independent generators, and the theorems state that hypothesis. $\Pi$ is bounded, so $\Pi\cap\mathbb{Z}^d$ is always finite and the count (`Nat.card`) is the true number of points. The index depends on the generator list: scaling a generator changes it.
-- source:
--   Barvinok, A polynomial time algorithm for counting integral points in polyhedra when the dimension is fixed, Math. Oper. Res. 19 (1994), p. 774, Definition 5.1 (the parallelepiped Π also in Remark 2.5, p. 771)

import Mathlib
import Definitions.Def_BarvinokCount_ShortFormula_RationalCone

namespace BarvinokCount.ShortFormula

/-- The "semi-open" parallelepiped `Π = {∑ α_i u_i : 0 ≤ α_i < 1}` spanned by the generators
(Remark 2.5, Definition 5.1). -/
def halfOpenBox {d k : ℕ} (u : Fin k → Fin d → ℤ) : Set (Fin d → ℝ) :=
  {x | ∃ α : Fin k → ℝ, (∀ i, 0 ≤ α i ∧ α i < 1) ∧ x = ∑ i, α i • castVec (u i)}

/-- The index `Ind K = #(Π ∩ ℤ^d)` of the cone given by the generators `u` (Definition 5.1).
The set is always finite, since `Π` is bounded. -/
noncomputable def coneIndex {d k : ℕ} (u : Fin k → Fin d → ℤ) : ℕ :=
  Nat.card {z : Fin d → ℤ // castVec z ∈ halfOpenBox u}

end BarvinokCount.ShortFormula


