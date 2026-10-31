-- Prove2me | Definitions.Def_GhostPenalty_M1
-- name    : GhostPenalty_M1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:47.694235+00:00
-- url     : https://prove2.me/theorems/c2b3e8a9-4c6b-4cef-b274-e72c79bf1d9b
-- title:
--   KKT multiplier set $M_1(x)$
-- statement:
--   For $x\in\mathbb R^n$,
--   $$M_1(x)\triangleq\{\xi\ :\ \xi\in N_{\mathbb R^m_-}(g(x)),\ 0\in\nabla f(x)+\nabla g(x)\xi+N_K(x)\},$$
--   where $\nabla g(x)\xi=\sum_i\xi_i\nabla g_i(x)$ and $N_K(x)$ is the normal cone of $K$ at $x$. If $g(x)\le 0$, the first condition reads $\xi\ge 0$, $\xi_ig_i(x)=0$; if $x$ is infeasible, $M_1(x)=\emptyset$.
--
--   $M_1(x)\ne\emptyset$ is the KKT condition for (P) at a feasible $x$.
--
--   **Formalization Note** $N_K(x)$ is the published `normalCone` (nonempty also off $K$), together with $x\in K$, which restores the classical convention $N_K(x)=\emptyset$ for $x\notin K$.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, §2, p.5

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_GhostPenalty_negOrthantNormalCone

namespace GhostPenalty

open FirstOrderOpt.ConvexTheory

/-- **The KKT multiplier set `M1(x)`.**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §2, p.5:
"`M1(x) ≜ { ξ | ξ ∈ N_{ℝᵐ₋}(g(x)), 0 ∈ ∇f(x) + ∇g(x)ξ + N_K(x) }` … where `N_{ℝᵐ₋}(y)` and
`N_K(x)` are the classical normal cones to the convex sets `ℝᵐ₋` and `K` at `y` and `x`,
respectively, `∇f` is the gradient of `f` and `∇g` is the transposed Jacobian of `g`. …
We note explicitly that if `x` is not feasible, the set `M1(x)` is empty."

**Formalization Note.** `∇g(x)ξ = ∑_i ξ_i ∇g_i(x)`; "`0 ∈ v + N_K(x)`" is "`-v ∈ N_K(x)`".
`N_K(x)` is the published `normalCone K x = {w | ∀ y ∈ K, ⟪w, y - x⟫ ≤ 0}`, which is not empty
for `x ∉ K`; the clause `x ∈ K` restores the classical convention `N_K(x) = ∅` off `K`.
`N_{ℝᵐ₋}(g(x))` is `negOrthantNormalCone`, empty unless `g(x) ≤ 0`, so `M1(x) = ∅` at
infeasible `x`, as the paper notes. -/
def M1 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Set (Fin m → ℝ) :=
  {ξ | ξ ∈ negOrthantNormalCone (fun i => g i x) ∧ x ∈ K ∧
    -(gradient f x + ∑ i, ξ i • gradient (g i) x) ∈ normalCone K x}

end GhostPenalty


