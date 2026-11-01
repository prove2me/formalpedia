-- Prove2me | Definitions.Def_ALAVI_IsConeConvexOn
-- name    : ALAVI_IsConeConvexOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:44.013076+00:00
-- url     : https://prove2.me/theorems/065c2ef2-803f-4863-9179-1e9c5d85b23a
-- title:
--   $C$-convexity of a mapping $\Theta$ on $U$ (Definition 1)
-- statement:
--   Let $C\subseteq F$ be a closed convex cone and $U\subseteq E$. A mapping $\Theta:E\to F$ is **$C$-convex** on $U$ if
--
--   $$
--   \Theta(\alpha u+(1-\alpha)v)-\alpha\Theta(u)-(1-\alpha)\Theta(v)\in-C\qquad\forall u,v\in U,\ \forall\alpha\in[0,1].
--   $$
--
--   For $C=\mathbb R^m_+$ this is componentwise convexity. For $p\in C^*$ it makes $u\mapsto\langle p,\Theta(u)\rangle$ convex on $U$, which is how the constraint $\Theta(u)\in-C$ enters the convex analysis of the paper.
--
--   **Formalization Note.** $C$ is Mathlib's `ProperCone ℝ F` (a closed convex cone containing $0$); membership in $-C$ is written as membership of the negative in $C$.
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, Definition 1, p.4

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj

namespace ALAVI

/-- **Definition 1 (conic convexity of a mapping).** Let `C` be a closed convex cone. The
mapping `Θ` is `C`-convex on `U` if for all `u, v ∈ U` and `α ∈ [0, 1]`,
`Θ(αu + (1 - α)v) - αΘ(u) - (1 - α)Θ(v) ∈ -C`.

Zhao, Zhu & Zhang, arXiv:2306.01214v1, Definition 1, p.4.

Formalization Note: `ℝⁿ`, `ℝᵐ` are finite-dimensional real inner product spaces `E`, `F` in the
theorems; the cone `C` is Mathlib's `ProperCone ℝ F` (a closed convex cone containing `0`, which
is every nonempty closed convex cone). Membership in `-C` is written as `-(…) ∈ C`. -/
def IsConeConvexOn {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (Θ : E → F) : Prop :=
  ∀ u ∈ U, ∀ v ∈ U, ∀ a ∈ Set.Icc (0 : ℝ) 1,
    -(Θ (a • u + (1 - a) • v) - a • Θ u - (1 - a) • Θ v) ∈ C

end ALAVI


