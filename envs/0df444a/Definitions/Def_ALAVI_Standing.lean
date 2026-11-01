-- Prove2me | Definitions.Def_ALAVI_Standing
-- name    : ALAVI_Standing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:41.089347+00:00
-- url     : https://prove2.me/theorems/6591f532-9b85-4a75-8cf5-0e4262305033
-- title:
--   Standing assumptions (H2)–(H5) of Assumption A
-- statement:
--   The **standing assumptions** on the data $(U,C,G,J,\Theta)$ with constants $L,\tau$:
--
--   1. $U\subseteq E$ is closed and convex;
--   2. $G$ is $L$-Lipschitz on $U$: $\|G(a)-G(b)\|\le L\|a-b\|$ for $a,b\in U$, with $L\ge0$;
--   3. $J:E\to(-\infty,+\infty]$ is proper, convex and lower semicontinuous;
--   4. $\Theta$ is $C$-convex on $U$;
--   5. $\Theta$ is $\tau$-Lipschitz on $U$, with $\tau>0$.
--
--   These are (H2)–(H5) of Assumption A together with the model of p.2 ($U$ closed convex, $C$ a closed convex cone).
--
--   **Formalization Note.** (H1) (the solution set of (VIP) is nonempty) and (H6) (a constraint qualification) are not part of this predicate: the results of the mission do not use (H6), and they use (H1) only through a point of $U\cap\operatorname{dom}J$ or through Assumption B, which they assume explicitly. The page states (H5) on an open set $\mathcal O\supseteq U$ and takes $G,\Theta$ continuous on $\mathbb R^n$; here the Lipschitz bounds are on $U$, where the proofs use them. $\tau>0$ is implicit on the page in $0<\gamma<1/\tau$.
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, model (VIP), p.2, and Assumption A (H2)–(H5), p.4

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_IsConeConvexOn

namespace ALAVI

/-- **Assumption A, (H2)–(H5), with the model of p.2.** `U` is a closed convex set, `G` is
`L`-Lipschitz on `U`, `J : E → (-∞, +∞]` is proper, convex and lower semicontinuous, `Θ` is
`C`-convex on `U` and `τ`-Lipschitz on `U` with `τ > 0`.

Zhao, Zhu & Zhang, arXiv:2306.01214v1, model (VIP) p.2 and Assumption A, p.4.

Formalization Notes: (H1) (nonempty solution set) and (H6) (constraint qualification) are not
part of this predicate; the theorems that need a solution assume one explicitly. (H2) and (H5)
are imposed on `U` (the page states (H5) on an open `O ⊇ U`); the proofs evaluate `G` and `Θ`
only at points of `U`. `τ > 0` is implicit on the page in `0 < γ < 1/τ`. `J` is extended-real
valued, as in (H3), through the published `GoldenRatioVI.Fixed.IsProperConvexLSC`. -/
def Standing {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ : ℝ) : Prop :=
  IsClosed U ∧ Convex ℝ U ∧ 0 ≤ L ∧ (∀ a ∈ U, ∀ b ∈ U, ‖G a - G b‖ ≤ L * ‖a - b‖) ∧
    GoldenRatioVI.Fixed.IsProperConvexLSC J ∧ IsConeConvexOn U C Θ ∧ 0 < τ ∧
    (∀ a ∈ U, ∀ b ∈ U, ‖Θ a - Θ b‖ ≤ τ * ‖a - b‖)

end ALAVI


