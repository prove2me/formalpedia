-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_LNaturalConvex
-- name    : DiscreteConvex_LConvexFunctions_LNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:14:21.155092+00:00
-- url     : https://prove2.me/theorems/a0efca3f-52bc-473e-9223-0e63c0c69b27
-- title:
--   L-natural-convex function (via the lift)
-- statement:
--   $g : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ is **L$^\natural$-convex** if its lift $\tilde g$ (Eq. (7.2)) to $\mathbb Z^{\tilde V}$ is an L-convex function (i.e. satisfies (SBF[Z]) and (TRF[Z])). This is the book's primary definition of L$^\natural$-convexity; Theorem 7.1 characterizes it by the direct translation-submodularity axiom (SBF$^\natural$[Z]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctions_LiftedFunctionL
import Definitions.Def_DiscreteConvex_LConvexFunctions_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctions_TRF

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.178: L♮-convex functions, defined via the lift
to the extended ground set, in `DiscreteConvex.LConvexFunctions`.
-/

namespace DiscreteConvex.LConvexFunctions

/-- `g : Zⱽ → R ∪ {+∞}` is **L♮-convex** if its lift `g̃` (Eq. (7.2)) to `Z^(Ṽ)`,
`Ṽ = \{0\} ∪ V`, is an L-convex function (i.e. satisfies (SBF[Z]) and (TRF[Z])). This is the
book's primary definition of L♮-convexity; Theorem 7.1 characterizes it by the direct
translation-submodularity axiom (SBF♮[Z]). -/
def LNaturalConvex {V : Type*} (g : (V → ℤ) → WithTop ℝ) : Prop :=
  SBF (LiftedFunctionL g) ∧ TRF (LiftedFunctionL g)

end DiscreteConvex.LConvexFunctions


