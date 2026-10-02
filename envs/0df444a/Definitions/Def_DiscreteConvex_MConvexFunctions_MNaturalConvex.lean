-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctions_MNaturalConvex
-- name    : DiscreteConvex_MConvexFunctions_MNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:57:16.131988+00:00
-- url     : https://prove2.me/theorems/3a1f4358-955b-448d-9275-51c15a493801
-- title:
--   M-natural-convex function (via the lift)
-- statement:
--   $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ is **M$^\natural$-convex** if its lift $\tilde f$ (Eq. (6.4)) to $\mathbb Z^{\tilde V}$ is an M-convex function. This is the book's primary definition of M$^\natural$-convexity; Theorem 6.2 characterizes it by the direct exchange axiom (M$^\natural$-EXC[Z]).
--
--   ({SRC}, p.134.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_LiftedFunction
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.134: M♮-convex functions, defined via the
lift to the extended ground set, in `DiscreteConvex.MConvexFunctions`.
-/

namespace DiscreteConvex.MConvexFunctions

/-- `f : Zⱽ → R ∪ {+∞}` is **M♮-convex** if its lift `f̃` (Eq. (6.4)) to `Z^(Ṽ)`,
`Ṽ = \{0\} ∪ V`, is an M-convex function. This is the book's primary definition of
M♮-convexity; Theorem 6.2 characterizes it by the direct exchange axiom (M♮-EXC[Z]). -/
noncomputable def MNaturalConvex {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) : Prop :=
  MExchangeAxiom (LiftedFunction f)

end DiscreteConvex.MConvexFunctions


