-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_LiftedFunction
-- name    : DiscreteConvex_MConvexFunctionsB_LiftedFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:06:01.558986+00:00
-- url     : https://prove2.me/theorems/64df1c38-221e-4a44-8a71-5c29e316c836
-- title:
--   LiftedFunction
-- statement:
--   The lift $\tilde f$ of $f$ to $\tilde V = \{0\} \cup V$ (Eq. (6.4)): $\tilde f(x_0,x) = f(x)$ if $x_0=-x(V)$, else $+\infty$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Eq. (6.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Eq. (6.4)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.134, Eq. (6.4), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The lift `f̃ : Z^(Ṽ) → R ∪ {+∞}` of `f` to `Ṽ = \{0\} ∪ V` (Eq. (6.4)), `Option V` with
`none` standing for the new element `0`. -/
def LiftedFunction {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) : (Option V → ℤ) → WithTop ℝ :=
  fun x => if x none = -(∑ v : V, x (some v)) then f (fun v => x (some v)) else ⊤

end DiscreteConvex.MConvexFunctionsB


