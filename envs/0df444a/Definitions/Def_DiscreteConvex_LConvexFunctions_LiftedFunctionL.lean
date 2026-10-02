-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_LiftedFunctionL
-- name    : DiscreteConvex_LConvexFunctions_LiftedFunctionL
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:13:42.629974+00:00
-- url     : https://prove2.me/theorems/fbdc051a-dbc8-49f4-9a69-d11524379683
-- title:
--   Lift to the extended ground set (Eq. 7.2)
-- statement:
--   The lift $\tilde g : \mathbb Z^{\tilde V} \to \mathbb R \cup \{+\infty\}$ of $g : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ to the extended ground set $\tilde V = \{0\} \cup V$ (represented as `Option V`): $\tilde g(p_0,p) = g(p - p_0 \mathbf 1)$.
--
--   ({SRC}, p.178, Eq. (7.2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, Eq. (7.2)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.178, Eq. (7.2): the lift of a function on
`Zⱽ` to a function on `Z^(Ṽ)` with `Ṽ = {0} ∪ V`, used to define L♮-convexity, in
`DiscreteConvex.LConvexFunctions`.
-/

namespace DiscreteConvex.LConvexFunctions

/-- The lift `g̃ : Z^(Ṽ) → R ∪ {+∞}` of `g : Zⱽ → R ∪ {+∞}` to the extended ground set
`Ṽ = {0} ∪ V` (Eq. (7.2)), represented as `Option V` with `none` standing for the new element
`0`: `g̃(p₀, p) = g(p - p₀ · 1)`. -/
def LiftedFunctionL {V : Type*} (g : (V → ℤ) → WithTop ℝ) : (Option V → ℤ) → WithTop ℝ :=
  fun x => g (fun v => x (some v) - x none)

end DiscreteConvex.LConvexFunctions


