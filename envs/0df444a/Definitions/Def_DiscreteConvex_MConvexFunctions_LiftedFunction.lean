-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctions_LiftedFunction
-- name    : DiscreteConvex_MConvexFunctions_LiftedFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:51:55.17764+00:00
-- url     : https://prove2.me/theorems/673ee639-6698-412f-acfa-b4addacdc99f
-- title:
--   Lift to the extended ground set (Eq. 6.4)
-- statement:
--   The lift $\tilde f : \mathbb Z^{\tilde V} \to \mathbb R \cup \{+\infty\}$ of $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ to the extended ground set $\tilde V = \{0\} \cup V$ (represented as `Option V`, `none` standing for the new element $0$): $\tilde f(x_0,x) = f(x)$ if $x_0 = -x(V)$, and $+\infty$ otherwise.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Eq. (6.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Eq. (6.4)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.134, Eq. (6.4): the lift of a function on
`Zⱽ` to a function on `Z^(Ṽ)` with `Ṽ = {0} ∪ V`, used to define M♮-convexity, in
`DiscreteConvex.MConvexFunctions`.
-/

namespace DiscreteConvex.MConvexFunctions

/-- The lift `f̃ : Z^(Ṽ) → R ∪ {+∞}` of `f : Zⱽ → R ∪ {+∞}` to the extended ground set
`Ṽ = {0} ∪ V` (Eq. (6.4)), represented as `Option V` with `none` standing for the new element
`0`: `f̃(x₀, x) = f(x)` if `x₀ = -x(V)`, and `+∞` otherwise. -/
noncomputable def LiftedFunction {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) :
    (Option V → ℤ) → WithTop ℝ :=
  fun x => if x none = -(∑ v : V, x (some v)) then f (fun v => x (some v)) else ⊤

end DiscreteConvex.MConvexFunctions


