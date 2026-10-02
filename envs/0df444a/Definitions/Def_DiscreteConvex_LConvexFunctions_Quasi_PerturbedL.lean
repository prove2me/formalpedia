-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_PerturbedL
-- name    : DiscreteConvex_LConvexFunctions_Quasi_PerturbedL
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:16:52.366984+00:00
-- url     : https://prove2.me/theorems/4e78b5a6-a182-46c8-9ab1-4e1de0ab1926
-- title:
--   Linear perturbation of a lattice function
-- statement:
--   The perturbation $g[x](p) = g(p) + \langle p,x\rangle$ of $g$ by a linear functional $x : V \to \mathbb R$. Supporting notion for Theorem 7.49(2).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, supporting Theorem 7.49.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199 (supporting Theorem 7.49)

import Mathlib

/-!
The linear perturbation `g[x]` of a function on the integer lattice, used in Theorem 7.49(2)
(Murota, *Discrete Convex Analysis*, SIAM 2003, p.199), in
`DiscreteConvex.LConvexFunctions.Quasi`.
-/

namespace DiscreteConvex.LConvexFunctions.Quasi

/-- The perturbation `g[x](p) = g(p) + ⟨p,x⟩` of `g` by a linear functional `x : V → ℝ`. -/
def PerturbedL {V : Type*} [Fintype V] (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ) :
    (V → ℤ) → WithTop ℝ :=
  fun p => g p + ((∑ v, (p v : ℝ) * x v : ℝ) : WithTop ℝ)

end DiscreteConvex.LConvexFunctions.Quasi


