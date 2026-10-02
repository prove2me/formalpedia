-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_PerturbedM
-- name    : DiscreteConvex_MConvexFunctions_Quasi_PerturbedM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:01:54.792982+00:00
-- url     : https://prove2.me/theorems/b99a1494-2560-43e3-be31-b60cc579080c
-- title:
--   Linear perturbation of a lattice function
-- statement:
--   The perturbation $f[p](x) = f(x) - \langle p,x\rangle$ of $f$ by a linear functional $p : V \to \mathbb R$, stated as addition of the negated shift to avoid subtraction on `WithTop ℝ`. Supporting notion for Theorem 6.68(2).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.171, supporting Theorem 6.68.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.171 (supporting Theorem 6.68)

import Mathlib

/-!
The linear perturbation `f[p]` of a function on the integer lattice, used in Theorem 6.68(2)
(Murota, *Discrete Convex Analysis*, SIAM 2003, p.171), in
`DiscreteConvex.MConvexFunctions.Quasi`.
-/

namespace DiscreteConvex.MConvexFunctions.Quasi

/-- The perturbation `f[p](x) = f(x) - ⟨p,x⟩` of `f` by a linear functional `p : V → ℝ`,
stated as addition of the negated shift to avoid subtraction on `WithTop ℝ`. -/
def PerturbedM {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) :
    (V → ℤ) → WithTop ℝ :=
  fun x => f x + ((-(∑ v, p v * (x v : ℝ)) : ℝ) : WithTop ℝ)

end DiscreteConvex.MConvexFunctions.Quasi


