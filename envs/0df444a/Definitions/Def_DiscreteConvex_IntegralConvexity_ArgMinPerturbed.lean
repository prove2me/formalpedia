-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexity_ArgMinPerturbed
-- name    : DiscreteConvex_IntegralConvexity_ArgMinPerturbed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:48:50.539436+00:00
-- url     : https://prove2.me/theorems/8fc1923f-c9e3-46e4-bc5f-3279102727b4
-- title:
--   Minimizer set of a perturbed function
-- statement:
--   The set $\arg\min f[-p] \subseteq \mathbb Z^n$ of minimizers of the linear perturbation $f[-p](x) = f(x) - \langle p,x\rangle$.
--
--   **Formalization Note.** Stated additively ($f(x) + \langle p,y\rangle \le f(y) + \langle p,x\rangle$) to avoid subtraction on `WithTop ℝ`, equivalent to $f(x)-\langle p,x\rangle \le f(y) - \langle p,y\rangle$ whenever that subtraction is defined.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93: the minimizer set `arg min f[-p]` of a
linearly perturbed function on the integer lattice, in `DiscreteConvex.IntegralConvexity`.
-/

namespace DiscreteConvex.IntegralConvexity

/-- The set `arg min f[-p] ⊆ Zⁿ` of minimizers of the perturbation `f[-p](x) = f(x) - ⟨p,x⟩`.
Stated additively (`f(x) + ⟨p,y⟩ ≤ f(y) + ⟨p,x⟩`) to avoid subtraction on `WithTop ℝ`, which is
equivalent to `f(x) - ⟨p,x⟩ ≤ f(y) - ⟨p,y⟩` whenever the subtraction is defined. -/
def ArgMinPerturbed {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (p : Fin n → ℝ) :
    Set (Fin n → ℤ) :=
  {x | ∀ y : Fin n → ℤ,
    f x + ((∑ i, p i * (y i : ℝ) : ℝ) : WithTop ℝ) ≤ f y + ((∑ i, p i * (x i : ℝ) : ℝ) : WithTop ℝ)}

end DiscreteConvex.IntegralConvexity


