-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_SubdifferentialZ
-- name    : DiscreteConvex_ConjugacyDuality_SubdifferentialZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:09:32.050121+00:00
-- url     : https://prove2.me/theorems/3eb3ba7d-4b37-4e7f-bb2b-0aa03174815c
-- title:
--   Integer subdifferential
-- statement:
--   The **integer subdifferential** $\partial_{\mathbb Z} f(x) \subseteq \mathbb Z^V$: $p$ is a subgradient of $f$ at $x$ if $f(x) - \langle p,x\rangle \le f(y) - \langle p,y\rangle$ for all $y$ — equivalently, $x$ minimizes the perturbation $f(\cdot) - \langle p,\cdot\rangle$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, supporting Proposition 8.11.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212 (supporting Proposition 8.11)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.212: the integer subdifferential of a
function on the integer lattice, in `DiscreteConvex.ConjugacyDuality`.
-/

namespace DiscreteConvex.ConjugacyDuality

/-- The integer subdifferential `∂_Z f(x) ⊆ Zⱽ`: `p` is a subgradient of `f` at `x` if
`f(x) - ⟨p,x⟩ ≤ f(y) - ⟨p,y⟩` for all `y`, stated additively as
`f(x) + ⟨p,y⟩ ≤ f(y) + ⟨p,x⟩` to avoid subtraction on `WithTop ℝ`. -/
def SubdifferentialZ {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ) :
    Set (V → ℤ) :=
  {p | ∀ y : V → ℤ,
    f x + ((∑ v, (y v : ℝ) * (p v : ℝ) : ℝ) : WithTop ℝ) ≤
      f y + ((∑ v, (x v : ℝ) * (p v : ℝ) : ℝ) : WithTop ℝ)}

end DiscreteConvex.ConjugacyDuality


