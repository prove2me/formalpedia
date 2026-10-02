-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_Submodular
-- name    : DiscreteConvex_CombinatorialB_Submodular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:31:10.090322+00:00
-- url     : https://prove2.me/theorems/6ebf001b-63a1-4b89-8472-41138e9cf36b
-- title:
--   Submodularity of a real function on Rⱽ
-- statement:
--   A function $g:\mathbb R^V\to\mathbb R$ is **submodular**: $g(p)+g(q)\ge g(p\vee q)+g(p\wedge q)$ for all $p,q$, where $\vee,\wedge$ are componentwise max/min.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.65, Eq. (2.17).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.65, Eq. (2.17)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.65, Eq. (2.17): submodularity of a real-valued
function on `Rⱽ`, in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- **Submodularity** (2.17) of `g : Rⱽ → R`: `g(p) + g(q) ≥ g(p ∨ q) + g(p ∧ q)`, where `∨`/`∧`
are the componentwise max/min (Eq. (2.16)), taken from the pointwise lattice structure on
`V → ℝ`. -/
def Submodular {V : Type*} [Fintype V] (g : (V → ℝ) → ℝ) : Prop :=
  ∀ p q : V → ℝ, g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.CombinatorialB


