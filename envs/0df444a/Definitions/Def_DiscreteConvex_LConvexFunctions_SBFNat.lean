-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_SBFNat
-- name    : DiscreteConvex_LConvexFunctions_SBFNat
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:13:39.130223+00:00
-- url     : https://prove2.me/theorems/0bbd1835-2d57-485d-933f-80572be1b822
-- title:
--   Translation submodularity (SBF-natural[Z])
-- statement:
--   Axiom **(SBF$^\natural$[Z])**, translation submodularity: $g(p)+g(q) \ge g((p-\alpha\mathbf 1)\vee q) + g(p \wedge (q+\alpha\mathbf 1))$ for all $p,q \in \mathbb Z^V$ and all $\alpha \in \mathbb Z_{\ge 0}$. A function $g$ with $\operatorname{dom} g \ne \emptyset$ satisfying this is **L$^\natural$-convex**.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, axiom (SBF♮[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, axiom (SBF♮[Z])

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.178, axiom (SBF♮[Z]): translation
submodularity, in `DiscreteConvex.LConvexFunctions`.
-/

namespace DiscreteConvex.LConvexFunctions

/-- Axiom **(SBF♮[Z])**, translation submodularity: `g(p) + g(q) ≥ g((p - α1) ∨ q) +
g(p ∧ (q + α1))` for all `p, q ∈ Zⱽ` and all `α ∈ Z₊` (nonnegative integers). A function
`g : Zⱽ → R ∪ {+∞}` with `dom g ≠ ∅` satisfying this is **L♮-convex**. -/
def SBFNat {V : Type*} (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, ∀ α : ℤ, 0 ≤ α →
    g p + g q ≥ g (fun v => max (p v - α) (q v)) + g (fun v => min (p v) (q v + α))

end DiscreteConvex.LConvexFunctions


