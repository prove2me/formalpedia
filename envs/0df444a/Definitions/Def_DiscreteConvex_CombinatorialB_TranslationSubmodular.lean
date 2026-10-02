-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_TranslationSubmodular
-- name    : DiscreteConvex_CombinatorialB_TranslationSubmodular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:31:11.230444+00:00
-- url     : https://prove2.me/theorems/eab8765f-6f3f-43a9-ac08-7ce0f0cd8f7f
-- title:
--   Translation submodularity (SBF-natural[R])
-- statement:
--   **Translation submodularity** (the book's $(\mathrm{SBF}^\natural[\mathbb R])$): for all $p,q\in\mathbb R^V$ and $\alpha\ge 0$, $g(p)+g(q)\ge g((p-\alpha\mathbf 1)\vee q)+g(p\wedge(q+\alpha\mathbf 1))$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.65, axiom (SBF-natural[R]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.65, axiom (SBF-natural[R])

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.65, axiom (SBF-natural[R]): translation
submodularity, in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- **Translation submodularity** (SBF-natural[R], the book's `SBF♮[R]`): for all `p, q ∈ Rⱽ`
and `α ≥ 0`,
`g(p) + g(q) ≥ g((p - α·1) ∨ q) + g(p ∧ (q + α·1))`,
where `1` is the all-ones vector. Ordinary submodularity is the special case `α = 0`. -/
def TranslationSubmodular {V : Type*} [Fintype V] (g : (V → ℝ) → ℝ) : Prop :=
  ∀ p q : V → ℝ, ∀ α : ℝ, 0 ≤ α →
    g p + g q ≥ g ((p - α • (fun _ => (1 : ℝ))) ⊔ q) + g (p ⊓ (q + α • (fun _ => (1 : ℝ))))

end DiscreteConvex.CombinatorialB


