-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_TranslationSubmodular
-- name    : DiscreteConvex_CombinatorialC_TranslationSubmodular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:39:51.167658+00:00
-- url     : https://prove2.me/theorems/a57c8d72-6a85-4a02-96b9-968b1b80a124
-- title:
--   Translation submodularity (SBF-natural[R])
-- statement:
--   $(\mathrm{SBF}^\natural[\mathbb R])$: $g(p)+g(q)\ge g((p-\alpha\mathbf1)\vee q)+g(p\wedge(q+\alpha\mathbf1))$ for $\alpha\ge0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.65, axiom (SBF-natural[R]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.65, axiom (SBF-natural[R])

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.65, axiom (SBF♮[R]): translation
submodularity, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Translation submodularity** (SBF-natural[R]): for all `p, q` and `α ≥ 0`,
`g(p) + g(q) ≥ g((p - α·1) ∨ q) + g(p ∧ (q + α·1))`. -/
def TranslationSubmodular {W : Type*} [Fintype W] (g : (W → ℝ) → ℝ) : Prop :=
  ∀ p q : W → ℝ, ∀ α : ℝ, 0 ≤ α →
    g p + g q ≥ g ((p - α • (fun _ => (1 : ℝ))) ⊔ q) + g (p ⊓ (q + α • (fun _ => (1 : ℝ))))

end DiscreteConvex.CombinatorialC


