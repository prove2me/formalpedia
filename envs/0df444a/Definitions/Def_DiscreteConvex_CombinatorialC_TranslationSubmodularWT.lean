-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_TranslationSubmodularWT
-- name    : DiscreteConvex_CombinatorialC_TranslationSubmodularWT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:40:18.61144+00:00
-- url     : https://prove2.me/theorems/f55063d2-2ba0-4d03-812d-d6b9ea54f56e
-- title:
--   Translation submodularity, extended-real version
-- statement:
--   As `TranslationSubmodular`, for $g$ valued in $\mathbb R\cup\{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.65, axiom (SBF-natural[R]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.65, axiom (SBF-natural[R])

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.65, axiom (SBF♮[R]), extended-real-valued
version for the general (possibly `+∞`) quadratic forms of §2.1.4, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Translation submodularity** (SBF-natural[R]) for a `WithTop ℝ`-valued function: for all
`p, q : Wⱽ → R` and `α ≥ 0`, `g(p) + g(q) ≥ g((p - α·1) ∨ q) + g(p ∧ (q + α·1))` (the `+∞`
cases are handled automatically by `WithTop ℝ` arithmetic, matching the book's stated
convention that the inequality holds whenever `g(p) = +∞` or `g(q) = +∞`). -/
def TranslationSubmodularWT {W : Type*} [Fintype W] (g : (W → ℝ) → WithTop ℝ) : Prop :=
  ∀ p q : W → ℝ, ∀ α : ℝ, 0 ≤ α →
    g p + g q ≥ g ((p - α • (fun _ => (1 : ℝ))) ⊔ q) + g (p ⊓ (q + α • (fun _ => (1 : ℝ))))

end DiscreteConvex.CombinatorialC


