-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_TranslationSubmodularOn
-- name    : DiscreteConvex_CombinatorialC_TranslationSubmodularOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:39:54.893616+00:00
-- url     : https://prove2.me/theorems/de71156a-fd7f-4b02-a597-75c7028e6d91
-- title:
--   Translation submodularity on a set of arguments
-- statement:
--   $g(p)+g(q)\ge g((p-\alpha\mathbf{1})\vee q)+g(p\wedge(q+\alpha\mathbf{1}))$ for all $p,q \in S$ and all $\alpha\ge 0$: translation submodularity asked only of the arguments in $S$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.84, restricted to a set of arguments.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.84

import Mathlib

namespace DiscreteConvex.CombinatorialC

/-- `g` is translation submodular on `S`: the defining inequality asked only of the arguments in
`S`. Murota, *Discrete Convex Analysis*, SIAM 2003, p. 74 defines `F(w,c)` for `c ≥ 0` only, so
the `c` part of Theorem 2.23 is a statement on the nonnegative orthant. -/
def TranslationSubmodularOn {W : Type*} [Fintype W] (S : Set (W → ℝ)) (g : (W → ℝ) → ℝ) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ α : ℝ, 0 ≤ α →
    g p + g q ≥ g ((p - α • (fun _ => (1 : ℝ))) ⊔ q) + g (p ⊓ (q + α • (fun _ => (1 : ℝ))))

end DiscreteConvex.CombinatorialC


