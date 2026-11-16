-- Prove2me | Definitions.Def_GeomDRSub_Supplement_offlineAns
-- name    : GeomDRSub_Supplement_offlineAns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:41:33.19034+00:00
-- url     : https://prove2.me/theorems/bfb285b0-2078-4731-8384-4bfd49b1c7eb
-- title:
--   Offline oracle answers: exact value–gradient pair and exact projection
-- statement:
--   In the offline model there is one objective $f$. An objective query at $y\in[0,1]^d$ is answered by the exact pair $(f(y),\nabla f(y))$, where $\nabla f$ is the gradient on the closed cube (boundary gradients are continuous extensions). A projection call on $z$ is answered by $\mathrm{proj}(z)$, which is instantiated with the exact Euclidean projection $\Pi_K(z)$. An emission is answered by $0$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Definition 6.1, p.33

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_OCall
import Definitions.Def_GeomDRSub_Supplement_OResp
import Definitions.Def_GeomDRSub_gradQ

namespace GeomDRSub.Supplement

/-- **Offline oracle answers.** Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Definition 6.1 (p.33): "An objective query at
`y ∈ [0,1]^d` returns the exact pair `(f(y), ∇f(y))`, and exact Euclidean projection onto `K` is
supplied separately." `offlineAns f proj n c` answers an objective query at `y` by
`(f(y), ∇f(y))` (`∇` is `gradQ`, the within-cube gradient), a projection call on `z` by
`proj z` (instantiated with the exact projection `Π_K`), and an emission by `Sum.inr 0`. The
mark count `n` is ignored: there is one objective. -/
noncomputable def offlineAns {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : ℕ → OCall d → OResp d :=
  fun _ c =>
    match c with
    | Sum.inl y => Sum.inl (f y, gradQ f y)
    | Sum.inr (Sum.inl z) => Sum.inr (proj z)
    | Sum.inr (Sum.inr _) => Sum.inr 0

end GeomDRSub.Supplement


