-- Prove2me | Definitions.Def_HybridXorLift_IsGood
-- name    : HybridXorLift_IsGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:21:28.2552+00:00
-- url     : https://prove2.me/theorems/829a449f-87a9-488b-a457-94facc3b9a11
-- title:
--   Good and bad histories
-- statement:
--   Fix $0 < \eta < 1$ and an outer string $z$. A history $h$ is **good for $z$** if
--   $$
--   \Delta^{z_{J(h)}}(h) < \eta\, \ell^{z_{J(h)}}_h ,
--   $$
--   and **bad** otherwise; in particular a history with $\ell^{z_{J(h)}}_h = 0$ is bad. On a good history the true likelihood $\ell_h(z)$ lies within a factor $1 \pm \eta$ of the average the simulator can compute.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §5.1, Eq. (5.1), p.17 (PDF p.19)

import Definitions.Def_HybridXorLift_delta
import Definitions.Def_HybridXorLift_avgLikelihood
import Definitions.Def_HybridXorLift_revealed

namespace HybridXorLift

/-- A history `h` is good for the outer string `z` (with parameter `η`) when
`Δ^{z_{J(h)}}(h) < η ℓ^{z_{J(h)}}_h`, and bad otherwise (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §5.1, Eq. (5.1), p.17 (PDF p.19)). In
particular a history with `ℓ^{z_{J(h)}}_h = 0` is bad. The kernel is the one of `τ = 1/(2q)`. -/
def IsGood {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α) (q : ℕ) (η : ℝ)
    (z : Fin n → Bool) (h : List (Step (Fin n × Fin r))) : Prop :=
  delta A q (revealed A h) z h < η * avgLikelihood A h (revealed A h) z

end HybridXorLift


