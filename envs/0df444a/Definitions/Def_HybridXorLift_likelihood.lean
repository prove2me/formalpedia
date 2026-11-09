-- Prove2me | Definitions.Def_HybridXorLift_likelihood
-- name    : HybridXorLift_likelihood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:17:38.423785+00:00
-- url     : https://prove2.me/theorems/14f71457-66bf-48c5-95aa-21dfc2a65b43
-- title:
--   Likelihood $\ell_h(z)$ of a history
-- statement:
--   For a history $h$ and an outer string $z$, the **likelihood** of $h$ under a uniformly random encoding of $z$ is
--   $$
--   \ell_h(z) = \mathbb E_{x \in \sigma^{-1}(z)}\, |c_h(x)|^2 ,
--   $$
--   the probability of reaching $h$ when the input is a uniformly random member of the fibre $\sigma^{-1}(z)$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §3.2, Eq. (3.7), p.12 (PDF p.14)

import Definitions.Def_HybridXorLift_pathProb
import Definitions.Def_HybridXorLift_fibreAvg

namespace HybridXorLift

/-- The likelihood `ℓ_h(z) = E_{x ∈ σ⁻¹(z)} |c_h(x)|²` of a history under a uniformly random
encoding of the outer string `z` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §3.2, Eq. (3.7), p.12 (PDF p.14)). -/
noncomputable def likelihood {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α)
    (h : List (Step (Fin n × Fin r))) (z : Fin n → Bool) : ℝ :=
  fibreAvg z fun x => pathProb A x h

end HybridXorLift


