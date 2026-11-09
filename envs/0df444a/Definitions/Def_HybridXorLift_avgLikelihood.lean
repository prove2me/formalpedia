-- Prove2me | Definitions.Def_HybridXorLift_avgLikelihood
-- name    : HybridXorLift_avgLikelihood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:18:45.376764+00:00
-- url     : https://prove2.me/theorems/78c051ab-7736-4a73-b905-71a6c7837a1f
-- title:
--   Averaged likelihood $\ell^\xi_h$
-- statement:
--   For a set $J \subseteq [n]$ and an assignment $\xi \in \{0,1\}^J$, the **averaged likelihood** of a history $h$ is
--   $$
--   \ell^\xi_h = \mathbb E_{z : z_J = \xi}\, \ell_h(z),
--   $$
--   the likelihood averaged over the outer strings that agree with $\xi$. It is what a classical simulator that knows only $z_J$ can compute.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §3.3, p.13 (PDF p.15)

import Definitions.Def_HybridXorLift_likelihood
import Definitions.Def_HybridXorLift_cubeAvg

namespace HybridXorLift

/-- The averaged likelihood `ℓ^ξ_h = E_{z : z_J = ξ} ℓ_h(z)` for `J ⊆ [n]` and `ξ ∈ {0,1}^J`
(Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §3.3, p.13 (PDF p.15)).

**Formalization Note** `ξ` is a full function of which only `ξ|_J` is read (see `cubeAvg`). -/
noncomputable def avgLikelihood {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α)
    (h : List (Step (Fin n × Fin r))) (J : Finset (Fin n)) (ξ : Fin n → Bool) : ℝ :=
  cubeAvg J ξ fun z => likelihood A h z

end HybridXorLift


