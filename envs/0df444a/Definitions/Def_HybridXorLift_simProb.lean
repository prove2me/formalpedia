-- Prove2me | Definitions.Def_HybridXorLift_simProb
-- name    : HybridXorLift_simProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:21:48.39246+00:00
-- url     : https://prove2.me/theorems/535c0683-7346-4eb7-9808-dfe372e2a5d6
-- title:
--   Simulator path probability $P'_z(h)$ (Algorithm 1)
-- statement:
--   **Algorithm 1** (the classical simulator) has query access to an outer string $z$. It starts at $h = \varnothing$; while $h$ is internal, it queries $z_i$ for every block $i \in J^+(h)$ whose bit is still unknown, sets $\xi' = z_{J^+(h)}$, returns $\bot$ if $\ell^{\xi'}_h = 0$, and otherwise moves to the child $hy$ with probability $\ell^{\xi'}_{hy} / \ell^{\xi'}_h$. For a path $h_0 = \varnothing, h_1, \dots, h_m$, the probability that the simulator follows it is
--   $$
--   P'_z(h_m) = \prod_{t=0}^{m-1} \frac{\ell^{z_{J^+(h_t)}}_{h_{t+1}}}{\ell^{z_{J^+(h_t)}}_{h_t}} .
--   $$
--
--   **Formalization Note** A factor with denominator $0$ evaluates to $0$, which is the probability of following the path when the simulator returns $\bot$ at that step.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Algorithm 1, p.17 (PDF p.19); Lemma 5.1, p.18 (PDF p.20)

import Definitions.Def_HybridXorLift_avgLikelihood
import Definitions.Def_HybridXorLift_revealedNext

namespace HybridXorLift

/-- The probability `P′_z(h)` that the classical simulator (Algorithm 1, p.17 (PDF p.19), of
Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd)) with query access to the outer string `z` follows the path `h = (h_0, …, h_m)`: at each
internal `h_t` it knows `ξ′ = z_{J⁺(h_t)}` and moves to `h_{t+1}` with probability
`ℓ^{ξ′}_{h_{t+1}} / ℓ^{ξ′}_{h_t}`; it returns `⊥` when `ℓ^{ξ′}_{h_t} = 0`.

**Formalization Note** The product of the transition probabilities along the path; a factor
with denominator `0` is `0` in Lean, which is the probability `0` of following the path when the
simulator returns `⊥` at that step. -/
noncomputable def simProb {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α)
    (z : Fin n → Bool) (h : List (Step (Fin n × Fin r))) : ℝ :=
  ∏ t ∈ Finset.range h.length,
    avgLikelihood A (h.take (t + 1)) (revealedNext A (h.take t)) z /
      avgLikelihood A (h.take t) (revealedNext A (h.take t)) z

end HybridXorLift


