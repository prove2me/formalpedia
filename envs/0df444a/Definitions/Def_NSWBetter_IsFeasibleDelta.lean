-- Prove2me | Definitions.Def_NSWBetter_IsFeasibleDelta
-- name    : NSWBetter_IsFeasibleDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:15.220684+00:00
-- url     : https://prove2.me/theorems/0523abbf-147a-452e-b75b-391e3d0e759c
-- title:
--   Feasible integer $\Delta$ for a fractional allocation (Definition 4.1)
-- statement:
--   A positive integer $\Delta$ is **feasible** for the fractional allocation $x$ and the rounding scheme $D$ if (a) $\Delta b_g$ is an integer for every bucket $b$ and good $g$, and (b) $\Delta\Pr[M]$ is an integer for every matching $M$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 4.1, p.17 (Feasible Integers)

import Mathlib
import Definitions.Def_NSWBetter_bucket

namespace NSWBetter

/-- **Feasible integers (Definition 4.1).**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 4.1, p.17: "we say that a positive integer ∆ is feasible with respect to a rational fractional allocation x if (a) ∆bg is an integer for each bucket b ∈ B and g ∈ G, and (b) ∆ Pr[MG(x) = M′] is an integer for each matching M′ in the support of MG(x)." -/
def IsFeasibleDelta {n m : ℕ} (r : Fin n → Fin m ≃ Fin m) (x : Fin n → Fin m → ℝ)
    (D : Finset (Fin n × Fin m × Fin m) → ℝ) (Δ : ℕ) : Prop :=
  1 ≤ Δ ∧ (∀ i t g, ∃ k : ℕ, (Δ : ℝ) * bucket r x i t g = k) ∧ ∀ M, ∃ k : ℕ, (Δ : ℝ) * D M = k

end NSWBetter


