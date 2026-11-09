-- Prove2me | Definitions.Def_HybridXorLift_delta
-- name    : HybridXorLift_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:19:13.799836+00:00
-- url     : https://prove2.me/theorems/2fecd1e1-d4ab-4c4a-ac3b-487eee3ce7fe
-- title:
--   Total deviation bound $\Delta^\xi(h)$
-- statement:
--   For $J \subseteq [n]$ and $\xi \in \{0,1\}^J$, the **total deviation bound** of a history $h$ is
--   $$
--   \Delta^\xi(h) = \sum_{\varnothing \ne I \subseteq \bar J} \Phi^\xi_I(h),
--   $$
--   an empty sum being zero. It bounds how far the true likelihood $\ell_h(z)$ can be from its average $\ell^\xi_h$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §3.3, Eq. (3.11), p.13 (PDF p.15)

import Definitions.Def_HybridXorLift_phi

namespace HybridXorLift

/-- The total deviation bound `Δ^ξ(h) = Σ_{∅ ≠ I ⊆ J̄} Φ^ξ_I(h)` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §3.3, Eq. (3.11), p.13
(PDF p.15)). An empty sum is zero. -/
noncomputable def delta {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α) (q : ℕ)
    (J : Finset (Fin n)) (ξ : Fin n → Bool) (h : List (Step (Fin n × Fin r))) : ℝ :=
  ∑ I ∈ Jᶜ.powerset.filter (·.Nonempty), phi A q I J ξ h

end HybridXorLift


