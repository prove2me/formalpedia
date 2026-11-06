-- Prove2me | Definitions.Def_MetricMinTest_centerProfile
-- name    : MetricMinTest_centerProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:59.888804+00:00
-- url     : https://prove2.me/theorems/47665e32-5c6c-4a33-89f2-66bd17df5387
-- title:
--   Distance profile $s_j$ of a center
-- statement:
--   With the distinct distances $0=r_{j1}<\dots<r_{jq_j}<\gamma$ from $j$, the gaps $a_{j\ell}=\gamma-r_{j\ell}$ and $a_{j,q_j+1}=0$, the distance profile of $j$ is
--   $$s_j=\sum_{\ell=1}^{q_j}\Big(1-\frac{a_{j,\ell+1}^2}{a_{j\ell}^2}\Big).$$
--   Each term is at most one, so $s_j\le q_j$.
--
--   **Formalization Note** Computed from the increasingly sorted list of distinct distances below $\gamma$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §2, p.6; Theorem 6.1, p.14

import Mathlib

namespace MetricMinTest

/-- **Distance profile `s_j` of a center** (Theorem 6.1). Chen–Fang, *Minimum-Mean Testing under
Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §2 p.6 and
Theorem 6.1, p.14: with the distinct distances `0 = r_{j1} < ⋯ < r_{jq_j} < γ` from `j`,
`a_{jℓ} = γ − r_{jℓ}` and `a_{j,q_j+1} = 0`,
`s_j = ∑_{ℓ=1}^{q_j} (1 − a²_{j,ℓ+1} / a²_{jℓ})`.

**Formalization Note.** The distinct distances `d j i < γ` are sorted increasingly, mapped to the
gaps `γ − r`, and `0` is appended; `s_j` sums `1 − a'² / a²` over consecutive pairs `(a, a')`. -/
noncomputable def centerProfile {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (γ : ℝ) (j : ι) : ℝ :=
  let rs : List ℝ := ((Finset.univ.image (fun i => d j i)).filter (· < γ)).sort (· ≤ ·)
  let as : List ℝ := rs.map (fun r => γ - r) ++ [0]
  (List.zipWith (fun a a' => 1 - a' ^ 2 / a ^ 2) as as.tail).sum

end MetricMinTest


