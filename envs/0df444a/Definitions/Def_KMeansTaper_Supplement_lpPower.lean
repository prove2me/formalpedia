-- Prove2me | Definitions.Def_KMeansTaper_Supplement_lpPower
-- name    : KMeansTaper_Supplement_lpPower
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:44:40.482672+00:00
-- url     : https://prove2.me/theorems/6c6b1dae-48cb-406b-b592-0d497da21018
-- title:
--   The natural power-cost relaxation $\mathrm{LP}_p$
-- statement:
--   For a metric $k$-means instance and a real exponent $p$, $\mathrm{LP}_p$ is the optimum of the standard facility-location relaxation
--
--   $$
--   \min \sum_{j\in J}\sum_{i\in F} d(j,i)^p x_{ji}
--   $$
--
--   subject to $0\le x_{ji}\le y_i\le1$, $\sum_{i\in F}x_{ji}=1$ for every client $j$, and $\sum_{i\in F}y_i\le k$. It is the LP benchmark in Theorem 3.6, and at $p=2$ it is exactly the published `KMeansTaper.lp2`.
--
--   **Formalization Note** The value is represented as the real infimum of the nonempty, nonnegative feasible objective set. Real powers use `Real.rpow`; the constraints are exactly those pinned by the base mission's squared LP.
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Section 2 ("Problem"), p.3 (PDF p.6), and paragraph before Theorem 3.6, p.5 (PDF p.8)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_lp2

namespace KMeansTaper
namespace Supplement

open OAI.MetricKMedian (Instance)

/-- **The power-cost LP value `LP_p`**, introduced immediately before Theorem 3.6, p.5
(PDF p.8): the optimum of the Section 2 relaxation with objective
`∑_{j ∈ J} ∑_{i ∈ F} d(j,i)^p x_{ji}` and facility budget `k`.

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

**Formalization Note.** This uses the same standard relaxation pinned by the published `lp2`:
`0 ≤ x_{ji} ≤ y_i ≤ 1`, every client is assigned one unit, and `∑_i y_i ≤ k`.
The real infimum is over a nonempty set bounded below by zero. Real powers use `Real.rpow`. -/
noncomputable def lpPower (I : Instance) (p : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ (x : Fin I.n → Fin I.n → ℝ) (y : Fin I.n → ℝ),
    (∀ j i, 0 ≤ x j i ∧ x j i ≤ y i) ∧ (∀ i, y i ≤ 1) ∧
    (∀ j ∈ I.clients, ∑ i ∈ I.facilities, x j i = 1) ∧ ∑ i ∈ I.facilities, y i ≤ I.k ∧
    v = ∑ j ∈ I.clients, ∑ i ∈ I.facilities, (I.distance j i : ℝ) ^ p * x j i}

/-- At exponent two, `lpPower` is exactly the published squared relaxation `lp2`. -/
@[simp] theorem lpPower_two (I : Instance) : lpPower I 2 = lp2 I := by
  simp [lpPower, lp2]

end Supplement
end KMeansTaper


