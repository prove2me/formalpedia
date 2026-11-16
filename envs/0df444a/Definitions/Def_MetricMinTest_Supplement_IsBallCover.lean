-- Prove2me | Definitions.Def_MetricMinTest_Supplement_IsBallCover
-- name    : MetricMinTest_Supplement_IsBallCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:29:39.47828+00:00
-- url     : https://prove2.me/theorems/335d7cb1-bfa6-49e8-91fc-d0427584afa7
-- title:
--   Fractional ball cover (feasible point of (2.1))
-- statement:
--   A **fractional ball cover** is a weighting $y\ge0$ of the indexed balls $B_{j\ell}=B(j,r_{j\ell})$, $0=r_{j1}<\dots<r_{jq_j}<\gamma$ the distinct distances from $j$ below $\gamma$, such that every index is covered with total weight at least one:
--   $$\sum_{(j,\ell):\,i\in B_{j\ell}}y_{j\ell}\ge1\qquad\text{for every }i.$$
--
--   Feasible covers of the certificate program (2.1) drive the randomized-certificate testers (Theorems D.2, D.3) and the distance-profile bridge (Theorem 6.1).
--
--   **Formalization Note** Indexed balls are encoded as in the published certificate workload, by pairs $(j,i)$ with $d(j,i)<\gamma$ (the ball $B(j,d(j,i))$); a repeated distance duplicates a ball, and covers over distinct balls are those supported on one pair per ball.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), (2.1), p.6

import Mathlib

namespace MetricMinTest.Supplement

/-- **Fractional ball cover** (a feasible point of program (2.1)). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), (2.1), p.6: `y ≥ 0`,
`∑_{(j,ℓ) : i ∈ B_{jℓ}} y_{jℓ} ≥ 1` for every `i`.

**Formalization Note.** The indexed-ball encoding of the published `certWorkload`: a pair `(j, i)`
with `d j i < γ` is the ball `B(j, d j i)`; coordinates of `y` at pairs with `d j i ≥ γ` are
not balls and do not count. A repeated distance duplicates a ball; a cover over distinct balls is
the special case supported on one pair per ball. -/
def IsBallCover {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (γ : ℝ) (y : ι × ι → ℝ) : Prop :=
  (∀ p, 0 ≤ y p) ∧
  ∀ i, 1 ≤ ∑ p ∈ Finset.univ.filter (fun p : ι × ι => d p.1 p.2 < γ ∧ d i p.1 ≤ d p.1 p.2), y p

end MetricMinTest.Supplement


