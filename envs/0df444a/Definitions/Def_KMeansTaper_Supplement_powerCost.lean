-- Prove2me | Definitions.Def_KMeansTaper_Supplement_powerCost
-- name    : KMeansTaper_Supplement_powerCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:44:04.714087+00:00
-- url     : https://prove2.me/theorems/5bce31e3-1293-4d0e-a45b-0fc208f01df0
-- title:
--   Power cost $\mathrm{cost}_p(S)$ for real $p\ge 1$
-- statement:
--   Let $I=(J,F,d,k)$ be a finite rational metric instance and let $p$ be a real exponent. For a nonempty set $S$ of candidate facilities, the **power cost** is
--
--   $$
--   \mathrm{cost}_p(S)=\sum_{j\in J} d(j,S)^p,
--   \qquad d(j,S)=\min_{i\in S}d(j,i).
--   $$
--
--   This is the general objective introduced before Theorem 3.6. At $p=2$ it is exactly the published squared objective `KMeansTaper.cost2`.
--
--   **Formalization Note** Real exponentiation is Mathlib's `Real.rpow`. The reused `nearest` returns zero on the empty set, where the paper's distance is infinite; theorem statements therefore require $S$ to be nonempty.
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), paragraph before Theorem 3.6, p.5 (PDF p.8)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_cost2

namespace KMeansTaper
namespace Supplement

open OAI.MetricKMedian (Instance nearest)

/-- **Power cost** `cost_p(S) = ∑_{j ∈ J} d(j,S)^p`, introduced immediately before
Theorem 3.6, p.5 (PDF p.8).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

**Formalization Note.** The exponent is a real number and exponentiation is `Real.rpow`.
`nearest I j S` is `0` when `S` is empty, whereas the paper's distance to the empty set is
infinite; every theorem using `powerCost` therefore requires `S.Nonempty`. -/
noncomputable def powerCost (I : Instance) (p : ℝ) (S : Finset (Fin I.n)) : ℝ :=
  ∑ j ∈ I.clients, (nearest I j S) ^ p

/-- At exponent two, `powerCost` is exactly the published squared cost `cost2`. -/
@[simp] theorem powerCost_two (I : Instance) (S : Finset (Fin I.n)) :
    powerCost I 2 S = cost2 I S := by
  simp [powerCost, cost2]

end Supplement
end KMeansTaper


