-- Prove2me | Definitions.Def_PctDistortion_distortion
-- name    : PctDistortion_distortion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:04.975756+00:00
-- url     : https://prove2.me/theorems/33762a63-cde9-4122-b1e1-7e1be025e23f
-- title:
--   α-percentile distortion of a lottery
-- statement:
--   Given an election $\mathcal E=(V,C,\vec\succ)$ and $\alpha$, the **α-percentile distortion** of a lottery $p\in\Delta C$ is the largest ratio between the cost of $p$ and that of an optimal candidate, over all metrics consistent with the rankings:
--   $$\mathrm{dist}^\alpha_{\mathcal E}(p)=\sup_{d\sim\vec\succ}\frac{\mathrm{cost}^\alpha_d(p)}{\min_{c\in C}\mathrm{cost}^\alpha_d(c)}.$$
--   The distortion of a rule is the supremum of this quantity over all elections.
--
--   **Formalization Note** The ratio is computed in $[0,\infty]$ with $x/0=\infty$ for $x>0$ and $0/0=0$. Hence $\mathrm{dist}^\alpha_{\mathcal E}(p)\le B$ holds exactly when $\mathrm{cost}^\alpha_d(p)\le B\cdot\min_c\mathrm{cost}^\alpha_d(c)$ for every consistent metric $d$, the form in which the paper proves its bounds.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Definition 1, p.8

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_IsMetric
import Definitions.Def_PctDistortion_percentileCost

set_option autoImplicit false

namespace PctDistortion

/-- The **α-percentile distortion** of a lottery `p` in the election `E`:
`dist^α_E(p) = sup_{d ∼ ≻⃗} cost^α_d(p) / min_{c ∈ C} cost^α_d(c)`, the supremum over all metrics
`d` (quadrilateral inequality, nonnegative) consistent with the rankings of `E`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Definition 1, p.8: "the α-percentile distortion of a lottery p ∈ ∆C is the largest possible
ratio between the cost of p and that of an optimal candidate, over all metrics d ∼ ≻⃗:
dist^α_E(p) := sup_{d∼≻⃗} cost^α_d(p) / min_{c∈C} cost^α_d(c)."

**Formalization Note.** The ratio is taken in `ℝ≥0∞`: `x / 0 = ⊤` for `x > 0` (an optimal cost
`0` with a positive lottery cost is unbounded distortion) and `0 / 0 = 0` (the zero metric
contributes nothing). With this convention `dist^α_E(p) ≤ B` holds exactly when
`cost^α_d(p) ≤ B · min_c cost^α_d(c)` for every consistent metric `d`. The minimum over the
finite candidate set is the real infimum `⨅ c`. -/
noncomputable def distortion {V C : Type} [Fintype V] [Fintype C] (α : ℝ) (E : Election V C)
    (p : C → ℝ) : ENNReal :=
  ⨆ (d : V → C → ℝ) (_ : IsMetric d ∧ Consistent E d),
    ENNReal.ofReal (lotteryCost α d p) / ENNReal.ofReal (⨅ c, percentileCost α d c)

end PctDistortion


