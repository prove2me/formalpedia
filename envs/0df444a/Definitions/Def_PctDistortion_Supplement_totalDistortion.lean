-- Prove2me | Definitions.Def_PctDistortion_Supplement_totalDistortion
-- name    : PctDistortion_Supplement_totalDistortion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:29:29.432968+00:00
-- url     : https://prove2.me/theorems/ab8a53d5-afc8-406b-b596-1ac1063fbda8
-- title:
--   Total cost and total-cost distortion
-- statement:
--   Let $\mathcal E=(V,\mathcal C,\vec\succ)$ be an election and $d$ a metric consistent with its rankings. The **total cost** of a candidate and of a lottery $p\in\Delta\mathcal C$ are
--   $$\mathrm{cost}^+_d(c)=\sum_{v\in V}d(v,c),\qquad \mathrm{cost}^+_d(p)=\sum_{c\in\mathcal C}p_c\,\mathrm{cost}^+_d(c).$$
--   The **total-cost distortion** of $p$ is
--   $$\mathrm{dist}^+_{\mathcal E}(p)=\sup_{d\sim\vec\succ}\frac{\mathrm{cost}^+_d(p)}{\min_{c\in\mathcal C}\mathrm{cost}^+_d(c)},$$
--   the supremum over all metrics (nonnegative, satisfying the quadrilateral inequality) consistent with $\vec\succ$.
--
--   This is the classical utilitarian distortion measure, used in Theorem 12.
--
--   **Formalization Note** As for the mission's α-percentile distortion, the ratio is taken in $[0,\infty]$ with $x/0=\infty$ for $x>0$ and $0/0=0$, so $\mathrm{dist}^+_{\mathcal E}(p)\le B$ iff $\mathrm{cost}^+_d(p)\le B\cdot\min_c\mathrm{cost}^+_d(c)$ for every consistent metric. Metrics and consistency are the published `IsMetric` and `Consistent`.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), App. C, p.32

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_IsMetric

set_option autoImplicit false

namespace PctDistortion.Supplement

open PctDistortion

/-- The **total cost** `cost⁺_d(c) = Σ_{v ∈ V} d(v, c)` of candidate `c` under `d`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), App. C, p.32. -/
noncomputable def totalCost {V C : Type} [Fintype V] (d : V → C → ℝ) (c : C) : ℝ :=
  ∑ v, d v c

/-- The total cost of a lottery: `cost⁺_d(p) = E_{c∼p}[cost⁺_d(c)] = Σ_c p_c · cost⁺_d(c)`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), App. C, p.32. -/
noncomputable def lotteryTotalCost {V C : Type} [Fintype V] [Fintype C] (d : V → C → ℝ)
    (p : C → ℝ) : ℝ :=
  ∑ c, p c * totalCost d c

/-- The **total-cost distortion** of a lottery `p` in the election `E`:
`dist⁺_E(p) = sup_{d ∼ ≻⃗} cost⁺_d(p) / min_{c ∈ C} cost⁺_d(c)`, over all metrics `d`
(nonnegative, quadrilateral inequality) consistent with the rankings of `E`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), App. C, p.32: "the total-cost distortion of a lottery p ∈ ∆C for a given election
E = (V, C, ≻⃗) is dist⁺_E(p) = sup_{d∼≻⃗} cost⁺_d(p) / min_{c∈C} cost⁺_d(c)".

**Formalization Note.** As for the published α-percentile `distortion`, the ratio is taken in
`ℝ≥0∞` (`x / 0 = ⊤` for `x > 0`, `0 / 0 = 0`), so `dist⁺_E(p) ≤ B` holds exactly when
`cost⁺_d(p) ≤ B · min_c cost⁺_d(c)` for every consistent metric. Metrics and consistency are the
published `IsMetric` and `Consistent`. -/
noncomputable def totalDistortion {V C : Type} [Fintype V] [Fintype C] (E : Election V C)
    (p : C → ℝ) : ENNReal :=
  ⨆ (d : V → C → ℝ) (_ : IsMetric d ∧ Consistent E d),
    ENNReal.ofReal (lotteryTotalCost d p) / ENNReal.ofReal (⨅ c, totalCost d c)

end PctDistortion.Supplement


