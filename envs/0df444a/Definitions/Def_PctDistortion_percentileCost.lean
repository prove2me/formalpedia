-- Prove2me | Definitions.Def_PctDistortion_percentileCost
-- name    : PctDistortion_percentileCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:03.461199+00:00
-- url     : https://prove2.me/theorems/4f8d7834-ac82-4624-9e35-efd9274a7964
-- title:
--   The α-percentile cost of a candidate and of a lottery
-- statement:
--   Let $n=|V|$ and $\alpha\in[0,1)$. The **α-percentile cost** of a candidate $c$ under a metric $d$ is the $\lfloor\alpha n+1\rfloor$-th smallest voter cost of $c$:
--   $$\mathrm{cost}^\alpha_d(c)=\min^{\lfloor\alpha n+1\rfloor}_{v\in V} d(v,c),$$
--   i.e. the $(\lfloor\alpha n\rfloor+1)$-st smallest of the numbers $d(v,c)$, $v\in V$, counted with multiplicity. For $\alpha=1/2$ this is the median cost and for $\alpha\in[1-1/n,1)$ the maximum cost. For a lottery $p\in\Delta C$,
--   $$\mathrm{cost}^\alpha_d(p)=\sum_{c\in C}p_c\,\mathrm{cost}^\alpha_d(c).$$
--
--   **Formalization Note** The $k$-th smallest value is written as the least voter cost $t=d(v,c)$ such that at least $k=\lfloor\alpha n+1\rfloor$ voters $w$ have $d(w,c)\le t$. For $0\le\alpha<1$ and $n\ge 1$, $1\le k\le n$, so this least value exists.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), §2.1, p.8

import Mathlib

set_option autoImplicit false

namespace PctDistortion

open Classical in
/-- The **α-percentile cost** `cost^α_d(c)` of candidate `c` under `d`: the
`⌊αn + 1⌋`-th smallest of the voter costs `d(v, c)`, `v ∈ V` (`n = |V|`).

It is defined as the least voter cost `t = d(v, c)` such that at least `⌊αn + 1⌋` voters `w`
have `d(w, c) ≤ t`; this is the `⌊αn + 1⌋`-th smallest entry of the list of voter costs
(counted with multiplicity).

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2.1, p.8: "the α-percentile cost of a candidate c under a metric d ∼ ≻⃗ is defined by
cost^α_d(c) = min^{⌊αn+1⌋}_{v∈V} d(v, c), that is, the (⌊αn⌋+1)st smallest voter cost of
candidate c."

**Formalization Note.** For `0 ≤ α < 1` and `n ≥ 1` the rank `⌊αn + 1⌋ = ⌊αn⌋ + 1` lies in
`[1, n]`, so the set below is finite and nonempty and its infimum is attained. The value for
`n = 0` (empty set, value `0`) never occurs: every theorem assumes nonempty voters. -/
noncomputable def percentileCost {V C : Type} [Fintype V] (α : ℝ) (d : V → C → ℝ) (c : C) : ℝ :=
  sInf {t : ℝ | ∃ v, d v c = t ∧
    ⌊α * (Fintype.card V : ℝ) + 1⌋₊ ≤ (Finset.univ.filter (fun w => d w c ≤ t)).card}

/-- The α-percentile cost of a lottery `p` over candidates, in expectation:
`cost^α_d(p) = Σ_c p_c · cost^α_d(c)`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2.1, p.8: "given a lottery p ∈ ∆C, we write cost^α_d(p) = E_{c∼p}[cost^α_d(c)] =
Σ_{c∈C} p_c · cost^α_d(c)." -/
noncomputable def lotteryCost {V C : Type} [Fintype V] [Fintype C] (α : ℝ) (d : V → C → ℝ)
    (p : C → ℝ) : ℝ :=
  ∑ c, p c * percentileCost α d c

end PctDistortion


