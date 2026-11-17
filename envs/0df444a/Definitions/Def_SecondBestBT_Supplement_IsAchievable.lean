-- Prove2me | Definitions.Def_SecondBestBT_Supplement_IsAchievable
-- name    : SecondBestBT_Supplement_IsAchievable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:33:45.421201+00:00
-- url     : https://prove2.me/theorems/afd9480a-2ec0-4e90-bf8f-ee9af1dd372a
-- title:
--   Achievable indexed state (Definition 5.1)
-- statement:
--   An **indexed state** is $\omega=(y;r_t,r_{t+1},\dots,r_m)$ with $y\in(0,1]$, $0\le t\le m$, $r_t\in\mathbb R_{\ge0}$ and $r_i\in\mathbb R_{>0}\cup\{\infty\}$ for $i>t$.
--
--   A state is **achievable** (for parameters $\alpha,\beta$) if there exist $K\ge0$, an $\alpha$-weakly regular seller prior $F_S$ with full support on $\{0,\dots,K\}$, and a buyer value $b\ge1$ such that Algorithm 1 successfully processes $b$, ending with threshold $t_b$ and allocation $x$, and
--   $$
--   m=b-1,\qquad t=t_b,\qquad y=x(t_b,b),\qquad (r_t,\dots,r_m)=\text{the entries }t_b,\dots,b-1\text{ of }F_S\text{'s global ratio sequence}.
--   $$
--   Ratios beyond $K$ are $\infty$.
--
--   Achievable states are the states that the greedy construction can actually reach; Section 5 compares them under the dominance order.
--
--   **Formalization Note** A state is a pair $(y,\text{list of ratio values})$; the threshold index is not stored. Algorithm 1 is the published `SecondBestBT.greedyRun`. The conditions $b\ge1$, $t_b<b$ and $y\in(0,1]$ are the coordinate conditions of an indexed state. Section 5 uses $\beta=1/2$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Definition 5.1, p.16

import Mathlib
import Definitions.Def_SecondBestBT_IsFullSupportOn
import Definitions.Def_SecondBestBT_IsAlphaWeaklyRegular
import Definitions.Def_SecondBestBT_greedyRun
import Definitions.Def_SecondBestBT_Supplement_globalRatio

open scoped ENNReal

namespace SecondBestBT.Supplement

/-- An **achievable** indexed state (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Definition 5.1, p.16). An indexed state is
`ω = (y ; r_t, r_{t+1}, …, r_m)` with `y ∈ (0, 1]` and `0 ≤ t ≤ m`. It is achievable if there
exist an `α`-weakly regular seller prior `F_S` with full support on `{0, …, K}` for some `K ≥ 0`
and a buyer value `b` such that Algorithm 1 (with parameters `α, β`) reaches `ω` after
successfully processing `b`, with `m = b − 1`, `t = t_b`, `y = x(t_b, b)`, and
`(r_t, …, r_m)` the corresponding entries of `F_S`'s global ratio sequence.

**Formalization Note** A state is a pair `(y, [r_t, …, r_m])` of a real and a list of values in
`ℝ≥0∞`; the threshold index `t` is not stored (as in the paper's notation, which records only
the ratio values). Algorithm 1 is the published `SecondBestBT.greedyRun`, which returns
`some (x, t_b)` after successfully processing `b`. `b ≥ 1` and `t_b < b` are the conditions
`0 ≤ t ≤ m = b − 1` of Definition 5.1; `y ∈ (0, 1]` is the state's coordinate condition. Ratios
beyond `K` are `∞` (`globalRatio`). Section 5 uses `β = 1/2`; the theorems pass `β = 1/2`. -/
def IsAchievable (α β : ℝ) (ω : ℝ × List ℝ≥0∞) : Prop :=
  ω.1 ∈ Set.Ioc (0 : ℝ) 1 ∧
  ∃ (K : ℕ) (fS : ℕ → ℝ) (b : ℕ) (x : ℕ → ℕ → ℝ) (t : ℕ),
    IsFullSupportOn fS K ∧ IsAlphaWeaklyRegular α fS K ∧ 1 ≤ b ∧ t < b ∧
    greedyRun α β K fS b = some (x, t) ∧
    ω.1 = x t b ∧ ω.2 = (List.range (b - t)).map (fun j => globalRatio fS (t + j))

end SecondBestBT.Supplement


