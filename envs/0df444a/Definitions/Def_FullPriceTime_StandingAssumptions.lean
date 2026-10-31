-- Prove2me | Definitions.Def_FullPriceTime_StandingAssumptions
-- name    : FullPriceTime_StandingAssumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:05.146337+00:00
-- url     : https://prove2.me/theorems/e2644340-a35c-43cd-a91d-785060e07b69
-- title:
--   Standing assumptions on the leisure utility $U$ and the overhead time $O$
-- statement:
--   Let $U(t_l,c_l)$ be the consumer's utility from leisure time $t_l$ and leisure consumption $c_l$, and let $O(c_O)$ be the time spent on overhead activities when $c_O$ is spent to reduce them. The **standing assumptions** of the model are:
--
--   1. $U$ is continuous on the closed quadrant $\{t_l\ge 0,\ c_l\ge 0\}$;
--   2. $U$ is non-decreasing in $t_l$ for every fixed $c_l\ge 0$, and non-decreasing in $c_l$ for every fixed $t_l\ge 0$;
--   3. $U$ is concave in $t_l$ for every fixed $c_l\ge 0$, and concave in $c_l$ for every fixed $t_l\ge 0$;
--   4. $U(0,c_l)\ge 0$ for all $c_l\ge 0$ and $U(t_l,0)\ge 0$ for all $t_l\ge 0$;
--   5. $O$ is strictly decreasing on $[0,\infty)$;
--   6. $O$ is strictly convex on $[0,\infty)$ (diminishing returns to buying overhead time back).
--
--   These are the assumptions under which every result of the paper is stated.
--
--   **Formalization Note** $U$ is a function on $\mathbb R\times\mathbb R$ and every condition is imposed only on the closed quadrant, where problem (PC) evaluates it. "Concave in both arguments" is read as concave in each argument separately, the weaker of its two readings. "Decreasing" is encoded as strictly decreasing; for a strictly convex function on $[0,\infty)$ the two notions coincide. No sign, continuity or differentiability is assumed for $O$, since the paper assumes none.
-- source:
--   Li, Lariviere, Bassamboo, Is Full Price the Full Story When Consumers Have Time and Budget Constraints?, SSRN 4223388, §2.1, p.5 (assumptions on U and O)

import Mathlib

namespace FullPriceTime

/-- **Standing assumptions on the leisure utility `U` and the overhead-time function `O`.**
Li, Lariviere, Bassamboo, *Is Full Price the Full Story When Consumers Have Time and Budget
Constraints?*, SSRN 4223388, §2.1, p.5 (PDF p.5): "We assume U(tl,cl) to be continuous,
non-decreasing and concave in both arguments. In addition, U(0,cl) and U(tl,0) are assumed to be
non-negative for all cl ≥ 0 and tl ≥ 0." and "We assume O(cO) to be decreasing and strictly
convex in cO".

`StandingAssumptions U O` holds when, on the closed quadrant `t_l, c_l ≥ 0`,
1. `U` is continuous;
2. `U` is non-decreasing in `t_l` for every fixed `c_l ≥ 0`, and in `c_l` for every fixed `t_l ≥ 0`;
3. `U` is concave in `t_l` for every fixed `c_l ≥ 0`, and in `c_l` for every fixed `t_l ≥ 0`;
4. `U(0, c_l) ≥ 0` for every `c_l ≥ 0` and `U(t_l, 0) ≥ 0` for every `t_l ≥ 0`;
and on `c_O ≥ 0`,
5. `O` is strictly decreasing;
6. `O` is strictly convex.

**Formalization Note** `U` is a function on `ℝ × ℝ` (pairs `(t_l, c_l)`) and every condition is
imposed only on the closed quadrant, where (PC) evaluates it. "Concave in both arguments" is read
as concave in each argument separately, the weaker of its two readings (joint concavity implies
it). "Decreasing" is read as strictly decreasing (`StrictAntiOn`). No sign, continuity or
differentiability is assumed for `O`, since the paper assumes none. -/
def StandingAssumptions (U : ℝ × ℝ → ℝ) (O : ℝ → ℝ) : Prop :=
  ContinuousOn U (Set.Ici 0 ×ˢ Set.Ici 0) ∧
  (∀ cl, 0 ≤ cl → MonotoneOn (fun tl => U (tl, cl)) (Set.Ici 0)) ∧
  (∀ tl, 0 ≤ tl → MonotoneOn (fun cl => U (tl, cl)) (Set.Ici 0)) ∧
  (∀ cl, 0 ≤ cl → ConcaveOn ℝ (Set.Ici 0) (fun tl => U (tl, cl))) ∧
  (∀ tl, 0 ≤ tl → ConcaveOn ℝ (Set.Ici 0) (fun cl => U (tl, cl))) ∧
  (∀ cl, 0 ≤ cl → 0 ≤ U (0, cl)) ∧
  (∀ tl, 0 ≤ tl → 0 ≤ U (tl, 0)) ∧
  StrictAntiOn O (Set.Ici 0) ∧
  StrictConvexOn ℝ (Set.Ici 0) O

end FullPriceTime


