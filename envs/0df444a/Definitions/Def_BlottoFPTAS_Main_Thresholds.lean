-- Prove2me | Definitions.Def_BlottoFPTAS_Main_Thresholds
-- name    : BlottoFPTAS_Main_Thresholds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:39:59.513208+00:00
-- url     : https://prove2.me/theorems/017087e5-942f-40ca-a407-3e58f7cd226e
-- title:
--   Open and closed choices of an opposing bid at thresholds, and the affordability condition (10)
-- statement:
--   Suppose the player's bids on battlefield $j$ lie in a finite set $T_j\subseteq[0,\infty)$ of thresholds containing $0$. An opposing bid $y_j\ge0$ makes the **closed choice** at $t\in T_j$ if $y_j=t$, and the **open choice** at $t$ if $y_j\notin T_j$ and $t$ is the largest threshold below $y_j$. A choice is encoded by its threshold $t_j$ and a flag (open or closed). A tuple of choices is **affordable** for the budget $c'$ (condition (10)) when $\sum_jt_j\le c'$, with strict inequality if at least one choice is open.
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 32, §5.2 (deviations against finitely many bids; (10))

import Mathlib

open scoped BigOperators

namespace BlottoFPTAS.Main

/-!
# Open and closed choices at thresholds (§5.2, p. 32)

On each battlefield `j` the player's bids lie in a finite set `T_j ⊆ [0, ∞)` of thresholds that
contains `0`. A bid `y_j ≥ 0` of the opponent makes exactly one choice:
* the **closed choice** at `t ∈ T_j` if `y_j = t`;
* the **open choice** at `t` if `y_j ∉ T_j` and `t` is the largest threshold below `y_j`.

A choice is encoded by its threshold `t` and a flag `isOpen : Bool`. A tuple of choices
`(t_j, o_j)_j` satisfies condition (10) for the budget `c'` (`Affordable`) when `∑_j t_j ≤ c'`,
with strict inequality if at least one choice is open.
-/

/-- The bid `y` makes the choice `(t, isOpen)` against the threshold set `T`. -/
def Makes (T : Finset ℝ) (t : ℝ) (isOpen : Bool) (y : ℝ) : Prop :=
  if isOpen then y ∉ T ∧ t < y ∧ ∀ t' ∈ T, t' < y → t' ≤ t else y = t

/-- Condition (10): `∑_j t_j ≤ c'`, strictly if some choice is open. -/
def Affordable {m : ℕ} (t : Fin m → ℝ) (o : Fin m → Bool) (c' : ℝ) : Prop :=
  ∑ j, t j ≤ c' ∧ ((∃ j, o j = true) → ∑ j, t j < c')

end BlottoFPTAS.Main


