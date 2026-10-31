-- Prove2me | Definitions.Def_StengelZeroSum_IsSuitableM
-- name    : StengelZeroSum_IsSuitableM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:03:47.610984+00:00
-- url     : https://prove2.me/theorems/db3999e1-545e-48a4-9caf-466f16009262
-- title:
--   The properties of $M$ in Theorem 7
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb R^m$, $c\in\mathbb R^n$, consider the primal LP (1) $\max c^\top x$ subject to $Ax\le b$, $x\ge\mathbf0$ and its dual (2) $\min y^\top b$ subject to $A^\top y\ge c$, $y\ge\mathbf 0$, and let $B_M$ be the game (51). A real number $M$ **has the properties of Theorem 7** if:
--
--   1. if (1) and (2) are both feasible, they have feasible solutions $x$ and $y$ with $\mathbf 1^\top x+\mathbf 1^\top y+1\le M$;
--   2. the game $B_M$ has a value;
--   3. every value $v$ of $B_M$ satisfies $v\ge0$ and
--      - (a) $v=0$ if and only if (1) and (2) are feasible; and if $v=0$, then for **every** min-max strategy $(y,x,t)$ of $B_M$ (one exists, because $v$ is a value), $(y,x,t,0)$ is a max-min strategy (with max-min value $0$), $t>0$, $x\frac1t$ is optimal for (1) and $y\frac1t$ is optimal for (2);
--      - (b) if $v>0$, then $v<1$; (1) and (2) are not both feasible; every max-min strategy $(y,x,r,s)$ of $B_M$ satisfies $r=0$, $s=v$ and
--      $$Ax\le\mathbf0,\quad x\ge\mathbf0,\quad A^\top y\ge\mathbf0,\quad y\ge\mathbf0,\quad b^\top y-c^\top x<0;\qquad(52)$$
--      and the smallest $w$ for which (53) has feasible solutions exists and equals
--      $$w=\frac{M+1}{1/v-1}.\qquad(54)$$
--
--   **Formalization Note** Min-max strategies are those of the minimizing column player, max-min strategies those of the maximizing row player (the published game vocabulary). "The smallest $w$" is a least element, which is attained.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 7, p.18

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair
import Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame
import Definitions.Def_StengelZeroSum_extGame
import Definitions.Def_StengelZeroSum_Feasible53

open Matrix VanderbeiLP.StrictComp ZeroSumLP.DantzigExt

namespace StengelZeroSum

/-- `M` **has the properties of Theorem 7**,
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Theorem 7,
p.18 ("There is some M ∈ ℝ with the following properties"), for the LP (1)
`max c⊤x s.t. Ax ≤ b, x ≥ 0` and its dual (2) `min y⊤b s.t. y⊤A ≥ c⊤, y ≥ 0`:

* if (1) and (2) are feasible, they have feasible `x`, `y` with `1⊤x + 1⊤y + 1 ≤ M`;
* the game `B_M` of (51) has a value, and every value `v` of `B_M` satisfies `v ≥ 0` and
  * (a) `v = 0` iff (1) and (2) are feasible; and if `v = 0`, then for every min-max strategy
    `(y, x, t)` of `B_M` (one exists, because `v` is a value), `(y, x, t, 0)` is a max-min
    strategy (value 0), `t > 0`, `x(1/t)` is optimal for (1) and `y(1/t)` is optimal for (2);
  * (b) if `v > 0`: `v < 1`; (1) and (2) are not both feasible; every max-min strategy
    `(y, x, r, s)` of `B_M` has `r = 0`, `s = v` and satisfies (52)
    `Ax ≤ 0, x ≥ 0, A⊤y ≥ 0, y ≥ 0, b⊤y − c⊤x < 0`; and the smallest `w` for which (53) is
    feasible is `w = (M + 1)/(1/v − 1)` (54).

**Formalization Note** Column strategies `(y, x, t)` are functions on `(Fin m ⊕ Fin n) ⊕ Unit`,
row strategies `(y, x, r, s)` functions on `((Fin m ⊕ Fin n) ⊕ Unit) ⊕ Unit` (see `extGame`).
Min-max strategies are those of the column (minimizing) player, `IsMinMaxStrategy`; max-min
strategies those of the row (maximizing) player, `IsMaxMinStrategy`. "The smallest number w" is
`IsLeast`, which also asserts that it is attained. -/
def IsSuitableM {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (M : ℝ) : Prop :=
  ((∃ x, PrimalFeasible A b x) ∧ (∃ y, DualFeasible A c y) →
      ∃ x y, PrimalFeasible A b x ∧ DualFeasible A c y ∧ ∑ j, x j + ∑ i, y i + 1 ≤ M) ∧
  (∃ v, IsGameValue (extGame A b c M) v) ∧
  ∀ v, IsGameValue (extGame A b c M) v →
    0 ≤ v ∧
    -- (a)
    (v = 0 ↔ (∃ x, PrimalFeasible A b x) ∧ ∃ y, DualFeasible A c y) ∧
    (v = 0 → ∀ z : (Fin m ⊕ Fin n) ⊕ Unit → ℝ, IsMinMaxStrategy (extGame A b c M) z 0 →
        IsMaxMinStrategy (extGame A b c M) (Sum.elim z fun _ => 0) 0 ∧
        0 < z (.inr ()) ∧
        PrimalOptimal A b c (fun j => z (.inl (.inr j)) / z (.inr ())) ∧
        DualOptimal A b c (fun i => z (.inl (.inl i)) / z (.inr ()))) ∧
    -- (b)
    (0 < v →
        v < 1 ∧
        ¬((∃ x, PrimalFeasible A b x) ∧ ∃ y, DualFeasible A c y) ∧
        (∀ (q : ((Fin m ⊕ Fin n) ⊕ Unit) ⊕ Unit → ℝ) (u : ℝ),
          IsMaxMinStrategy (extGame A b c M) q u →
          q (.inl (.inr ())) = 0 ∧ q (.inr ()) = v ∧
          A *ᵥ (fun j => q (.inl (.inl (.inr j)))) ≤ 0 ∧
          0 ≤ (fun j => q (.inl (.inl (.inr j)))) ∧
          0 ≤ Aᵀ *ᵥ (fun i => q (.inl (.inl (.inl i)))) ∧
          0 ≤ (fun i => q (.inl (.inl (.inl i)))) ∧
          b ⬝ᵥ (fun i => q (.inl (.inl (.inl i)))) - c ⬝ᵥ (fun j => q (.inl (.inl (.inr j)))) < 0) ∧
        IsLeast {w : ℝ | Feasible53 A b c w} ((M + 1) / (1 / v - 1)))

end StengelZeroSum


