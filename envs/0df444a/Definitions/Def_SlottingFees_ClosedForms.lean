-- Prove2me | Definitions.Def_SlottingFees_ClosedForms
-- name    : SlottingFees_ClosedForms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:35.957597+00:00
-- url     : https://prove2.me/theorems/38c3ccbd-c78d-47fb-8ae7-d176c3b1bdf7
-- title:
--   Attractiveness $v_l$, $\bar v$, $v_{12}$, $S^{|2|}$ and the parameter set $\Omega$
-- statement:
--   The closed-form quantities that the paper's statements name.
--
--   1. The **attractiveness** of product $l$: $v_l=(q_l-c_l)^2/q_l$ (p.11), and the relative attractiveness of product 1, $r=v_1/(v_1+v_2)$.
--   2. From Proposition 2 (p.15):
--   $$
--   \bar v=\frac{(2q_1-q_2)^2}{q_1q_2+(2q_1-q_2)^2},\qquad
--   v_{12}=\frac{q_1^2(4q_1-3q_2)(v_1+v_2)-2q_1q_2\sqrt{q_1v_1q_2v_2}}{4(q_1-q_2)(4q_1-q_2)^2}.
--   $$
--   3. The slotting fee (17):
--   $$
--   S^{|2|}=\begin{cases}\dfrac{\min\{((2q_1-q_2)\sqrt{q_1v_1}-q_1\sqrt{q_2v_2})^2,\ ((2q_1-q_2)\sqrt{q_1v_2}-q_1\sqrt{q_2v_1})^2\}}{2(q_1-q_2)(4q_1-q_2)^2} & r\in(1-\bar v,\bar v),\\ 0&\text{otherwise.}\end{cases}
--   $$
--   4. The feasible parameter set (p.16):
--   $$
--   \Omega=\Bigl\{\omega\in\mathbb R^5:\ 0\le K\le\min\Bigl\{\tfrac{(q_1-c_1)^2}{16q_1},\tfrac{(q_2-c_2)^2}{16q_2}\Bigr\},\ q_1>c_1\ge0,\ q_2>c_2\ge 0,\ \tfrac{q_1}{2q_1-q_2}<\tfrac{q_1-c_1}{q_2-c_2}<\tfrac{2q_1-q_2}{q_2}\Bigr\}.
--   $$
--
--   The equilibrium quantities of the game are not defined by these formulas; the theorems of the mission prove that they equal them.
--
--   **Formalization Note** Transcribed literally; product 1 is index $0$. The first branch of (17) is the separate definition `S2min`, which (19) uses. The chain of inequalities in $\Omega$ implies $q_1>q_2$.
-- source:
--   Alan–Kurtuluş–Nakkas, Retail Category Management with Slotting Fees, MSOM (2024), doi:10.1287/msom.2022.0143, Lemma 2 preamble, p.11; Proposition 2, (17), p.15; definition of Ω, p.16

import Mathlib
import Definitions.Def_SlottingFees_Model

namespace SlottingFees

/-- Attractiveness of product `l`, `v_l ≡ (q_l − c_l)²/q_l`, p.11 (before Lemma 2). -/
noncomputable def Params.v (ω : Params) (l : Fin 2) : ℝ := (ω.q l - ω.c l) ^ 2 / ω.q l

/-- Relative attractiveness of product 1, `v₁/(v₁ + v₂)` (p.13, Proposition 1 and Figure 2).
**Formalization Note** Product 1 is index `0`. -/
noncomputable def Params.ratio (ω : Params) : ℝ := ω.v 0 / (ω.v 0 + ω.v 1)

/-- `v̄ ≡ (2q₁ − q₂)²/(q₁q₂ + (2q₁ − q₂)²)`, Proposition 2, p.15. -/
noncomputable def Params.vbar (ω : Params) : ℝ :=
  (2 * ω.q 0 - ω.q 1) ^ 2 / (ω.q 0 * ω.q 1 + (2 * ω.q 0 - ω.q 1) ^ 2)

/-- `v₁₂ ≡ (q₁²(4q₁ − 3q₂)(v₁ + v₂) − 2q₁q₂√(q₁v₁q₂v₂)) / (4(q₁ − q₂)(4q₁ − q₂)²)`,
Proposition 2, p.15. -/
noncomputable def Params.v12 (ω : Params) : ℝ :=
  (ω.q 0 ^ 2 * (4 * ω.q 0 - 3 * ω.q 1) * (ω.v 0 + ω.v 1)
      - 2 * ω.q 0 * ω.q 1 * Real.sqrt (ω.q 0 * ω.v 0 * ω.q 1 * ω.v 1))
    / (4 * (ω.q 0 - ω.q 1) * (4 * ω.q 0 - ω.q 1) ^ 2)

/-- The first branch of (17), p.15 (and the last row of (19), p.17):
`min{((2q₁−q₂)√(q₁v₁) − q₁√(q₂v₂))², ((2q₁−q₂)√(q₁v₂) − q₁√(q₂v₁))²} / (2(q₁−q₂)(4q₁−q₂)²)`. -/
noncomputable def Params.S2min (ω : Params) : ℝ :=
  min (((2 * ω.q 0 - ω.q 1) * Real.sqrt (ω.q 0 * ω.v 0)
          - ω.q 0 * Real.sqrt (ω.q 1 * ω.v 1)) ^ 2)
      (((2 * ω.q 0 - ω.q 1) * Real.sqrt (ω.q 0 * ω.v 1)
          - ω.q 0 * Real.sqrt (ω.q 1 * ω.v 0)) ^ 2)
    / (2 * (ω.q 0 - ω.q 1) * (4 * ω.q 0 - ω.q 1) ^ 2)

/-- The slotting fee `S^{|2|}` of (17), Proposition 2, p.15: `S2min` if
`v₁/(v₁+v₂) ∈ (1 − v̄, v̄)`, and `0` otherwise. -/
noncomputable def Params.S2 (ω : Params) : ℝ :=
  if 1 - ω.vbar < ω.ratio ∧ ω.ratio < ω.vbar then ω.S2min else 0

/-- The feasible parameter set Ω, §4.3, p.16:
`Ω ≡ {(q₁,q₂,c₁,c₂,K) ∈ ℝ⁵ | 0 ≤ K ≤ min{(q₁−c₁)²/(16q₁), (q₂−c₂)²/(16q₂)}, q₁ > c₁ ≥ 0,
q₂ > c₂ ≥ 0, q₁/(2q₁−q₂) < (q₁−c₁)/(q₂−c₂) < (2q₁−q₂)/q₂}`.

**Formalization Note** Transcribed literally. It implies the standing assumption `q₁ > q₂`
(the chain forces `2q₁ > q₂` and then `q₁/(2q₁ − q₂) < (2q₁ − q₂)/q₂`, i.e. `q₁ > q₂`). -/
def Omega : Set Params :=
  {ω | 0 ≤ ω.K ∧
    ω.K ≤ min ((ω.q 0 - ω.c 0) ^ 2 / (16 * ω.q 0)) ((ω.q 1 - ω.c 1) ^ 2 / (16 * ω.q 1)) ∧
    ω.c 0 < ω.q 0 ∧ 0 ≤ ω.c 0 ∧ ω.c 1 < ω.q 1 ∧ 0 ≤ ω.c 1 ∧
    ω.q 0 / (2 * ω.q 0 - ω.q 1) < (ω.q 0 - ω.c 0) / (ω.q 1 - ω.c 1) ∧
    (ω.q 0 - ω.c 0) / (ω.q 1 - ω.c 1) < (2 * ω.q 0 - ω.q 1) / ω.q 1}

end SlottingFees


