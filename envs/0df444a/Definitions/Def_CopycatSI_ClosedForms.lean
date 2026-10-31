-- Prove2me | Definitions.Def_CopycatSI_ClosedForms
-- name    : CopycatSI_ClosedForms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:25.29706+00:00
-- url     : https://prove2.me/theorems/2415a8cb-b83f-4bef-83f6-efef0d7c6490
-- title:
--   The threshold $\beta^*$, the cutoff $h_1(\beta)$ and the entries of Tables 1 and 2 (Table 2 rows $q_2$, $s_C$, $\pi_C$ corrected)
-- statement:
--   The closed-form quantities named by Proposition 2 and the entries of Tables 1 and 2, used only as right-hand sides of the theorems.
--
--   1. $\beta^*=(\sqrt{73}-5)/6\approx 0.5907$, the root in $[0,1)$ of $3\beta^2+5\beta-4=0$.
--   2. The holding-cost cutoff of Table 2:
--   $$
--   h_1(\beta)=\frac{1-\beta}{(2-\beta)(4-3\beta)}\Bigl(2-\beta-\frac{\beta}{2}\sqrt{\frac{17-13\beta}{1-\beta}}\Bigr).
--   $$
--   3. An outcome **matches Table 1** if $(w_1,w_2)=\bigl(\tfrac12,\tfrac{1-\beta}{2-\beta}\bigr)$, $(s_1,s_2)=(\tfrac14,\tfrac14)$, $(p_1,p_2)=\bigl(\tfrac34,\tfrac{3(1-\beta)}{2(2-\beta)}\bigr)$, $(\pi_S,\pi_R)=\bigl(\tfrac{4-3\beta}{8(2-\beta)},\tfrac{4-3\beta}{16(2-\beta)}\bigr)$, and, when $\beta>0$, $s_C=\tfrac{3}{4(2-\beta)}$, $p_C=\tfrac{3\beta(1-\beta)}{4(2-\beta)}$, $\pi_C=\tfrac{9\beta(1-\beta)}{16(2-\beta)^2}$.
--   4. An outcome **matches Table 2** if all fourteen of its entries equal the Condition I column of Table 2 (copycat rows when $\beta>0$), with three rows corrected:
--   $$
--   q_2=\frac{3(2-\beta)}{2(17-13\beta)}+\frac{h(2-\beta)(5-4\beta)}{2(1-\beta)(17-13\beta)},\qquad
--   s_C=\frac{1}{2(17-13\beta)}\Bigl(\frac{23-16\beta}{2-\beta}+\frac{h(5-4\beta)}{1-\beta}\Bigr),
--   $$
--   $$
--   \pi_C=\frac{\beta}{16(1-\beta)(2-\beta)^2}\Bigl(\frac{2(2-\beta)}{13}\Bigl(4h+3-\frac{3(h+4)}{17-13\beta}\Bigr)+2(1-\beta)\Bigr)^2.
--   $$
--   The printed rows contradict the table's own other rows: $q_2=s_2-I$ forces the $+$ sign (at $\beta=0$, $h=1/10$ the printed $q_2=5/34$, while $s_2-I=7/34$); the copycat demand at the table's own $p_2,p_C$ is $p_2/(2(1-\beta))$; and $\pi_C=p_Cs_C$.
--
--   **Formalization Note** Table 1 lists no orders or inventory, so `MatchesTable1` asserts none. The copycat rows are asserted only for $\beta>0$: at $\beta=0$ every copycat price earns $0$ and these rows are not determined by the model.
-- source:
--   Jin–Wu–Chen, Managing Competition from Within and Outside: Using Strategic Inventory and Network Externality to Combat Copycats, SSRN 3826955 (version of 2023-05-17), Table 1, p.8; Proposition 2 and Table 2 (Condition I, h₁, β*), p.9

import Mathlib
import Definitions.Def_CopycatSI_Model

namespace CopycatSI

/-- The copycat-quality threshold `β* = (√73 − 5)/6 ≈ 0.5907` of Proposition 2(ii) and Table 2,
Jin–Wu–Chen, SSRN 3826955 (version of 2023-05-17), p.9. It is the root in `[0, 1)` of
`3β² + 5β − 4 = 0`. -/
noncomputable def betaStar : ℝ := (Real.sqrt 73 - 5) / 6

/-- The holding-cost cutoff of Table 2, Condition I, p.9:
`h₁(β) = (1 − β)/((2 − β)(4 − 3β)) · (2 − β − (β/2)·√((17 − 13β)/(1 − β)))`.

**Formalization Note** Transcribed literally. It is used for `0 ≤ β < 1`, where `1 − β`,
`2 − β`, `4 − 3β` and `17 − 13β` are positive. -/
noncomputable def h1 (β : ℝ) : ℝ :=
  (1 - β) / ((2 - β) * (4 - 3 * β)) *
    (2 - β - β / 2 * Real.sqrt ((17 - 13 * β) / (1 - β)))

/-- An outcome record has the entries of **Table 1** ("Optimal Decisions without Strategic
Inventory or Network Externality", p.8), with copycat quality `β`:
`(w₁, w₂) = (1/2, (1−β)/(2−β))`, `(s₁, s₂) = (1/4, 1/4)`, `(p₁, p₂) = (3/4, 3(1−β)/(2(2−β)))`,
`(π_S, π_R) = ((4−3β)/(8(2−β)), (4−3β)/(16(2−β)))`, and, when `β > 0`, the copycat rows
`s_C = 3/(4(2−β))`, `p_C = 3β(1−β)/(4(2−β))`, `π_C = 9β(1−β)/(16(2−β)²)`.

**Formalization Note** Table 1 lists no orders or inventory, so none are asserted here. The copycat
rows are asserted only for `β > 0`: at `β = 0` the copycats' valuation is `0`, every price earns
them `0`, and `p_C`, `s_C`, `π_C` are not determined by the model (the printed `s_C = 3/8` at
`β = 0` is the limit `β → 0`). -/
def MatchesTable1 (β : ℝ) (o : Outcome) : Prop :=
  o.w1 = 1 / 2 ∧ o.w2 = (1 - β) / (2 - β) ∧
  o.s1 = 1 / 4 ∧ o.s2 = 1 / 4 ∧
  o.p1 = 3 / 4 ∧ o.p2 = 3 * (1 - β) / (2 * (2 - β)) ∧
  o.piS = (4 - 3 * β) / (8 * (2 - β)) ∧ o.piR = (4 - 3 * β) / (16 * (2 - β)) ∧
  (0 < β →
    o.sC = 3 / (4 * (2 - β)) ∧ o.pC = 3 * β * (1 - β) / (4 * (2 - β)) ∧
    o.piC = 9 * β * (1 - β) / (16 * (2 - β) ^ 2))

/-- An outcome record has the entries of **Table 2**, Condition I ("Dynamic Contract without
Network Externality", p.9), with copycat quality `β` and holding cost `h`, **with the rows `q₂`,
`s_C` and `π_C` corrected**:

* `w₁ = (9(1−β) − h(2−β))/(17−13β)`, `w₂ = (2/13)(4h + 3 − 3(h+4)/(17−13β))`;
* `q₁ = (13−11β)/(2(17−13β)) − h(7β²−23β+18)/(2(1−β)(17−13β))`,
  `q₂ = 3(2−β)/(2(17−13β)) + h(2−β)(5−4β)/(2(1−β)(17−13β))` (printed with `−` before the
  `h`-term; corrected, `q₂ = s₂ − I`);
* `I = (1/(17−13β))((5−7β)/2 − h(4β²−13β+10)/(1−β))`;
* `s₁ = (2−β)(h+4)/(2(17−13β))`, `s₂ = (11−10β)/(2(17−13β)) − h(4β²−13β+10)/(2(1−β)(17−13β))`;
* `p₁ = (1/2)(1 + (9(1−β) − h(2−β))/(17−13β))`, `p₂ = (1/13)(4h + 16 − 3(h+4)/(17−13β)) − 1/(2−β)`;
* `π_S = (1/(2(17−13β)))(9(1−β) − 2h(2−β) + h²(3β²−10β+8)/(1−β))`;
* `π_R = (118h−155+β(350−357h)+β²(309h−290)+β³(87−80h))/(2(13β−17)²(β−2))
  + h²(97β³−437β²+638β−304)/(4(13β−17)²(β−1))`;
* when `β > 0`, the copycat rows
  `s_C = (1/(2(17−13β)))((23−16β)/(2−β) + h(5−4β)/(1−β))` (corrected, `= p₂/(2(1−β))`),
  `p_C = (β/26)(4h + 16 − 3(h+4)/(17−13β)) − β/(2(2−β))`,
  `π_C = (β/(16(1−β)(2−β)²))((2(2−β)/13)(4h + 3 − 3(h+4)/(17−13β)) + 2(1−β))²`
  (corrected, `= p_C · s_C`).

**Formalization Note** The printed `q₂`, `s_C` and `π_C` contradict the table's own other rows:
at `β = 0`, `h = 1/10` the printed `q₂ = 5/34` while `s₂ − I = 7/34`; at `β = 3/10`, `h = 1/20`
the printed `s_C ≈ 0.38893` while the copycat demand at the table's own `p₂, p_C` is
`13063/31178 ≈ 0.41898`, and the printed `π_C ≈ 0.031056` while `p_C · s_C ≈ 0.036865`. The copycat
rows are asserted only for `β > 0`, as in `MatchesTable1`. -/
def MatchesTable2 (β h : ℝ) (o : Outcome) : Prop :=
  o.w1 = (9 * (1 - β) - h * (2 - β)) / (17 - 13 * β) ∧
  o.w2 = 2 / 13 * (4 * h + 3 - 3 * (h + 4) / (17 - 13 * β)) ∧
  o.q1 = (13 - 11 * β) / (2 * (17 - 13 * β)) -
    h * (7 * β ^ 2 - 23 * β + 18) / (2 * (1 - β) * (17 - 13 * β)) ∧
  o.q2 = 3 * (2 - β) / (2 * (17 - 13 * β)) +
    h * (2 - β) * (5 - 4 * β) / (2 * (1 - β) * (17 - 13 * β)) ∧
  o.inv = 1 / (17 - 13 * β) * ((5 - 7 * β) / 2 - h * (4 * β ^ 2 - 13 * β + 10) / (1 - β)) ∧
  o.s1 = (2 - β) * (h + 4) / (2 * (17 - 13 * β)) ∧
  o.s2 = (11 - 10 * β) / (2 * (17 - 13 * β)) -
    h * (4 * β ^ 2 - 13 * β + 10) / (2 * (1 - β) * (17 - 13 * β)) ∧
  o.p1 = 1 / 2 * (1 + (9 * (1 - β) - h * (2 - β)) / (17 - 13 * β)) ∧
  o.p2 = 1 / 13 * (4 * h + 16 - 3 * (h + 4) / (17 - 13 * β)) - 1 / (2 - β) ∧
  o.piS = 1 / (2 * (17 - 13 * β)) *
    (9 * (1 - β) - 2 * h * (2 - β) + h ^ 2 * (3 * β ^ 2 - 10 * β + 8) / (1 - β)) ∧
  o.piR = (118 * h - 155 + β * (350 - 357 * h) + β ^ 2 * (309 * h - 290) +
      β ^ 3 * (87 - 80 * h)) / (2 * (13 * β - 17) ^ 2 * (β - 2)) +
    h ^ 2 * (97 * β ^ 3 - 437 * β ^ 2 + 638 * β - 304) / (4 * (13 * β - 17) ^ 2 * (β - 1)) ∧
  (0 < β →
    o.sC = 1 / (2 * (17 - 13 * β)) * ((23 - 16 * β) / (2 - β) + h * (5 - 4 * β) / (1 - β)) ∧
    o.pC = β / 26 * (4 * h + 16 - 3 * (h + 4) / (17 - 13 * β)) - β / (2 * (2 - β)) ∧
    o.piC = β / (16 * (1 - β) * (2 - β) ^ 2) *
      (2 * (2 - β) / 13 * (4 * h + 3 - 3 * (h + 4) / (17 - 13 * β)) + 2 * (1 - β)) ^ 2)

end CopycatSI


