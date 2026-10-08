-- Prove2me | Definitions.Def_StrategicQR_Game_Model
-- name    : StrategicQR_Game_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:17:38.711696+00:00
-- url     : https://prove2.me/theorems/5dc40c44-5f6f-46a9-a9ee-807972245938
-- title:
--   Sec. 3–4 and §7 — the two-period model: segments, $\bar G$, $\xi$, sale revenue $R(s,I)$, profit $\pi(q,\hat v)$ (1), and the quick-response profit $\pi_r(q,\hat v)$
-- statement:
--   A retailer sells one product over two periods: at the exogenous full price $p$ in period 1 and at a markdown price $s$ in period 2. Unsold units at the end are worth nothing. First-period demand is $D\ge 0$ with density $f$ (see the demand-density module). Three consumer segments:
--
--   1. **myopic consumers**, $(1-\alpha)D$ of them, with value $v_M$, who only buy in period 1;
--   2. **strategic consumers**, $\alpha D$ of them, with value $v_M$ in period 1 and second-period values uniform on $[\underline v,\bar v]$, who choose when to buy;
--   3. unlimited **bargain hunters** with value $v_B$, who only buy on sale.
--
--   The model data are $p, v_B, v_M, \underline v, \bar v$, the optimism parameter $\theta$ of the sale-period queue (§5), and $f$, with the standing assumptions $\bar v\le p$, $\underline v\ge v_M-p+v_B$, $\underline v<\bar v$, $0\le\theta\le1$, plus $p<v_M$ and $v_B>0$ (see the note). The strategic fraction $\alpha$, the costs and the order quantity are arguments of the functions below.
--
--   Let $\bar G(s)=\min\{1,\max\{0,(\bar v-s)/(\bar v-\underline v)\}\}$ be the complementary distribution function of the strategic values. If strategic consumers with second-period value below the threshold $\hat v$ buy in period 1, the fraction of first-period demand that buys in period 1 is $\xi=1-\bar G(\hat v)\alpha$. With inventory $I$ at the start of period 2, the **sale-period revenue** (p. 12) is
--   $$R(s,I)=\begin{cases} s\min(\bar G(s)\alpha D, I) & s\ge \hat v,\\ s\min(\bar G(\hat v)\alpha D,I) & \hat v>s>v_B,\\ sI & s\le v_B,\end{cases}$$
--   and its optimum is $\sup_{0\le s\le p} R(s,I)$. The retailer's **expected profit** (1) at unit cost $c$ and order $q$ is
--   $$\pi(q,\hat v)=\mathbb E\Big[p\min(q,\xi D)-cq+\sup_{0\le s\le p}R(s,I)\Big],\qquad I=(q-\xi D)^+ .$$
--
--   With **quick response** (§7), the retailer orders $q$ at $c_1$ before the season and buys more at $c_2$ after observing $D$, both for first-period demand and, as $q_2\ge0$, for the sale period. The sale-period revenue is $R(s,I,q_2)=s\min(\bar G(s)\alpha D,I+q_2)-c_2q_2$ for $s\ge\hat v$, $s\min(\bar G(\hat v)\alpha D,I+q_2)-c_2q_2$ for $\hat v>s>v_B$, and $s(I+q_2)-c_2q_2$ for $s\le v_B$. The profit is
--   $$\pi_r(q,\hat v)=\mathbb E\Big[p\xi D-c_2(\xi D-q)^+-c_1q+\sup_{0\le s\le p,\ q_2\ge0}R(s,I,q_2)\Big] .$$
--
--   These are the objects of every result in the mission. The benchmark with only myopic consumers is the same function at $\alpha=0$, where the belief $\hat v$ plays no role.
--
--   **Formalization Note**
--   - **Added hypotheses.** $v_B>0$ is added: $D_l$ divides by $s_l=v_B$. $p<v_M$ strengthens the page's $v_M\ge p$: the proof of Lemma 4 (ii) uses a strictly positive first-period surplus, and Theorem 2's last claim fails at $v_M=p$.
--   - **Optima.** Both optima are suprema over all admissible prices $s\in[0,p]$ (no markups, footnote 6), never Lemma 2's closed form.
--   - **Prices above $\bar v$.** The page states $R$ only for $s\le\bar v$. For $s>\bar v$ the formula gives $0$ because $\bar G(s)=0$.
--   - **Quick-response revenue.** Appendix p. 5 omits the middle case $\hat v>s>v_B$, and the main-text revenue is used there. For $s\le v_B$ the appendix writes $sI$; here the formula keeps $q_2$, and its supremum over $q_2$ is $sI$ because $s\le v_B<c_2$.
--   - **Printed slip.** The proof of Theorem 2 writes "$pD-c_2(D-q)^+$", dropping $\xi$. The appendix's $\xi D$ is used.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), pp. 6–9, Section 3; p. 11, eq. (1); p. 12, R(s, I); p. 18, Section 7; Technical Appendix p. 5 (PDF 37), proof of Lemma 5, π_r and R(s, I, q2)

import Mathlib
import Definitions.Def_StrategicQR_Game_DemandDensity

namespace StrategicQR.Game

open MeasureTheory

/-- The two-period model of Cachon–Swinney, §3, pp. 6–9: full price `p`, bargain hunters' value
`vB`, first-period value `vM` of myopic and strategic consumers, strategic consumers' second-period
values uniform on `[vlo, vhi]`, optimism parameter `θ` of the sale-period queue (p. 14), and the
density `f` of the first-period demand `D`. The fields after the data are the standing assumptions
of §3 (`vhi ≤ p`, `vlo ≥ vM - p + vB`, `0 ≤ θ ≤ 1`), with `p < vM` (the page has `vM ≥ p`) and
`0 < vB` added; see the natural-language statement. -/
structure Model where
  p : ℝ
  vB : ℝ
  vM : ℝ
  vlo : ℝ
  vhi : ℝ
  θ : ℝ
  f : ℝ → ℝ
  vB_pos : 0 < vB
  p_lt_vM : p < vM
  vhi_le_p : vhi ≤ p
  vlo_ge : vM - p + vB ≤ vlo
  vlo_lt_vhi : vlo < vhi
  θ_nonneg : 0 ≤ θ
  θ_le_one : θ ≤ 1
  density : IsDemandDensity f

/-- The complementary distribution function `Ḡ(s) = 1 - G(s)` of the uniform distribution of
strategic consumers' second-period values on `[vlo, vhi]`: `1` for `s ≤ vlo`, `0` for
`s ≥ vhi`, linear in between. -/
noncomputable def Gbar (M : Model) (s : ℝ) : ℝ :=
  min 1 (max 0 ((M.vhi - s) / (M.vhi - M.vlo)))

/-- `ξ = 1 - Ḡ(v̂) α` (p. 11): the fraction of first-period demand that buys in the first period
when strategic consumers with values below the belief threshold `v̂` buy early. -/
noncomputable def xi (M : Model) (α vhat : ℝ) : ℝ :=
  1 - α * Gbar M vhat

/-- The second-period revenue `R(s, I)` (p. 12) at sale price `s`, inventory `I`, demand
realization `D`, strategic fraction `α` and belief `v̂`:
`s min(Ḡ(s) α D, I)` if `s ≥ v̂`, `s min(Ḡ(v̂) α D, I)` if `v̂ > s > vB`, and `s I` if `s ≤ vB`. -/
noncomputable def saleRevenue (M : Model) (α D vhat s I : ℝ) : ℝ :=
  if vhat ≤ s then s * min (Gbar M s * α * D) I
  else if M.vB < s then s * min (Gbar M vhat * α * D) I
  else s * I

/-- The optimal second-period revenue `max_s R(s, I)`: the supremum of `R(s, I)` over all sale
prices `s ∈ [0, p]` (no markups, footnote 6, p. 8). Never Lemma 2's closed form. -/
noncomputable def optSaleRevenue (M : Model) (α D vhat I : ℝ) : ℝ :=
  sSup ((fun s => saleRevenue M α D vhat s I) '' Set.Icc 0 M.p)

/-- The retailer's expected profit (1), p. 11, at unit cost `c`, order quantity `q` and belief
`v̂`: `π(q, v̂) = E[p min(q, ξD) - c q + max_s R(s, I)]` with `I = (q - ξD)⁺`. -/
noncomputable def profit (M : Model) (α c q vhat : ℝ) : ℝ :=
  ∫ x, (M.p * min q (xi M α vhat * x) - c * q +
      optSaleRevenue M α x vhat (max (q - xi M α vhat * x) 0)) * M.f x

/-- The second-period revenue with quick response `R(s, I, q₂)` (Technical Appendix p. 5,
proof of Lemma 5), with `q₂ ≥ 0` units bought at `c₂` for the sale period:
`s min(Ḡ(s) α D, I + q₂) - c₂ q₂` if `s ≥ v̂`, `s min(Ḡ(v̂) α D, I + q₂) - c₂ q₂` if
`v̂ > s > vB` (the main-text middle case, omitted on the appendix page), and `s (I + q₂) - c₂ q₂`
if `s ≤ vB` (unlimited bargain hunters). -/
noncomputable def qrSaleRevenue (M : Model) (α c₂ D vhat s I q₂ : ℝ) : ℝ :=
  if vhat ≤ s then s * min (Gbar M s * α * D) (I + q₂) - c₂ * q₂
  else if M.vB < s then s * min (Gbar M vhat * α * D) (I + q₂) - c₂ * q₂
  else s * (I + q₂) - c₂ * q₂

/-- `max_{s ≤ p, q₂ ≥ 0} R(s, I, q₂)`: the supremum over `s ∈ [0, p]` and `q₂ ≥ 0`. -/
noncomputable def qrOptSaleRevenue (M : Model) (α c₂ D vhat I : ℝ) : ℝ :=
  sSup ((fun z : ℝ × ℝ => qrSaleRevenue M α c₂ D vhat z.1 I z.2) ''
    (Set.Icc 0 M.p ×ˢ Set.Ici 0))

/-- The retailer's expected profit with quick response (Technical Appendix p. 5):
`π_r(q, v̂) = E[p ξ D - c₂ (ξD - q)⁺ - c₁ q + max_{s ≤ p, q₂ ≥ 0} R(s, I, q₂)]`,
`I = (q - ξD)⁺`. -/
noncomputable def qrProfit (M : Model) (α c₁ c₂ q vhat : ℝ) : ℝ :=
  ∫ x, (M.p * (xi M α vhat * x) - c₂ * max (xi M α vhat * x - q) 0 - c₁ * q +
      qrOptSaleRevenue M α c₂ x vhat (max (q - xi M α vhat * x) 0)) * M.f x

end StrategicQR.Game


