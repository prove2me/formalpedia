-- Prove2me | Definitions.Def_WasteNotWant_Model
-- name    : WasteNotWant_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:43:00.294115+00:00
-- url     : https://prove2.me/theorems/b46f7baf-a55f-46b7-a422-7f85322b4ca7
-- title:
--   The benchmark and quick response models: profits, stage-2 rule, optimal decisions, threshold, deadstock
-- statement:
--   A fashion firm sells one product at a fixed price $p_f$. Fabric costs $c_m$ per unit and regular production costs $c$ per unit, with $c+c_m<p_f<1$, $c_m>0$ and $c\ge0$. Each unit of product uses one unit of fabric. When the market size is $y$, demand is
--   $$D_f(y)=(1-p_f)\,y.$$
--   A **stage-1 decision** is a pair $(x,q)$ of fabric $x$ and production $q$ with $0\le q\le x$.
--
--   **Benchmark model.** Everything is decided before $Y$ is known, and the expected profit is
--   $$\mathbb E\Pi^B(x,q)=p_f\,\mathbb E\min\{D_f(Y),q\}-c_mx-cq.$$
--
--   **Quick response model.** After $y$ is known the firm may produce more, from leftover fabric, at unit cost $c+\delta$ with $\delta>0$. The stage-2 rule is
--   $$q^Q_\delta(x,q,y)=\begin{cases}\min\{(D_f(y)-q)^+,\,x-q\}&\text{if }p_f-(c+\delta)>0,\\0&\text{otherwise,}\end{cases}$$
--   and the expected profit, equation (1) of the paper, is
--   $$\mathbb E\Pi^Q(x,q)=p_f\,\mathbb E\min\{D_f(Y),\,q+q^Q_\delta(x,q,Y)\}-c_mx-cq-(c+\delta)\,\mathbb E\,q^Q_\delta(x,q,Y).$$
--
--   **Optimal decisions.** A pair is optimal in a model when it is feasible and maximizes that model's expected profit over all feasible pairs.
--
--   **Threshold.** $\bar\delta^Q=\bigl(\tfrac{p_f}{c_m+c}-1\bigr)\cdot c$.
--
--   **Deadstock.** At a decision $(x,q)$, the expected deadstock finished goods are $\Theta_l=\mathbb E[(q-D_f(Y))^+]$ in both models. The expected deadstock fabric is $\Theta^Q_m=\mathbb E[(x-q-q^Q_\delta(x,q,Y))^+]$ in the quick response model and $\Theta^B_m=(x-q)^+$ in the benchmark model.
--
--   These objects are shared by every statement of the mission. They reduce the paper's comparisons to statements about maximizers of two explicit functions.
--
--   **Formalization Note** Optimal decisions are maximizers and are never defined by the critical-fractile formulas, which are the content of the theorems. The paper writes $\Theta^B_m=0$ because $x^B=q^B$; defining the quantity as the unused fabric makes this a consequence. The stage-2 rule is transcribed, and its optimality is a separate theorem. The conditions $p_f<1$, $c_m>0$, $c\ge0$ are readings of the model on p.8.
-- source:
--   Long–Gui, Waste Not Want Not?, SSRN 4013877 (2023-08-10 copy), §3, pp.8–10, eq. (1), p.10; Lemma 1, p.10; §3.2.1, p.12

import Mathlib
import Definitions.Def_WasteNotWant_IsMarketLaw

open MeasureTheory

namespace WasteNotWant

/-- **The price and the unit costs.**
Long–Gui, *Waste Not Want Not?*, SSRN 4013877 (2023-08-10 copy), §3, p.8: the product price `pf`,
the unit fabric cost `cm`, the unit production cost `c`, with "we let `pf > c + cm`".

**Formalization Note.** `pf < 1`, `0 < cm` and `0 ≤ c` are readings of p.8: consumer valuations are
uniform on `[0, 1]`, so a price `pf ≥ 1` leaves no demand (and the paper divides by `1 - pf`), and
`c`, `cm` are unit costs. At `cm = 0` the fabric fractile of Lemma 1(i) is `1` and the optimal
fabric level is not unique. The quick-response premium `δ` is not a field, because Lemma 1 and
Propositions 1 and 2 vary it. -/
structure Params where
  /-- The product price `p_f`. -/
  pf : ℝ
  /-- The unit production cost `c`. -/
  c : ℝ
  /-- The unit fabric cost `c_m`. -/
  cm : ℝ
  c_nonneg : 0 ≤ c
  cm_pos : 0 < cm
  c_add_cm_lt_pf : c + cm < pf
  pf_lt_one : pf < 1

/-- **Demand.** `D_f(y) = (1 - p_f) y`, Long–Gui, SSRN 4013877 (2023-08-10 copy), §3, p.8. -/
def demand (P : Params) (y : ℝ) : ℝ := (1 - P.pf) * y

/-- **The set of stage-1 decisions** `(x, q)`: fabric `x` and production `q` with `0 ≤ q ≤ x`.
Long–Gui, SSRN 4013877 (2023-08-10 copy), p.10 ("subject to `q ≤ x`") and p.44 (the constraints
`q ≤ x`, `q ≥ 0`, `x ≥ 0`). The pair is `(x, q)`, so the first coordinate is the fabric. -/
def feasibleDecisions : Set (ℝ × ℝ) := {d | 0 ≤ d.2 ∧ d.2 ≤ d.1}

/-- **Expected profit of the benchmark model.**
`EΠ^B(x, q) = p_f E min{D_f(Y), q} - c_m x - c q`, Long–Gui, SSRN 4013877 (2023-08-10 copy), §3.1,
p.10. -/
noncomputable def benchmarkProfit (P : Params) (μ : Measure ℝ) (x q : ℝ) : ℝ :=
  P.pf * ∫ y, min (demand P y) q ∂μ - P.cm * x - P.c * q

/-- **The stage-2 production rule of the quick response model.**
`q^Q_δ(x, q, y) = min{(D_f(y) - q)^+, x - q}` if `p_f - (c + δ) > 0`, and `0` otherwise.
Long–Gui, SSRN 4013877 (2023-08-10 copy), §3.1, p.10.

**Formalization Note.** The paper derives this rule by backward induction and substitutes it into
(1). Here it is transcribed, and its optimality is the theorem `stage2_rule_optimal`. -/
noncomputable def stage2Rule (P : Params) (δ x q y : ℝ) : ℝ :=
  if 0 < P.pf - (P.c + δ) then min (max (demand P y - q) 0) (x - q) else 0

/-- **Expected profit of the quick response model**, eq. (1).
`EΠ^Q(x, q) = p_f E min{D_f(Y), q + q^Q_δ(x, q, Y)} - c_m x - c q - (c + δ) E q^Q_δ(x, q, Y)`,
Long–Gui, SSRN 4013877 (2023-08-10 copy), eq. (1), p.10. -/
noncomputable def qrProfit (P : Params) (μ : Measure ℝ) (δ x q : ℝ) : ℝ :=
  P.pf * ∫ y, min (demand P y) (q + stage2Rule P δ x q y) ∂μ - P.cm * x - P.c * q
    - (P.c + δ) * ∫ y, stage2Rule P δ x q y ∂μ

/-- **Optimal decisions of the benchmark model**: `(x, q)` maximizes `EΠ^B` over the feasible
decisions. Long–Gui, SSRN 4013877 (2023-08-10 copy), §3.1, p.10.

**Formalization Note.** Optimality is the maximizer property and never the critical-fractile
formula, which is the content of `benchmark_optimal`. -/
def IsBenchmarkOptimal (P : Params) (μ : Measure ℝ) (x q : ℝ) : Prop :=
  (x, q) ∈ feasibleDecisions ∧
    IsMaxOn (fun d : ℝ × ℝ => benchmarkProfit P μ d.1 d.2) feasibleDecisions (x, q)

/-- **Optimal stage-1 decisions of the quick response model at cost premium `δ`**: "The optimal
stage 1 decisions `(x^Q, q^Q)` maximize `EΠ^Q(x, q)` subject to `q ≤ x`." Long–Gui, SSRN 4013877
(2023-08-10 copy), §3.1, p.10.

**Formalization Note.** Optimality is the maximizer property and never the critical-fractile
formulas, which are the content of `lemma_1`. The constraints `q ≥ 0`, `x ≥ 0` are those of the
proof, p.44. -/
def IsQROptimal (P : Params) (μ : Measure ℝ) (δ x q : ℝ) : Prop :=
  (x, q) ∈ feasibleDecisions ∧
    IsMaxOn (fun d : ℝ × ℝ => qrProfit P μ δ d.1 d.2) feasibleDecisions (x, q)

/-- **The threshold of Lemma 1.** `δ̄^Q = (p_f / (c_m + c) - 1) · c`, Long–Gui, SSRN 4013877
(2023-08-10 copy), Lemma 1, p.10. -/
noncomputable def threshold (P : Params) : ℝ := (P.pf / (P.cm + P.c) - 1) * P.c

/-- **Expected deadstock finished goods** at production level `q`:
`Θ_l = E[(q - D_f(Y))^+]`. Long–Gui, SSRN 4013877 (2023-08-10 copy), §3.2.1, p.12.

**Formalization Note.** The same formula serves both models, as on p.12, where
`Θ^j_l = E[(q^j - D_f(Y))^+]` for `j = B, Q`. -/
noncomputable def deadstockGoods (P : Params) (μ : Measure ℝ) (q : ℝ) : ℝ :=
  ∫ y, max (q - demand P y) 0 ∂μ

/-- **Expected deadstock fabric of the quick response model** at decisions `(x, q)`:
`Θ^Q_m = E[(x - q - q^Q_δ(x, q, Y))^+]`. Long–Gui, SSRN 4013877 (2023-08-10 copy), §3.2.1, p.12. -/
noncomputable def deadstockFabricQR (P : Params) (μ : Measure ℝ) (δ x q : ℝ) : ℝ :=
  ∫ y, max (x - q - stage2Rule P δ x q y) 0 ∂μ

/-- **Deadstock fabric of the benchmark model** at decisions `(x, q)`: the unused fabric
`(x - q)^+`. Long–Gui, SSRN 4013877 (2023-08-10 copy), §3.2.1, p.12: "in the benchmark case, all
fabric is used in production so there is no deadstock fabric, which we denote by `Θ^B_m = 0`".

**Formalization Note.** The paper's `Θ^B_m = 0` holds because `x^B = q^B`. Defining the quantity as
the unused fabric makes that a consequence of `benchmark_optimal` instead of a convention. -/
noncomputable def deadstockFabricBenchmark (x q : ℝ) : ℝ := max (x - q) 0

end WasteNotWant


