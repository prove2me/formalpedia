-- Prove2me | Definitions.Def_ClosedLoopBass_Immediate_Model
-- name    : ClosedLoopBass_Immediate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:32.470688+00:00
-- url     : https://prove2.me/theorems/6ff07290-5584-420c-ae77-fded7d02c4a1
-- title:
--   §3, (1)–(6), pp. 4–6; §4.1, p. 7 — sales-dependent Bass diffusion, backlogs, returns, feasible sales plans, profit, and the immediate-fulfillment plan
-- statement:
--   A producer sells a new durable good, and remanufactured copies of returned units, over a selling horizon of $T$ periods.
--
--   **Parameters.** The parameters are the following:
--
--   1. a market size $m>0$;
--   2. a coefficient of innovation $p>0$ and a coefficient of imitation $q>0$, with $p+q\le1$;
--   3. a backlogging fraction $\alpha\in[0,1]$;
--   4. segment fractions $\gamma_1=1-\gamma_2$ (newness-conscious) and $\gamma_2\in[0,1]$ (functionality-oriented);
--   5. return fractions $\beta_i\ge0$, $i\ge1$, with $\sum_i\beta_i\le1$;
--   6. unit prices and costs with $p_n>c_n$, $p_r>c_r$ and $p_r-c_r>p_n-c_n$.
--
--   These conditions are the **standing assumptions** of the model.
--
--   **Sales plans.** A sales plan consists of new-item sales $n_t$ and remanufactured-item sales $r_t$ in each period $t=1,\dots,T$. The total sales are $s_t=n_t+r_t$, and the cumulative sales are $S_1=0$ and $S_t=\sum_{i=1}^{t-1}s_i$.
--
--   **Diffusion (1).** Only satisfied customers spread word of mouth, so the diffusion demand in period $t$ is
--
--   $$
--   d_t=\Bigl(p+\frac{qS_t}{m}\Bigr)(m-D_t),\qquad D_1=0,\quad D_t=\sum_{i=1}^{t-1}d_i .
--   $$
--
--   **Backlogs (4).** Let $b_{1t}$ and $b_{2t}$ be the backorders of the two segments, with $(b_{11},b_{21})=(0,0)$. If $\gamma_1d_t+b_{1t}\ge n_t$ and $\gamma_2d_t+b_{2t}\ge r_t$, then
--
--   $$
--   (b_{1(t+1)},b_{2(t+1)})=\bigl(\alpha(\gamma_1d_t+b_{1t}-n_t),\ \alpha(\gamma_2d_t+b_{2t}-r_t)\bigr);
--   $$
--
--   otherwise $(b_{1(t+1)},b_{2(t+1)})=\bigl(0,\ \alpha(d_t+b_{1t}+b_{2t}-n_t-r_t)\bigr)$.
--
--   **Returns (6).** The end-of-use return volume available in period $t$ is $e_1=0$ and
--
--   $$
--   e_{t+1}=e_t-r_t+\sum_{i=1}^{t}\beta_i s_{t+1-i}.
--   $$
--
--   **Feasibility and profit.** A plan is **feasible** if, for every $t=1,\dots,T$, it satisfies
--
--   - (2) $0\le s_t\le d_t+b_{1t}+b_{2t}$;
--   - (3) $0\le r_t\le\gamma_2d_t+b_{2t}$;
--   - (5) $0\le r_t\le e_t$.
--
--   Its total profit is $\sum_{t=1}^{T}\bigl[(p_n-c_n)n_t+(p_r-c_r)r_t\bigr]$.
--
--   **The immediate-fulfillment plan** (§4.1, p. 7) meets all demand in every period, and meets remanufactured-item demand from the available returns to the fullest extent possible. Let $\widetilde D_t$ and $\widetilde d_t$ be the original Bass trajectory. Then $\widetilde e_1=0$ and
--
--   $$
--   \widetilde r_t=\min\{\widetilde e_t,\gamma_2\widetilde d_t\},\qquad \widetilde n_t=\widetilde d_t-\widetilde r_t,\qquad \widetilde e_{t+1}=\widetilde e_t-\widetilde r_t+\sum_{i=1}^{t}\beta_i\widetilde d_{t+1-i}.
--   $$
--
--   **Demand differences** (p. 7). For a plan with diffusion demand $d_t$, define
--
--   $$
--   D_T^-=\sum_{t\le T:\ \widetilde d_t>d_t}(\widetilde d_t-d_t),\qquad D_T^+=\sum_{t\le T:\ d_t>\widetilde d_t}(d_t-\widetilde d_t).
--   $$
--
--   This module is the producer's nonlinear sales-planning problem of §3, together with the benchmark plan of §4.1. Every theorem of the mission is stated about these objects.
--
--   **Formalization Note**
--
--   1. A plan is a pair of real sequences indexed by periods $t\ge1$, and only periods $1,\dots,T$ are constrained. Cumulative quantities and backlogs are computed by recursions on the offset $k=t-1$.
--   2. The page states the second case of (4) under "$\gamma_1d_t+b_{1t}<n_t$ and $\gamma_2d_t+b_{2t}>r_t$". Lean uses it as the "otherwise" branch. On plans satisfying (2)–(3) the two printed cases are exhaustive, so the readings agree.
--   3. The sign conditions $m>0$, $p>0$, $q>0$, $\alpha,\gamma_2\in[0,1]$ and $\beta_i\ge0$ are implicit in the page's description of these quantities as a population, coefficients and fractions. They are stated explicitly in `Standing`, and $\sum_i\beta_i\le1$ is stated for every partial sum.
--   4. $n_t\ge0$ is not a printed constraint and is not imposed.
-- source:
--   Nadar, Kaya and Güler, New-Product Diffusion in Closed-Loop Supply Chains, MSOM (Articles in Advance, 2020), doi:10.1287/msom.2019.0864, pp. 4–7, §3, (1)–(6), the profit maximization problem p. 6, standing assumptions pp. 4–6; §4.1, p. 7 (immediate-fulfillment plan, D−T and D+T)

import Mathlib
import Definitions.Def_ClosedLoopBass_Immediate_Bass

namespace ClosedLoopBass.Immediate

/-- Primitives of the closed-loop sales-planning model (§3, pp. 4–6): horizon `T`, market size `m`,
innovation and imitation coefficients `p`, `q`, backlogging fraction `alpha`, the
functionality-oriented fraction `gamma2` (`gamma1 = 1 - gamma2`), return fractions `beta i`
(`i ≥ 1`; `beta 0` is never read), and prices and costs `pn, cn, pr, cr`. -/
structure Params where
  T : ℕ
  m : ℝ
  p : ℝ
  q : ℝ
  alpha : ℝ
  gamma2 : ℝ
  beta : ℕ → ℝ
  pn : ℝ
  cn : ℝ
  pr : ℝ
  cr : ℝ

/-- `γ1 = 1 − γ2` (p. 5, "We assume γ1 + γ2 = 1"). -/
def Params.gamma1 (P : Params) : ℝ := 1 - P.gamma2

/-- Standing assumptions of §3. From the page: `p + q ≤ 1` (p. 4), `β = Σ βi ≤ 1` (p. 5),
`pn > cn`, `pr > cr` and `pr − cr > pn − cn` (p. 6). Implicit sign conditions of the model's
primitives: `m > 0`, `p > 0`, `q > 0`, `α, γ2 ∈ [0, 1]`, `βi ≥ 0`. -/
structure Standing (P : Params) : Prop where
  m_pos : 0 < P.m
  p_pos : 0 < P.p
  q_pos : 0 < P.q
  p_add_q_le_one : P.p + P.q ≤ 1
  alpha_nonneg : 0 ≤ P.alpha
  alpha_le_one : P.alpha ≤ 1
  gamma2_nonneg : 0 ≤ P.gamma2
  gamma2_le_one : P.gamma2 ≤ 1
  beta_nonneg : ∀ i, 1 ≤ i → 0 ≤ P.beta i
  beta_sum_le_one : ∀ N, ∑ i ∈ Finset.Icc 1 N, P.beta i ≤ 1
  cn_lt_pn : P.cn < P.pn
  cr_lt_pr : P.cr < P.pr
  margin_lt : P.pn - P.cn < P.pr - P.cr

/-! A sales plan is a pair `n r : ℕ → ℝ` of new-item and remanufactured-item sales volumes,
indexed by period `t ≥ 1`; only its values in periods `1, …, T` are constrained. -/

/-- `s_t = n_t + r_t`, the total sales volume in period `t`. -/
def sales (n r : ℕ → ℝ) (t : ℕ) : ℝ := n t + r t

/-- `S_t = ∑_{i=1}^{t-1} s_i`, the total sales volume up to period `t` (`S_1 = 0`). -/
def S (n r : ℕ → ℝ) (t : ℕ) : ℝ := ∑ i ∈ Finset.Ico 1 t, sales n r i

/-- Cumulative diffusion demand, indexed by the offset `k = t - 1`: `Dc P n r k = D_{k+1}`,
with `D_1 = 0` and `D_{t+1} = D_t + d_t`, where `d_t = (p + q S_t / m)(m − D_t)` is (1). -/
noncomputable def Dc (P : Params) (n r : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => Dc P n r k + (P.p + P.q * S n r (k + 1) / P.m) * (P.m - Dc P n r k)

/-- `D_t = ∑_{i=1}^{t-1} d_i`, the total diffusion demand observed up to period `t` (`D_1 = 0`). -/
noncomputable def D (P : Params) (n r : ℕ → ℝ) (t : ℕ) : ℝ := Dc P n r (t - 1)

/-- The diffusion demand (1): `d_t = (p + q S_t / m)(m − D_t)`. -/
noncomputable def d (P : Params) (n r : ℕ → ℝ) (t : ℕ) : ℝ :=
  (P.p + P.q * S n r t / P.m) * (P.m - D P n r t)

/-- Backlogs (4), indexed by the offset `k = t - 1`: `bc P n r k = (b_{1,k+1}, b_{2,k+1})`, with
`(b_{11}, b_{21}) = (0, 0)`. The first case of (4) applies when `γ1 d_t + b_{1t} ≥ n_t` and
`γ2 d_t + b_{2t} ≥ r_t`; otherwise the second case applies. -/
noncomputable def bc (P : Params) (n r : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | k + 1 =>
    if n (k + 1) ≤ P.gamma1 * d P n r (k + 1) + (bc P n r k).1 ∧
        r (k + 1) ≤ P.gamma2 * d P n r (k + 1) + (bc P n r k).2 then
      (P.alpha * (P.gamma1 * d P n r (k + 1) + (bc P n r k).1 - n (k + 1)),
        P.alpha * (P.gamma2 * d P n r (k + 1) + (bc P n r k).2 - r (k + 1)))
    else
      (0, P.alpha * (d P n r (k + 1) + (bc P n r k).1 + (bc P n r k).2 - n (k + 1) - r (k + 1)))

/-- `b_{1t}`, the accumulated backorders of newness-conscious customers in period `t`. -/
noncomputable def b1 (P : Params) (n r : ℕ → ℝ) (t : ℕ) : ℝ := (bc P n r (t - 1)).1

/-- `b_{2t}`, the accumulated backorders of functionality-oriented customers in period `t`. -/
noncomputable def b2 (P : Params) (n r : ℕ → ℝ) (t : ℕ) : ℝ := (bc P n r (t - 1)).2

/-- End-of-use return volume (6), indexed by the offset `k = t - 1`: `ec P n r k = e_{k+1}`, with
`e_1 = 0` and `e_{t+1} = e_t − r_t + ∑_{i=1}^{t} β_i s_{t+1−i}`. -/
noncomputable def ec (P : Params) (n r : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => ec P n r k - r (k + 1) +
      ∑ i ∈ Finset.Icc 1 (k + 1), P.beta i * sales n r (k + 2 - i)

/-- `e_t`, the end-of-use return volume available in period `t`. -/
noncomputable def e (P : Params) (n r : ℕ → ℝ) (t : ℕ) : ℝ := ec P n r (t - 1)

/-- A sales plan is feasible for the producer's problem (p. 6) if, in every period `t = 1, …, T`,
constraints (2) `0 ≤ s_t ≤ d_t + b_{1t} + b_{2t}`, (3) `0 ≤ r_t ≤ γ2 d_t + b_{2t}` and
(5) `0 ≤ r_t ≤ e_t` hold, where `d`, `b` and `e` are given by (1), (4) and (6). -/
noncomputable def Feasible (P : Params) (n r : ℕ → ℝ) : Prop :=
  ∀ t ∈ Finset.Icc 1 P.T,
    0 ≤ sales n r t ∧ sales n r t ≤ d P n r t + b1 P n r t + b2 P n r t ∧
    0 ≤ r t ∧ r t ≤ P.gamma2 * d P n r t + b2 P n r t ∧
    r t ≤ e P n r t

/-- Total profit `∑_{t=1}^{T} [(pn − cn) n_t + (pr − cr) r_t]` (p. 6). -/
noncomputable def profit (P : Params) (n r : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 P.T, ((P.pn - P.cn) * n t + (P.pr - P.cr) * r t)

/-- `D̃_t`, the cumulative demand of the original Bass process (p. 4). -/
noncomputable def DB (P : Params) (t : ℕ) : ℝ := bassCum P.p P.q P.m t

/-- `d̃_t = (p + q D̃_t / m)(m − D̃_t)`, the demand of the original Bass process (p. 4). -/
noncomputable def dB (P : Params) (t : ℕ) : ℝ := bassDemand P.p P.q P.m t

/-- Return volume of the immediate-fulfillment plan, indexed by the offset `k = t - 1`:
`ẽ_1 = 0` and `ẽ_{t+1} = ẽ_t − min{ẽ_t, γ2 d̃_t} + ∑_{i=1}^{t} β_i d̃_{t+1−i}` (§4.1, p. 7, with (6)). -/
noncomputable def eIFc (P : Params) : ℕ → ℝ
  | 0 => 0
  | k + 1 => eIFc P k - min (eIFc P k) (P.gamma2 * dB P (k + 1)) +
      ∑ i ∈ Finset.Icc 1 (k + 1), P.beta i * dB P (k + 2 - i)

/-- `ẽ_t`, the accumulated return volume under the immediate-fulfillment plan. -/
noncomputable def eIF (P : Params) (t : ℕ) : ℝ := eIFc P (t - 1)

/-- `r̃_t = min{ẽ_t, γ2 d̃_t}`, remanufactured sales of the immediate-fulfillment plan (p. 7). -/
noncomputable def rIF (P : Params) (t : ℕ) : ℝ := min (eIF P t) (P.gamma2 * dB P t)

/-- `ñ_t = d̃_t − r̃_t`, new-item sales of the immediate-fulfillment plan, so that `s̃_t = d̃_t`
(p. 7). -/
noncomputable def nIF (P : Params) (t : ℕ) : ℝ := dB P t - rIF P t

/-- `D⁻_T = ∑_{t ≤ T : d̃_t > d_t} (d̃_t − d_t)` for the plan `(n, r)` (§4.1, p. 7). -/
noncomputable def Dminus (P : Params) (n r : ℕ → ℝ) : ℝ :=
  ∑ t ∈ (Finset.Icc 1 P.T).filter (fun t => d P n r t < dB P t), (dB P t - d P n r t)

/-- `D⁺_T = ∑_{t ≤ T : d_t > d̃_t} (d_t − d̃_t)` for the plan `(n, r)` (§4.1, p. 7). -/
noncomputable def Dplus (P : Params) (n r : ℕ → ℝ) : ℝ :=
  ∑ t ∈ (Finset.Icc 1 P.T).filter (fun t => dB P t < d P n r t), (d P n r t - dB P t)

end ClosedLoopBass.Immediate


