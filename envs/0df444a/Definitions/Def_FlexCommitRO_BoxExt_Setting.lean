-- Prove2me | Definitions.Def_FlexCommitRO_BoxExt_Setting
-- name    : FlexCommitRO_BoxExt_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:59:48.536262+00:00
-- url     : https://prove2.me/theorems/12aa7b01-f8f9-4155-87f0-150b6f70529e
-- title:
--   §2.2–§2.3, pp. 252–255 — RSFC data, nonanticipative policies, the min-max RSFC problem (5)–(6) over a product uncertainty set, its optimal value, the R-boxed variant
-- statement:
--   **The retailer–supplier flexible commitments (RSFC) model** of Ben-Tal, Golany, Nemirovski and Vial (§2.2). A retailer manages one product over $T$ periods. Before any demand is seen it fixes **commitments** $w = (w_1,\dots,w_T)$ with $w_t \ge 0$ and auxiliary amounts $z_1,\dots,z_T$. At the start of period $t$ it holds inventory $x_t$, orders $q_t$ at unit cost $c_t$, and then demand $d_t$ arrives.
--
--   **Data.** Unit costs $c_t$, holding costs $h_t$, shortage costs $p_t$, penalties $\alpha_t^{+}, \alpha_t^{-}$ for deviations of orders from commitments, penalties $\beta_t^{+}, \beta_t^{-}$ for changes between successive commitments, salvage value $s$, initial inventory $x_1$, nominal previous commitment $w_0$, and order bounds $L_t \le q_t \le U_t$ and cumulative bounds $\widehat L_t \le \sum_{\tau \le t} q_\tau \le \widehat U_t$ in $[-\infty, +\infty]$. Put $\bar h_t = h_t$ for $t < T$ and $\bar h_T = h_T - s$.
--
--   **Uncertainty and policies.** The demand trajectory $d = (d_1,\dots,d_T)$ ranges over a product set $\mathcal U^T = \mathcal U_1 \times \dots \times \mathcal U_T$. A policy consists of the numbers $w_t, z_t$ and decision rules $q_t(d), y_t(d), u_t(d), x_t(d)$ which are **nonanticipative** on $\mathcal U^T$: for trajectories in $\mathcal U^T$, $q_t, y_t, u_t$ depend only on $d^{t-1} = (d_1,\dots,d_{t-1})$, and $x_{t+1}$ only on $d^t$.
--
--   **Feasibility (6).** For every $d \in \mathcal U^T$ and every $t$:
--   $$
--   \begin{aligned}
--   &x_1 = x_1^{\text{data}},\quad x_{t+1}(d^t) = x_t(d^{t-1}) + q_t(d^{t-1}) - d_t,\quad L_t \le q_t \le U_t,\quad \widehat L_t \le \textstyle\sum_{\tau=1}^t q_\tau \le \widehat U_t,\\
--   &y_t \ge \bar h_t\, x_{t+1},\quad y_t \ge -p_t\, x_{t+1},\quad u_t \ge \alpha_t^{+}(q_t - w_t),\quad u_t \ge -\alpha_t^{-}(q_t - w_t),\\
--   &z_t \ge \beta_t^{+}(w_t - w_{t-1}),\quad z_t \ge -\beta_t^{-}(w_t - w_{t-1}),\quad w_t \ge 0 .
--   \end{aligned}
--   $$
--
--   **Value (5).** The cost on trajectory $d$ is $E(d) = \sum_{t=1}^T \big[c_t q_t(d^{t-1}) + y_t(d^{t-1}) + u_t(d^{t-1}) + z_t\big]$, and the optimal value of the min-max RSFC problem is
--   $$
--   \operatorname{value}(\mathcal U) = \inf_{\text{feasible policies}}\ \sup_{d \in \mathcal U^T} E(d) \in [-\infty, +\infty],
--   $$
--   equal to $+\infty$ when no policy is feasible. The **$R$-boxed** value $\operatorname{value}_R(\mathcal U)$ is the same with the additional constraints that every decision ($x_t$, $q_t$, the cumulative order $\sum_{\tau\le t} q_\tau$, $y_t$, $u_t$, $w_t$, $z_t$) has absolute value at most $R$ on every trajectory of $\mathcal U^T$ — the "additional box constraints" of the Appendix (p. 271).
--
--   These are the objects of Proposition 1: the box uncertainty (9)–(10) is the case $\mathcal U_t = [d_t^{\min}, d_t^{\max}]$.
--
--   **Formalization Note** Periods are `Fin T`, 0-based: Lean period $t$ is the paper's period $t+1$, and `x k` is the inventory at the start of Lean period $k$ (so `x 0` is $x_1$). Decision rules are functions of the whole trajectory, made nonanticipative by an explicit condition quantified over trajectories of the uncertainty set only. Optimal values are `EReal` infima of suprema. The bounds $L, U, \widehat L, \widehat U$ are `EReal` so that infinite bounds (p. 253) are allowed. The standing assumptions $s < c_T$ and (1) $h_T - s \ge -p_T$ of §2.2 are not imposed, and no sign is assumed on any cost or penalty.
-- source:
--   Ben-Tal, Golany, Nemirovski & Vial, Retailer-supplier flexible commitments contracts: a robust optimization approach, MSOM 7(3) (2005), pp. 252–255, §2.2 (1)–(6), §2.3 (9)–(10); Appendix p. 271 (additional box constraints)

import Mathlib

namespace FlexCommitRO.BoxExt

/-- Data of the RSFC model (§2.2, pp. 252–253). Periods are `Fin T`, 0-based: Lean period `t` is
the paper's period `t + 1`. Costs `c, h, p`, contract penalties `αp = α⁺, αm = α⁻, βp = β⁺,
βm = β⁻`, salvage value `s`, initial inventory `x₁`, nominal previous commitment `w₀`, and order
bounds `L ≤ q_t ≤ U`, cumulative bounds `Lhat ≤ Σ_{τ ≤ t} q_τ ≤ Uhat`, valued in `EReal` so that
infinite bounds (p. 253) are allowed. No sign assumption is imposed on any cost or penalty. -/
structure RSFCData (T : ℕ) where
  c : Fin T → ℝ
  h : Fin T → ℝ
  p : Fin T → ℝ
  αp : Fin T → ℝ
  αm : Fin T → ℝ
  βp : Fin T → ℝ
  βm : Fin T → ℝ
  s : ℝ
  x₁ : ℝ
  w₀ : ℝ
  L : Fin T → EReal
  U : Fin T → EReal
  Lhat : Fin T → EReal
  Uhat : Fin T → EReal

variable {T : ℕ}

/-- `h̄_t` (p. 253): `h̄_t = h_t` for `t < T` and `h̄_T = h_T − s` (last Lean period `T − 1`). -/
def hbar (D : RSFCData T) (t : Fin T) : ℝ :=
  if (t : ℕ) + 1 = T then D.h t - D.s else D.h t

/-- The previous commitment `w_{t−1}`, with `w_0` taken from the data for the first period. -/
def wPrev (D : RSFCData T) (w : Fin T → ℝ) (t : Fin T) : ℝ :=
  if h : (t : ℕ) = 0 then D.w₀ else w ⟨(t : ℕ) - 1, by omega⟩

/-- A policy of the min-max RSFC problem (5): here-and-now commitments `w` and commitment-change
penalties `z`, and decision rules `q, y, u` (period `t`) and `x` (inventory at the start of Lean
period `k`, so `x 0` is the paper's `x_1`) given as functions of the whole demand trajectory
`d : Fin T → ℝ`; nonanticipativity is imposed separately. -/
structure RSFCPolicy (T : ℕ) where
  w : Fin T → ℝ
  z : Fin T → ℝ
  q : Fin T → (Fin T → ℝ) → ℝ
  y : Fin T → (Fin T → ℝ) → ℝ
  u : Fin T → (Fin T → ℝ) → ℝ
  x : Fin (T + 1) → (Fin T → ℝ) → ℝ

/-- Nonanticipativity on the trajectories of the product uncertainty set `∏_t Ucal t`:
`q_t, y_t, u_t` depend only on the demands of earlier periods (`d^{t−1}`) and the inventory
`x k` at the start of Lean period `k` only on the demands of Lean periods `< k`. -/
def NonAnticipative (Ucal : Fin T → Set ℝ) (pol : RSFCPolicy T) : Prop :=
  ∀ d ∈ Set.univ.pi Ucal, ∀ d' ∈ Set.univ.pi Ucal,
    (∀ t : Fin T, (∀ τ : Fin T, τ < t → d τ = d' τ) →
        pol.q t d = pol.q t d' ∧ pol.y t d = pol.y t d' ∧ pol.u t d = pol.u t d') ∧
    (∀ k : Fin (T + 1), (∀ τ : Fin T, (τ : ℕ) < (k : ℕ) → d τ = d' τ) → pol.x k d = pol.x k d')

/-- Feasibility of a policy for the constraints (6) of the min-max RSFC problem over the product
uncertainty set `∏_t Ucal t`. -/
def Feasible (D : RSFCData T) (Ucal : Fin T → Set ℝ) (pol : RSFCPolicy T) : Prop :=
  NonAnticipative Ucal pol ∧
  (∀ t, 0 ≤ pol.w t) ∧
  (∀ t, pol.z t ≥ D.βp t * (pol.w t - wPrev D pol.w t)) ∧
  (∀ t, pol.z t ≥ -D.βm t * (pol.w t - wPrev D pol.w t)) ∧
  ∀ d ∈ Set.univ.pi Ucal,
    pol.x 0 d = D.x₁ ∧
    ∀ t : Fin T,
      pol.x t.succ d = pol.x t.castSucc d + pol.q t d - d t ∧
      D.L t ≤ ((pol.q t d : ℝ) : EReal) ∧ ((pol.q t d : ℝ) : EReal) ≤ D.U t ∧
      D.Lhat t ≤ ((∑ τ ∈ Finset.univ.filter (· ≤ t), pol.q τ d : ℝ) : EReal) ∧
      ((∑ τ ∈ Finset.univ.filter (· ≤ t), pol.q τ d : ℝ) : EReal) ≤ D.Uhat t ∧
      pol.y t d ≥ hbar D t * pol.x t.succ d ∧
      pol.y t d ≥ -D.p t * pol.x t.succ d ∧
      pol.u t d ≥ D.αp t * (pol.q t d - pol.w t) ∧
      pol.u t d ≥ -D.αm t * (pol.q t d - pol.w t)

/-- The objective `E` of (5) on the trajectory `d`. -/
def cost (D : RSFCData T) (pol : RSFCPolicy T) (d : Fin T → ℝ) : ℝ :=
  ∑ t, (D.c t * pol.q t d + pol.y t d + pol.u t d + pol.z t)

/-- The optimal value of the min-max RSFC problem (5)–(6) over `∏_t Ucal t`, in `EReal`
(`⊤` if infeasible, possibly `⊥`). -/
noncomputable def value (D : RSFCData T) (Ucal : Fin T → Set ℝ) : EReal :=
  ⨅ (pol : RSFCPolicy T) (_ : Feasible D Ucal pol),
    ⨆ d ∈ Set.univ.pi Ucal, ((cost D pol d : ℝ) : EReal)

/-- Feasibility with the additional box constraints of p. 271: every decision (inventories,
orders, cumulative orders, `y`, `u`, `w`, `z`) has absolute value at most `R` on every
trajectory of the uncertainty set. -/
def FeasibleR (D : RSFCData T) (Ucal : Fin T → Set ℝ) (R : ℝ) (pol : RSFCPolicy T) : Prop :=
  Feasible D Ucal pol ∧
  (∀ t, |pol.w t| ≤ R) ∧ (∀ t, |pol.z t| ≤ R) ∧
  ∀ d ∈ Set.univ.pi Ucal,
    (∀ k, |pol.x k d| ≤ R) ∧
    ∀ t : Fin T,
      |pol.q t d| ≤ R ∧ |∑ τ ∈ Finset.univ.filter (· ≤ t), pol.q τ d| ≤ R ∧
      |pol.y t d| ≤ R ∧ |pol.u t d| ≤ R

/-- The optimal value of the R-boxed min-max RSFC problem. -/
noncomputable def valueR (D : RSFCData T) (Ucal : Fin T → Set ℝ) (R : ℝ) : EReal :=
  ⨅ (pol : RSFCPolicy T) (_ : FeasibleR D Ucal R pol),
    ⨆ d ∈ Set.univ.pi Ucal, ((cost D pol d : ℝ) : EReal)

end FlexCommitRO.BoxExt


