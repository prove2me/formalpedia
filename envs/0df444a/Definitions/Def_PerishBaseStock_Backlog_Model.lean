-- Prove2me | Definitions.Def_PerishBaseStock_Backlog_Model
-- name    : PerishBaseStock_Backlog_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T02:42:45.331121+00:00
-- url     : https://prove2.me/theorems/4b5f5a7e-cabb-4fce-8cc0-6615acd43308
-- title:
--   Perishable backlogging inventory system with lead times, base-stock policies and the heuristic cost $\widetilde C^L$
-- statement:
--   A perishable product has a fixed lifetime of $m\ge1$ periods and replenishment orders arrive after a lead time of $L\ge0$ periods. Demands $D_1,D_2,\dots$ are i.i.d. copies of a nonnegative random variable $D$ with $0<\mathbb E[D]<\infty$. Unit costs are $h>0$ for holding leftover inventory, $b>0$ per backlogged unit per period, and $\theta$ for each outdated unit (in addition to its holding cost), with the standing assumption $\theta\ge hL$.
--
--   In period $t$ the order placed in period $t-L$ arrives, the firm observes the state $\mathbf x_t=(x_{t,1},\dots,x_{t,m+L-1})$, orders $q_t\ge0$ and raises the **inventory position** to $x_{t,m+L}=x_{t,m+L-1}+q_t$. For $i\le m$, $x_{t,i}$ is the on-hand inventory with remaining lifetime at most $i$ minus the backorders; for $m<i<m+L$, $x_{t,i}$ adds the pipeline orders arriving by period $t+i-m$. Demand is served first-in-first-out, the excess is backlogged, and
--
--   $$o_t=(x_{t,1}-D_t)^+,\qquad x_{t+1,i}=x_{t,i+1}-D_t-o_t\quad(i=1,\dots,m+L-1).$$
--
--   The system starts empty. The period cost is $C^\pi_t=h(x_{t,m}-D_t)^++b(D_t-x_{t,m})^++\theta o_t$, where $x_{t,m}$ is the net on-hand inventory. An **admissible policy** $\pi\in\Pi$ orders $\varphi^\pi_t(\mathbf x_t)\ge0$ with $\varphi^\pi_t$ measurable; its long-run average cost is $C^\pi=\limsup_{T\to\infty}\frac1T\sum_{t=1}^T\mathbb E[C^\pi_t]$ and $\mathrm{OPT}^L=\inf_{\pi\in\Pi}C^\pi$. The **base-stock policy** $\pi_S$ orders $(S-x_{t,m+L-1})^+$, and $C^L(S)=C^{\pi_S}$. Finally
--
--   $$\widetilde C^L(S)=h\mathbb E\Big[\Big(S-\sum_{i=1}^{L+1}D_i\Big)^+\Big]+b\mathbb E\Big[\Big(\sum_{i=1}^{L+1}D_i-S\Big)^+\Big]+\frac{\theta-hL}{m+L}\mathbb E\Big[\Big(S-\sum_{i=1}^{m+L}D_i\Big)^+\Big],$$
--
--   and $\widetilde S^L$ denotes any minimizer of $\widetilde C^L$ over $[0,\infty)$.
--
--   These objects are the model of every statement of the mission.
--
--   **Formalization Note** Time is zero-based: Lean period $t$ is the paper's period $t+1$ and `d t` is $D_{t+1}$. The state is `Fin (m + L - 1) → ℝ` (signed), with $x_{t,0}:=0$ when $m+L=1$. Costs are in $[0,\infty]$ and expectations are lower Lebesgue integrals over the i.i.d. demand path law; `OPT` is the infimum over all measurable state-feedback policies. The standing assumptions are the predicate `Params.Standing`; the expectations in $\widetilde C^L$ use `expectedHolding`, `expectedShortfall` and `leadTimeLaw` of the referenced backorder definitions.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), pp. 8–9 (§2: demands, admissible policies, long-run average cost, OPT), p. 19 (§5: backlogging system with lead times, dynamics, base-stock policy, (14)), p. 20 (S̃^L), p. ec11 (period cost C^{π_S}_t)

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Backlog

/-! # The backlogging perishable inventory system with lead times (Bu, Gong & Chao, §5, p. 19)

Time is zero-based: Lean period `t` is the paper's period `t + 1`, and the demand `d t` of a
path `d : CappedBaseStock.DemandPath` is the paper's `D_{t+1}`. The system starts empty. -/

/-- The data of the backlogging system: lifetime `m`, lead time `L`, unit holding cost `h`,
unit backlogging cost `b` (per unit per period) and unit outdating cost `θ`. -/
structure Params where
  m : ℕ
  L : ℕ
  h : ℝ
  b : ℝ
  θ : ℝ

/-- The standing assumptions of §2 and §5 (pp. 8, 19): `m ≥ 1`, `h > 0`, `b > 0` and
`θ ≥ hL`. -/
def Params.Standing (c : Params) : Prop :=
  1 ≤ c.m ∧ 0 < c.h ∧ 0 < c.b ∧ c.h * (c.L : ℝ) ≤ c.θ

/-- The state `x_t = (x_{t,1}, …, x_{t,m+L-1})`, signed (backorders are negative);
Lean coordinate `j` is the paper's `x_{t,j+1}`. -/
abbrev State (c : Params) := Fin (c.m + c.L - 1) → ℝ

/-- The paper's `x_{t,i}` for `1 ≤ i ≤ m + L - 1`, read off the state, with `x_{t,0} := 0`
(only used when the state is empty). -/
def stateCoord (c : Params) (x : State c) (i : ℕ) : ℝ :=
  if hi : 1 ≤ i ∧ i ≤ c.m + c.L - 1 then x ⟨i - 1, by omega⟩ else 0

/-- The inventory position after ordering `q`: `x_{t,m+L} = x_{t,m+L-1} + q`. -/
def orderUpTo (c : Params) (x : State c) (q : ℝ) : ℝ :=
  stateCoord c x (c.m + c.L - 1) + q

/-- The paper's `x_{t,i}` for `1 ≤ i ≤ m + L` after the order `q` of the period. -/
def level (c : Params) (x : State c) (q : ℝ) (i : ℕ) : ℝ :=
  if i = c.m + c.L then orderUpTo c x q else stateCoord c x i

/-- Outdated quantity under FIFO: `o_t = (x_{t,1} - D_t)^+`. -/
def outdated (c : Params) (x : State c) (q d : ℝ) : ℝ :=
  max (level c x q 1 - d) 0

/-- The net on-hand inventory after the arrival of the period: `x_{t,m}`. -/
def netInventory (c : Params) (x : State c) (q : ℝ) : ℝ :=
  level c x q c.m

/-- The dynamics `x_{t+1,i} = x_{t,i+1} - D_t - o_t`, `i = 1, …, m + L - 1`. -/
def next (c : Params) (x : State c) (q d : ℝ) : State c :=
  fun j => level c x q (j.val + 2) - d - outdated c x q d

/-- The period cost `h(x_{t,m} - D_t)^+ + b(D_t - x_{t,m})^+ + θ o_t`. -/
def periodCost (c : Params) (x : State c) (q d : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c.h * max (netInventory c x q - d) 0 +
    c.b * max (d - netInventory c x q) 0 + c.θ * outdated c x q d)

/-- Admissible policies `Π`: in each period the order is a non-negative measurable function
`φ_t(x_t)` of the current state. -/
structure Policy (c : Params) where
  φ : ℕ → State c → ℝ≥0
  measurable_φ : ∀ t, Measurable (φ t)

/-- The state trajectory of policy `π` along the demand path `d`, from the empty state. -/
def traj (c : Params) (π : Policy c) (d : CappedBaseStock.DemandPath) : ℕ → State c
  | 0 => 0
  | t + 1 => next c (traj c π d t) (π.φ t (traj c π d t)) (d t)

/-- The order `q^π_t`. -/
def orderAt (c : Params) (π : Policy c) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  π.φ t (traj c π d t)

/-- `x^π_{t,i}`, `1 ≤ i ≤ m + L`. -/
def levelAt (c : Params) (π : Policy c) (d : CappedBaseStock.DemandPath) (t i : ℕ) : ℝ :=
  level c (traj c π d t) (orderAt c π d t) i

/-- `o^π_t`. -/
def outdatedAt (c : Params) (π : Policy c) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  outdated c (traj c π d t) (orderAt c π d t) (d t)

/-- `C^π_t`. -/
def costAt (c : Params) (π : Policy c) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ≥0∞ :=
  periodCost c (traj c π d t) (orderAt c π d t) (d t)

/-- The long-run average cost `C^π = limsup_T (1/T) Σ_{t=1}^T E[C^π_t]`, in `ℝ≥0∞`. -/
def policyCost (P : CappedBaseStock.DemandLaw) (c : Params) (π : Policy c) : ℝ≥0∞ :=
  limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ *
    ∑ t ∈ Finset.range T, ∫⁻ d, costAt c π d t ∂CappedBaseStock.demandPathLaw P) atTop

/-- The optimal cost `OPT^L = inf_{π ∈ Π} C^π`. -/
def OPT (P : CappedBaseStock.DemandLaw) (c : Params) : ℝ≥0∞ :=
  ⨅ π : Policy c, policyCost P c π

lemma measurable_stateCoord (c : Params) (i : ℕ) : Measurable (fun x : State c => stateCoord c x i) := by
  unfold stateCoord
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

/-- The base-stock policy `π_S`: `q_t = (S - x_{t,m+L-1})^+`. -/
def baseStock (c : Params) (S : ℝ≥0) : Policy c where
  φ _ x := Real.toNNReal ((S : ℝ) - stateCoord c x (c.m + c.L - 1))
  measurable_φ _ := (measurable_const.sub (measurable_stateCoord c _)).real_toNNReal

/-- `C^L(S)`, the long-run average cost of the base-stock policy `π_S`. -/
def bsCost (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : ℝ≥0∞ :=
  policyCost P c (baseStock c S)

/-- The function `C̃^L(S)` of (14):
`hE[(S - Σ_{i=1}^{L+1} D_i)^+] + bE[(Σ_{i=1}^{L+1} D_i - S)^+]
  + ((θ - hL)/(m + L)) E[(S - Σ_{i=1}^{m+L} D_i)^+]`. -/
def heuristicCost (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : ℝ :=
  c.h * LostSalesOrderUpTo.Asymptotic.expectedHolding
      (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P c.L) S +
    c.b * LostSalesOrderUpTo.Asymptotic.expectedShortfall
      (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P c.L) S +
    (c.θ - c.h * c.L) / ((c.m : ℝ) + c.L) *
      LostSalesOrderUpTo.Asymptotic.expectedHolding
        (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m + c.L - 1)) S

/-- `S̃^L` is a minimizer of `C̃^L` over `[0, ∞)`. -/
def IsHeuristicLevel (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : Prop :=
  ∀ S' : ℝ≥0, heuristicCost P c S ≤ heuristicCost P c S'

end PerishBaseStock.Backlog


