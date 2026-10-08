-- Prove2me | Definitions.Def_QFlexSC_ZeroInv_Model
-- name    : QFlexSC_ZeroInv_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:17.481369+00:00
-- url     : https://prove2.me/theorems/fe2c27fc-7277-47f8-b58d-37699bdc16bf
-- title:
--   §1 and §3, pp. 91–97 — QF parameters, cumulative flexibilities (9), (11), IR constraints (6)–(7), the MC policy (21)–(23) and its rolling run
-- statement:
--   This module fixes the model of a **flex node** in a rolling-horizon supply chain governed by quantity flexibility (QF) contracts (Tsay & Lovejoy 1999, §3).
--
--   **Schedules.** Time is discrete, $t = 0, 1, 2, \dots$. In period $t$ the node receives from its customer a *release schedule* $f(t) = [f_0(t), f_1(t), f_2(t), \dots]$, where $f_0(t)$ is the quantity sold in period $t$ and $f_j(t)$ is the period-$t$ estimate of the quantity to be sold in period $t + j$. The node passes upstream a *replenishment schedule* $r(t) = [r_0(t), r_1(t), \dots]$, where $r_0(t)$ is the purchase made in period $t$ and $r_j(t)$ the estimate of the purchase in period $t + j$. Both schedules are infinite sequences of reals.
--
--   **QF parameters.** The node has input parameters $(\alpha^{in}_q, \omega^{in}_q)$ and output parameters $(\alpha^{out}_q, \omega^{out}_q)$, $q \ge 1$. The **cumulative flexibilities** (9), (11) are
--   $$1 + A_j = \prod_{q=1}^{j} (1 + \alpha_q), \qquad 1 - \Omega_j = \prod_{q=1}^{j} (1 - \omega_q), \qquad j \ge 0,$$
--   for each of the input and output sides, so $A_0 = \Omega_0 = 0$.
--
--   **Incremental Revision (IR) constraints.** The output constraints (6) say that, for all $t$ and $j \ge 1$,
--   $$(1 - \omega^{out}_j) f_j(t) \le f_{j-1}(t+1) \le (1 + \alpha^{out}_j) f_j(t),$$
--   and the input constraints (7) are the same statement for $r$ with the input parameters.
--
--   **Minimum Commitment (MC) policy** (21)–(23). Given the previous ending stock $I(t-1)$, the previous replenishment schedule $r(t-1)$ and the current release schedule $f(t)$, the node computes, by one recursion on $j \ge 0$, the projected inventories $l_j(t)$ and the schedule $r_j(t)$:
--   $$l_0(t) = I(t-1), \qquad T_j(t) = \frac{(1 + A^{out}_j) f_j(t) - l_j(t)}{1 + A^{in}_j},$$
--   $$r_j(t) = \max\bigl[T_j(t),\ (1 - \omega^{in}_{j+1})\, r_{j+1}(t-1)\bigr],$$
--   $$l_{j+1}(t) = \bigl[l_j(t) + (1 - \Omega^{in}_j) r_j(t) - (1 + A^{out}_j) f_j(t)\bigr]^+ .$$
--
--   **The run.** Starting from an initial state $(I(0), r(0))$, in every period $t \ge 1$ the node applies the MC policy to $(I(t-1), r(t-1), f(t))$ to obtain $r(t)$, and its ending stock is $I(t) = I(t-1) + r_0(t) - f_0(t)$. The module provides $I(t)$, $r(t)$ and the projections $l_j(t)$ along this run.
--
--   These objects are shared by every statement of the mission: the zero-inventory result (Proposition 2) and the milestones on its proof are all statements about this run.
--
--   **Formalization Note.** The parameter sequences are functions $\mathbb N \to \mathbb R$ whose value at index $0$ is unused. Constraint (6) is stated with the paper's $j$ written $j + 1$ (so $j \ge 0$), which avoids natural-number subtraction; (7) is stated between periods $t$ and $t+1$. The MC policy is applied for every $j \in \mathbb N$ (the paper's range $j = 0, \dots, h$ belongs to Proposition 1's finite program). Period $0$ is the initial state; the policy acts from period $1$ on. The accessor for $l_j(t)$ is meaningful for $t \ge 1$ only. The module also records the two unfolding identities $r(t+1) = \mathrm{MC}(I(t), r(t), f(t+1))$ and $I(t+1) = I(t) + r_0(t+1) - f_0(t+1)$.
-- source:
--   Tsay & Lovejoy, Quantity flexibility contracts and supply chain performance, MSOM 1(2) (1999), pp. 91–97, (2)–(3), (6)–(11), (21)–(23)

import Mathlib

namespace QFlexSC.ZeroInv

/-- The quantity-flexibility (QF) parameters of a flex node: input parameters `(αin, ωin)`
(towards its supplier) and output parameters `(αout, ωout)` (towards its customer).
The paper's `α_q`, `ω_q` are the values at `q ≥ 1`; index `0` is unused. -/
structure QFParams where
  αin : ℕ → ℝ
  ωin : ℕ → ℝ
  αout : ℕ → ℝ
  ωout : ℕ → ℝ

/-- Cumulative upside flexibility `A_j`: `1 + A_j = ∏_{q=1}^{j} (1 + α_q)` ((9), (11)). `A_0 = 0`. -/
def Acum (α : ℕ → ℝ) (j : ℕ) : ℝ := (∏ q ∈ Finset.Icc 1 j, (1 + α q)) - 1

/-- Cumulative downside flexibility `Ω_j`: `1 - Ω_j = ∏_{q=1}^{j} (1 - ω_q)` ((9), (11)). `Ω_0 = 0`. -/
def Ωcum (ω : ℕ → ℝ) (j : ℕ) : ℝ := 1 - ∏ q ∈ Finset.Icc 1 j, (1 - ω q)

/-- The output Incremental Revision constraints (6) for all periods: for all `t` and `j ≥ 0`,
`(1 - ω^out_{j+1}) f_{j+1}(t) ≤ f_j(t+1) ≤ (1 + α^out_{j+1}) f_{j+1}(t)`.
Here `f t j` is `f_j(t)`, the period-`t` estimate of the quantity sold in period `t + j`. -/
def IROut (P : QFParams) (f : ℕ → ℕ → ℝ) : Prop :=
  ∀ t j : ℕ, (1 - P.ωout (j + 1)) * f t (j + 1) ≤ f (t + 1) j ∧
    f (t + 1) j ≤ (1 + P.αout (j + 1)) * f t (j + 1)

/-- The input Incremental Revision constraints (7) between periods `t` and `t + 1`:
for all `j ≥ 0`, `(1 - ω^in_{j+1}) r_{j+1}(t) ≤ r_j(t+1) ≤ (1 + α^in_{j+1}) r_{j+1}(t)`. -/
def IRIn (P : QFParams) (r : ℕ → ℕ → ℝ) (t : ℕ) : Prop :=
  ∀ j : ℕ, (1 - P.ωin (j + 1)) * r t (j + 1) ≤ r (t + 1) j ∧
    r (t + 1) j ≤ (1 + P.αin (j + 1)) * r t (j + 1)

/-- The target `T_j(t) = ((1 + A^out_j) f_j(t) - l_j(t)) / (1 + A^in_j)` of (22), as a function of
the current release schedule `f = f(t)` and the projected inventory `l = l_j(t)`. -/
noncomputable def target (P : QFParams) (f : ℕ → ℝ) (l : ℝ) (j : ℕ) : ℝ :=
  ((1 + Acum P.αout j) * f j - l) / (1 + Acum P.αin j)

/-- The MC entry (21): `r_j(t) = max[T_j(t), (1 - ω^in_{j+1}) r_{j+1}(t - 1)]`, with
`rprev = r(t - 1)` and `l = l_j(t)`. -/
noncomputable def entry (P : QFParams) (rprev f : ℕ → ℝ) (l : ℝ) (j : ℕ) : ℝ :=
  max (target P f l j) ((1 - P.ωin (j + 1)) * rprev (j + 1))

/-- The projected inventory `l_j(t)` of (23), computed jointly with `r_j(t)` by one recursion on `j`:
`l_0(t) = I(t - 1)` and
`l_{j+1}(t) = [l_j(t) + (1 - Ω^in_j) r_j(t) - (1 + A^out_j) f_j(t)]^+`,
where `r_j(t)` is the MC entry (21) at `l_j(t)`. Data: `Iprev = I(t - 1)`, `rprev = r(t - 1)`,
`f = f(t)`. -/
noncomputable def proj (P : QFParams) (Iprev : ℝ) (rprev f : ℕ → ℝ) : ℕ → ℝ
  | 0 => Iprev
  | j + 1 =>
      max 0 (proj P Iprev rprev f j
        + (1 - Ωcum P.ωin j) * entry P rprev f (proj P Iprev rprev f j) j
        - (1 + Acum P.αout j) * f j)

/-- The Minimum Commitment (MC) replenishment schedule `r(t)` of (21)–(23):
`r_j(t) = max[T_j(t), (1 - ω^in_{j+1}) r_{j+1}(t - 1)]` with `l_j(t)` from `proj`. -/
noncomputable def mcStep (P : QFParams) (Iprev : ℝ) (rprev f : ℕ → ℝ) (j : ℕ) : ℝ :=
  entry P rprev f (proj P Iprev rprev f j) j

/-- The rolling run of a flex node using the MC policy. Period `0` is the initial state
`(I(0), r(0)) = (I₀, r₀)`; in each period `t + 1` the node receives `f(t + 1)`, sets
`r(t + 1)` by the MC policy from `(I(t), r(t), f(t + 1))`, and its ending stock is
`I(t + 1) = I(t) + r_0(t + 1) - f_0(t + 1)`. -/
noncomputable def run (P : QFParams) (I₀ : ℝ) (r₀ : ℕ → ℝ) (f : ℕ → ℕ → ℝ) :
    ℕ → ℝ × (ℕ → ℝ)
  | 0 => (I₀, r₀)
  | t + 1 =>
      let s := run P I₀ r₀ f t
      let r' := mcStep P s.1 s.2 (f (t + 1))
      (s.1 + r' 0 - f (t + 1) 0, r')

/-- Ending stock `I(t)` of the MC run. -/
noncomputable def inv (P : QFParams) (I₀ : ℝ) (r₀ : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (t : ℕ) : ℝ :=
  (run P I₀ r₀ f t).1

/-- Replenishment schedule `r(t)` of the MC run (`sched … t j = r_j(t)`). -/
noncomputable def sched (P : QFParams) (I₀ : ℝ) (r₀ : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (t : ℕ) :
    ℕ → ℝ :=
  (run P I₀ r₀ f t).2

/-- Projected inventories `l_j(t)` of the MC run at period `t`; meaningful for `t ≥ 1`
(at `t = 0` the natural subtraction makes it the projection from period 0's own state). -/
noncomputable def projInvAt (P : QFParams) (I₀ : ℝ) (r₀ : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (t : ℕ) :
    ℕ → ℝ :=
  proj P (inv P I₀ r₀ f (t - 1)) (sched P I₀ r₀ f (t - 1)) (f t)

theorem sched_succ (P : QFParams) (I₀ : ℝ) (r₀ : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (t : ℕ) :
    sched P I₀ r₀ f (t + 1) = mcStep P (inv P I₀ r₀ f t) (sched P I₀ r₀ f t) (f (t + 1)) :=
  rfl

theorem inv_succ (P : QFParams) (I₀ : ℝ) (r₀ : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (t : ℕ) :
    inv P I₀ r₀ f (t + 1) = inv P I₀ r₀ f t + sched P I₀ r₀ f (t + 1) 0 - f (t + 1) 0 :=
  rfl

end QFlexSC.ZeroInv


