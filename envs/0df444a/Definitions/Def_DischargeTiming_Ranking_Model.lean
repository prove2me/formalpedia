-- Prove2me | Definitions.Def_DischargeTiming_Ranking_Model
-- name    : DischargeTiming_Ranking_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:18.906824+00:00
-- url     : https://prove2.me/theorems/9ca6110d-57af-44e9-a780-e8d228344f18
-- title:
--   §3.1–3.2 and §4, pp. 10–15 — discharge model: class-by-LOS census, minimum-LOS discharges (3)–(4), dynamics (5)–(6), costs (7)–(8), strong dominance (15)
-- statement:
--   This file sets up the inpatient discharge model of Shi, Helm, Deglise-Hawkinson and Pan, in the pathwise, finite-horizon form used by the interchange argument of their Section 4.
--
--   **Parameters.** There are $M$ patient classes $m$ and a maximum length of stay (LOS) $J$. For each class $m$ a readmission-risk curve $r(m,\cdot):\mathbb R\to\mathbb R$ gives the readmission risk of a class-$m$ patient discharged at LOS $t$; $R$ is the readmission penalty ($R_t=R$ for all $t$), $C$ the unit holding cost, $N$ the number of beds, and $\underline L_m\in\{0,\dots,J\}$ the minimum LOS of class $m$. The **standing assumptions** are: each $r(m,\cdot)$ is continuously differentiable and nonincreasing on $[0,\infty)$, and $R\ge 0$.
--
--   **State and action.** A state $X=(X^{m,j})$ counts the class-$m$ patients who have spent $j$ days in the system, $j=0,\dots,J$; a discharge action $D=(D^{m,j})$ counts the class-$m$ patients with LOS $j$ that are discharged. The census is $S=\sum_{m}\sum_{j=0}^{J}X^{m,j}$.
--
--   **Costs.** The holding cost (7) and the discharge cost (8) with $R_t=R$ are
--   $$c_h(X)=C\,(S-N)^+,\qquad c_d(D)=\sum_{m=1}^{M}\sum_{j=0}^{J}D^{m,j}\,R\,r(m,j).$$
--
--   **Feasibility.** An action $D$ is feasible at $X$ if $0\le D^{m,j}\le X^{m,j}$ for all $m,j$ (3), $D^{m,j}=0$ for $j<\underline L_m$ (4), and every patient at the maximum LOS leaves: $D^{m,J}=X^{m,J}$.
--
--   **Dynamics.** Given the arrivals $a^m$ of class $m$ in a period (new arrivals plus readmissions), the next state is $X^{m,0}_{k+1}=a^m_k$ (5) and $X^{m,j}_{k+1}=X^{m,j-1}_k-D^{m,j-1}_k$ for $j=1,\dots,J$ (6). A schedule $(D_k)_{k\ge0}$, an initial state $X_0$ and an exogenous arrival path $(a_k)$ determine the trajectory $(X_k)$. The schedule is feasible on the horizon $H$ if $D_k$ is feasible at $X_k$ for every $k<H$, and its total cost is
--   $$V(D)=\sum_{k=0}^{H-1}\bigl[c_h(X_k)+c_d(D_k)\bigr]+c_h(X_H)+c_d(X_H),$$
--   where the last term charges every patient still present at the horizon as if discharged at their current LOS.
--
--   **Strong dominance** (Definition 1, (15)). Type $(m_1,t_1)$ strongly dominates type $(m_2,t_2)$, written $(m_1,t_1)\succ(m_2,t_2)$, iff
--   $$\Bigl|\frac{\partial r(m_1,t_1+t)}{\partial t}\Bigr|\le\Bigl|\frac{\partial r(m_2,t_2+t)}{\partial t}\Bigr|\qquad\forall t\ge 0.$$
--
--   Finally, $e_{(m,t)}$ is the unit action with a single discharge of type $(m,t)$, and the **interchange** of a schedule $D$ at epochs $k<k'$ (from the proof of Theorem 2) discharges one more $(m_1,t_1)$ and one fewer $(m_2,t_2)$ patient at $k$, and one fewer $(m_1,t_1+k'-k)$ and one more $(m_2,t_2+k'-k)$ patient at $k'$, leaving every other action unchanged.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Counts are natural numbers and costs real numbers; classes are indexed by `Fin M` and LOS by `Fin (J+1)`, so $\underline L_m\in[0,J]$ as on p. 10. Following Remark 4 (p. 12), arrivals (including readmissions) are an exogenous deterministic path `arr`, and everything is pathwise. The forced exit at LOS $J$ and the terminal valuation are modelling conventions added here: without the first, patients at LOS $J$ would vanish at no cost; without the second, a patient kept to the horizon would never be charged. The derivative in (15) is Mathlib's `deriv`, which is the true derivative because each $r(m,\cdot)$ is $C^1$ under the standing assumptions. `losShift t Δ h` is the LOS index $t+\Delta$ (valid when $t+\Delta\le J$). In `interchange`, natural-number subtraction is truncated; the theorems that use it assume the counts it decreases are at least one.
-- source:
--   Shi, Helm, Deglise-Hawkinson, Pan, Timing it right: balancing inpatient congestion versus readmission risk at discharge, SSRN working paper 3202975 (version of 2019-08-26), pp. 10–15, §3.1 (state, action, (3)–(6), p. 10), §3.2 (costs (7)–(8), p. 11; Remark 4, p. 12), §4 (Definition 1, (15), p. 14; monotonicity and e_(m,t), p. 15), interchange from the proof of Theorem 2, pp. 15–16

import Mathlib

namespace DischargeTiming.Ranking

/-- Parameters of the discharge model (§3.1–3.2): `M` patient classes, maximum length of stay
(LOS) `J`, readmission-risk curves `r m : ℝ → ℝ` (risk of a class-`m` patient discharged at
LOS `t`), the readmission penalty `R` (`R_t = R` for all `t`), the unit holding cost `C`, the
number of beds `N`, and the minimum LOS `L m ∈ [0, J]` of class `m`. -/
structure Model (M J : ℕ) where
  r : Fin M → ℝ → ℝ
  R : ℝ
  C : ℝ
  N : ℕ
  L : Fin M → Fin (J + 1)

variable {M J : ℕ}

/-- Standing facts used by §4: every risk curve `r(m, ·)` is continuously differentiable and
nonincreasing in the LOS on `[0, ∞)` (p. 15), and the penalty `R` is nonnegative. -/
def Model.Standing (P : Model M J) : Prop :=
  (∀ m, ContDiff ℝ 1 (P.r m)) ∧ (∀ m, AntitoneOn (P.r m) (Set.Ici 0)) ∧ 0 ≤ P.R

/-- System state `X^{m,j}`: the number of class-`m` patients with LOS `j`, `j = 0, …, J`. -/
abbrev State (M J : ℕ) := Fin M → Fin (J + 1) → ℕ

/-- Discharge action `D^{m,j}`: the number of class-`m` patients with LOS `j` discharged. -/
abbrev Action (M J : ℕ) := Fin M → Fin (J + 1) → ℕ

/-- Total census `S = ∑_m ∑_j X^{m,j}`. -/
def census (x : State M J) : ℕ := ∑ m, ∑ j, x m j

/-- Holding (overage) cost (7): `c_h(X) = C · (S − N)^+`. -/
def holdingCost (P : Model M J) (x : State M J) : ℝ :=
  P.C * max ((census x : ℝ) - (P.N : ℝ)) 0

/-- Discharge cost (8) with `R_t = R`: `c_d(D) = ∑_m ∑_j D^{m,j} · R · r(m, j)`. -/
def dischargeCost (P : Model M J) (d : Action M J) : ℝ :=
  ∑ m, ∑ j, (d m j : ℝ) * (P.R * P.r m ((j : ℕ) : ℝ))

/-- Feasible action at state `x`: (3) `D^{m,j} ≤ X^{m,j}`; (4) `D^{m,j} = 0` for `j < L_m`;
and forced exit at the maximum LOS: `D^{m,J} = X^{m,J}` (dynamics (6) have no LOS `J + 1`). -/
def Feasible (P : Model M J) (x : State M J) (d : Action M J) : Prop :=
  (∀ m j, d m j ≤ x m j) ∧
  (∀ m j, j < P.L m → d m j = 0) ∧
  (∀ m, d m (Fin.last J) = x m (Fin.last J))

/-- One-day dynamics (5)–(6): the arrivals `a m` (new arrivals plus readmissions) form the
LOS-0 cohort, and every patient not discharged ages by one day. -/
def step (a : Fin M → ℕ) (x : State M J) (d : Action M J) : State M J :=
  fun m j =>
    if h : (j : ℕ) = 0 then a m
    else x m ⟨(j : ℕ) - 1, by omega⟩ - d m ⟨(j : ℕ) - 1, by omega⟩

/-- State trajectory `X_k` from the initial state `x0` under the exogenous arrival path `arr`
and the discharge schedule `D`. -/
def traj (x0 : State M J) (arr : ℕ → Fin M → ℕ) (D : ℕ → Action M J) : ℕ → State M J
  | 0 => x0
  | k + 1 => step (arr k) (traj x0 arr D k) (D k)

/-- `D` is feasible at every epoch `k < H` along its own trajectory. -/
def FeasibleSchedule (P : Model M J) (x0 : State M J) (arr : ℕ → Fin M → ℕ) (H : ℕ)
    (D : ℕ → Action M J) : Prop :=
  ∀ k < H, Feasible P (traj x0 arr D k) (D k)

/-- Total cost over the horizon `H`: holding plus discharge costs at epochs `k < H`, plus the
terminal valuation `c_h(X_H) + c_d(X_H)`, which charges every patient still present at `H` as
if discharged at their current LOS. -/
def totalCost (P : Model M J) (x0 : State M J) (arr : ℕ → Fin M → ℕ) (H : ℕ)
    (D : ℕ → Action M J) : ℝ :=
  (∑ k ∈ Finset.range H, (holdingCost P (traj x0 arr D k) + dischargeCost P (D k)))
    + holdingCost P (traj x0 arr D H) + dischargeCost P (traj x0 arr D H)

/-- Strong dominance (15), Definition 1: `(m1, t1) ≻ (m2, t2)` iff
`|∂r(m1, t1 + t)/∂t| ≤ |∂r(m2, t2 + t)/∂t|` for all `t ≥ 0`. -/
def StronglyDominates (P : Model M J) (m1 : Fin M) (t1 : ℝ) (m2 : Fin M) (t2 : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → |deriv (P.r m1) (t1 + t)| ≤ |deriv (P.r m2) (t2 + t)|

/-- The unit vector `e_(m,t)`: one discharge of type `(m, t)`. -/
def unitAction (m : Fin M) (j : Fin (J + 1)) : Action M J :=
  fun m' j' => if m' = m ∧ j' = j then 1 else 0

/-- The LOS index `t + Δ`, valid when `t + Δ ≤ J`. -/
def losShift (t : Fin (J + 1)) (Δ : ℕ) (h : (t : ℕ) + Δ ≤ J) : Fin (J + 1) :=
  ⟨(t : ℕ) + Δ, Nat.lt_succ_of_le h⟩

/-- The interchange of the proof of Theorem 2 (p. 15–16): starting from schedule `D`, discharge
one more `(m1, t1)` patient and one fewer `(m2, t2)` patient at epoch `k`, and at the later epoch
`k'` discharge one fewer `(m1, t1 + Δ)` and one more `(m2, t2 + Δ)` patient, `Δ = k' − k`, where
`p1 = t1 + Δ` and `p2 = t2 + Δ`. All other actions are unchanged. (When `k'` is the horizon, the
action at `k'` is never used, and the swapped patient is carried by the terminal valuation.) -/
def interchange (D : ℕ → Action M J) (k k' : ℕ) (m1 : Fin M) (t1 p1 : Fin (J + 1))
    (m2 : Fin M) (t2 p2 : Fin (J + 1)) : ℕ → Action M J :=
  fun i =>
    if i = k then D k + unitAction m1 t1 - unitAction m2 t2
    else if i = k' then D k' - unitAction m1 p1 + unitAction m2 p2
    else D i

end DischargeTiming.Ranking


