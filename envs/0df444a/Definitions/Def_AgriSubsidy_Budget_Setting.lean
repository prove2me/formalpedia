-- Prove2me | Definitions.Def_AgriSubsidy_Budget_Setting
-- name    : AgriSubsidy_Budget_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:35.807103+00:00
-- url     : https://prove2.me/theorems/afd99c3b-9328-48f9-9ef5-90f5093d6c99
-- title:
--   Agricultural Cournot market and four subsidy budget programs
-- statement:
--   There are $N>0$ farmers. Farmer $j$ plants $z_jq_j$ units of input to obtain $q_j$ units of output. Planting costs $c_P$ per input unit and harvesting costs $c_H$ per output unit. A per-output payment vector $t$ changes farmer $j$'s unit cost to $z_jc_P+c_H-t_j$. A combined program pays $t_j=z_js_P+s_H$; a selective program pays $t_j=\max(z_js_P,s_H)$. Planting-only and harvesting-only programs set the other subsidy to zero.
--
--   The government accepts a profile when its Cournot equilibrium has every farmer active and total output at least $\bar Q$. Its feasible budget is the sum of payments $\sum_j t_jq_j$, and the optimum for each program is the infimum of those feasible budgets:
--
--   $$B_{\mathcal P}(\bar Q)=\inf\{\textstyle\sum_j t_jq_j:t\in\mathcal P,\ q\text{ is an all-active equilibrium},\ \sum_jq_j\ge\bar Q\}.$$
--
--   The setting also defines $\bar z$, $v_z$, $\bar a(s_P,s_H)$, the all-active expression $Q^C(s_P,s_H)$ from (5), and the three designs $s_P^P,s_H^H,(s_P^C,s_H^C)$ from Proposition 8. It provides one common meaning for every budget comparison in this mission.
--
--   **Formalization Note** Farmers use zero-based `Fin N` indices, corresponding to paper indices $j-1$. The standing assumptions are $\alpha>0$, $\beta>0$, nondecreasing $z_j$, and the disclosed physical condition $z_j>0$. Subsidies may be negative. The feasible programs are explicitly restricted to all-active equilibria; their budgets are defined from payments and equilibrium outputs, not from the paper's closed-form budget formulas. Ties under a selective subsidy pay the same amount either way.
-- source:
--   Fan, Feng, Li, Shanthikumar, Wu, Output-Oriented Agricultural Subsidy Design, SSRN 4378693 (version of 2023-03-18), pp. 5–6, 10, 14, 18–19, (1), (5), Proposition 8

import Mathlib
import Definitions.Def_AgriSubsidy_Budget_CournotGame
import Definitions.Def_AgriSubsidy_Combined_Setting

namespace AgriSubsidy.Budget

def Standing {N : ℕ} (P : AgriSubsidy.Combined.Params) (z : Fin N → ℝ) : Prop :=
  0 < P.α ∧ 0 < P.β ∧ Monotone z ∧ ∀ j, 0 < z j

def selective {N : ℕ} (z : Fin N → ℝ) (sP sH : ℝ) : Fin N → ℝ :=
  fun j => max (z j * sP) sH

def game {N : ℕ} (P : AgriSubsidy.Combined.Params) (z t : Fin N → ℝ) : CournotGame N :=
  { alpha := P.α, beta := P.β,
    unitCost := fun j => z j * P.cP + P.cH - t j }

def profit {N : ℕ} (P : AgriSubsidy.Combined.Params) (z t q : Fin N → ℝ) (j : Fin N) : ℝ :=
  (game P z t).profit q j

def IsEquilibrium {N : ℕ} (P : AgriSubsidy.Combined.Params) (z t q : Fin N → ℝ) : Prop :=
  (game P z t).IsEquilibrium q

def AllActiveAt {N : ℕ} (P : AgriSubsidy.Combined.Params) (z t : Fin N → ℝ) : Prop :=
  ∃ q : Fin N → ℝ, IsEquilibrium P z t q ∧ ∀ j, 0 < q j

noncomputable def vz {N : ℕ} (z : Fin N → ℝ) : ℝ :=
  (∑ j, (z j) ^ 2) / (N : ℝ) - (AgriSubsidy.Combined.zbar z) ^ 2

noncomputable def QC {N : ℕ} (P : AgriSubsidy.Combined.Params) (z : Fin N → ℝ) (sP sH : ℝ) : ℝ :=
  (N : ℝ) / (P.β * ((N : ℝ) + 1)) * AgriSubsidy.Combined.abar P z sP sH

def plantingProg {N : ℕ} (z : Fin N → ℝ) : Set (Fin N → ℝ) :=
  Set.range (fun sP : ℝ => AgriSubsidy.Combined.combined z sP 0)

def harvestingProg {N : ℕ} (z : Fin N → ℝ) : Set (Fin N → ℝ) :=
  Set.range (fun sH : ℝ => AgriSubsidy.Combined.combined z 0 sH)

def combinedProg {N : ℕ} (z : Fin N → ℝ) : Set (Fin N → ℝ) :=
  Set.range (fun s : ℝ × ℝ => AgriSubsidy.Combined.combined z s.1 s.2)

def selectiveProg {N : ℕ} (z : Fin N → ℝ) : Set (Fin N → ℝ) :=
  Set.range (fun s : ℝ × ℝ => selective z s.1 s.2)

def feasibleBudgets {N : ℕ} (P : AgriSubsidy.Combined.Params) (z : Fin N → ℝ)
    (prog : Set (Fin N → ℝ)) (Qbar : ℝ) : Set ℝ :=
  { b | ∃ t ∈ prog, ∃ q : Fin N → ℝ,
      IsEquilibrium P z t q ∧ (∀ j, 0 < q j) ∧
      Qbar ≤ ∑ j, q j ∧ b = ∑ j, t j * q j }

noncomputable def optBudget {N : ℕ} (P : AgriSubsidy.Combined.Params) (z : Fin N → ℝ)
    (prog : Set (Fin N → ℝ)) (Qbar : ℝ) : ℝ :=
  sInf (feasibleBudgets P z prog Qbar)

noncomputable def sPP {N : ℕ} (P : AgriSubsidy.Combined.Params) (z : Fin N → ℝ) (Qbar : ℝ) : ℝ :=
  (P.β * ((N : ℝ) + 1) / (N : ℝ) * Qbar - AgriSubsidy.Combined.abar P z 0 0) / AgriSubsidy.Combined.zbar z

noncomputable def sHH {N : ℕ} (P : AgriSubsidy.Combined.Params) (z : Fin N → ℝ) (Qbar : ℝ) : ℝ :=
  P.β * ((N : ℝ) + 1) / (N : ℝ) * Qbar - AgriSubsidy.Combined.abar P z 0 0

noncomputable def sCP (P : AgriSubsidy.Combined.Params) : ℝ := P.cP / 2

noncomputable def sCH {N : ℕ} (P : AgriSubsidy.Combined.Params) (z : Fin N → ℝ) (Qbar : ℝ) : ℝ :=
  P.β * ((N : ℝ) + 1) / (N : ℝ) * Qbar - AgriSubsidy.Combined.abar P z 0 0 - P.cP * AgriSubsidy.Combined.zbar z / 2

end AgriSubsidy.Budget


