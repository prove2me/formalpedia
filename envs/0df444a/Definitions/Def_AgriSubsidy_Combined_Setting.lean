-- Prove2me | Definitions.Def_AgriSubsidy_Combined_Setting
-- name    : AgriSubsidy_Combined_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:16:52.928355+00:00
-- url     : https://prove2.me/theorems/c79a21e2-e6f4-4398-91d9-a04c8eab6bcb
-- title:
--   §3 and §4.1 — the Cournot market, combined payment, equilibrium, and averages
-- statement:
--   There are $N\ge1$ farmers with common demand parameters $\alpha,\beta>0$, input and harvesting costs $c_P,c_H$, and input-to-output ratios $z_j>0$ arranged in nondecreasing order. A combined subsidy $(s_P,s_H)$ pays farmer $j$ the amount $t_j=z_js_P+s_H$ per unit of output. For an output vector $q$, the farmer's profit is
--
--   $$\pi_j(t,q)=\left(\alpha-z_jc_P-c_H+t_j-\beta\sum_i q_i\right)q_j.$$
--
--   An equilibrium is a nonnegative output vector at which no farmer can increase this profit by unilaterally choosing another nonnegative output. When every farmer is active, $\bar z=N^{-1}\sum_jz_j$ and $\bar a(s_P,s_H)=\alpha-\bar z(c_P-s_P)-(c_H-s_H)$.
--
--   This model connects the paper's subsidy payments to its Cournot equilibrium and supplies the objects compared by the mission's theorems.
--
--   **Formalization Note** The positive-ratio condition is explicit because $z_j$ is a ratio of physical quantities; the paper states the ordering and $\alpha,\beta>0$. Costs and subsidies may be any real numbers, including taxes. The paper's farmer $j$ is Lean index $j-1$. The averages range over all farmers because the mission assumes all are active. Equilibrium is defined by best responses, rather than by the output formula that Proposition 3 must establish.
-- source:
--   Fan, Feng, Li, Shanthikumar, Wu, Output-Oriented Agricultural Subsidy Design, SSRN 4378693 (version of 2023-03-18), pp. 5–6, 10–11, (1)–(2)

import Mathlib

namespace AgriSubsidy.Combined

structure Params where
  α : ℝ
  β : ℝ
  cP : ℝ
  cH : ℝ

def Standing {N : ℕ} (P : Params) (z : Fin N → ℝ) : Prop :=
  0 < N ∧ 0 < P.α ∧ 0 < P.β ∧ Monotone z ∧ ∀ j, 0 < z j

def combined {N : ℕ} (z : Fin N → ℝ) (sP sH : ℝ) : Fin N → ℝ :=
  fun j => z j * sP + sH

def profit {N : ℕ} (P : Params) (z t q : Fin N → ℝ) (j : Fin N) : ℝ :=
  (P.α - z j * P.cP - P.cH + t j - P.β * ∑ i, q i) * q j

def IsEquilibrium {N : ℕ} (P : Params) (z t q : Fin N → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧
    ∀ j x, 0 ≤ x → profit P z t (Function.update q j x) j ≤ profit P z t q j

noncomputable def zbar {N : ℕ} (z : Fin N → ℝ) : ℝ :=
  (∑ j, z j) / (N : ℝ)

noncomputable def abar {N : ℕ} (P : Params) (z : Fin N → ℝ) (sP sH : ℝ) : ℝ :=
  P.α - zbar z * (P.cP - sP) - (P.cH - sH)

end AgriSubsidy.Combined


