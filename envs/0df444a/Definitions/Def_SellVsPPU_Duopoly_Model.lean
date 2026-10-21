-- Prove2me | Definitions.Def_SellVsPPU_Duopoly_Model
-- name    : SellVsPPU_Duopoly_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:37.771412+00:00
-- url     : https://prove2.me/theorems/893eeaf4-4be0-42bc-9b36-680cf69e65a8
-- title:
--   §2, pp. 7–9; A.2.1, p. 37; Proposition 3, p. 14 — selling and pay-per-use duopoly model
-- statement:
--   A seller charges $p_s$ for unlimited use of a product, and a pay-per-use provider charges $p_u$ per use. Customer usage $q$ is uniform on $[0,q_m]$. With value $a$ per use, customer utilities are $U_s(q;p_s)=qa-p_s$ and $U_u(q;p_u)=q(a-p_u)$. The seller's market consists of customers with $U_s\ge0$ and $U_s\ge U_u$; the provider's market consists of customers with $U_u\ge0$ and $U_u\ge U_s$. Under strong pooling, the provider's effective cost per use is $c_u=c/q_m+\delta$. The profit functions integrate seller margin $p_s-c$ and provider margin times use $(p_u-c_u)q$ over their respective markets, with density $1/q_m$.
--
--   The model defines a price equilibrium by both firms' global profit maximization, the two regime formulas for equilibrium prices and profits, and the piecewise delivery-cost threshold $\bar\delta(c)$ of Proposition 3.
--
--   **Formalization Note** The nonnegative delivery cost, positive product cost and value and usage bounds, and $c_u\le a$ describe the admissible region. The printed market inequalities are weak, so ties belong to both segments; they have zero measure at the relevant equilibria. The seller's deviations range over all real prices and the provider's over prices at most $a$.
-- source:
--   Ladas, Kavadias & Loch, Product Selling vs. Pay-Per-Use Service, SSRN 3356458 manuscript (PDF of 16 Apr 2021; Management Science, doi:10.1287/mnsc.2021.4125), pp. 7–9, §2.1–2.3; p. 14, Proposition 3; p. 37, A.2.1 equilibrium table

import Mathlib
open MeasureTheory

namespace SellVsPPU.Duopoly

structure Params where
  a : ℝ
  qm : ℝ
  c : ℝ
  delta : ℝ

def Params.Admissible (P : Params) : Prop :=
  0 < P.a ∧ 0 < P.qm ∧ 0 < P.c ∧ 0 ≤ P.delta ∧ P.c / P.qm + P.delta ≤ P.a

noncomputable def cu (P : Params) : ℝ := P.c / P.qm + P.delta

def Us (P : Params) (q ps : ℝ) : ℝ := q * P.a - ps

def Uu (P : Params) (q pu : ℝ) : ℝ := q * (P.a - pu)

def sellSet (P : Params) (ps pu : ℝ) : Set ℝ :=
  {q | q ∈ Set.Icc 0 P.qm ∧ 0 ≤ Us P q ps ∧ Uu P q pu ≤ Us P q ps}

def ppuSet (P : Params) (ps pu : ℝ) : Set ℝ :=
  {q | q ∈ Set.Icc 0 P.qm ∧ 0 ≤ Uu P q pu ∧ Us P q ps ≤ Uu P q pu}

noncomputable def profitS (P : Params) (ps pu : ℝ) : ℝ :=
  (ps - P.c) * (volume (sellSet P ps pu)).toReal / P.qm

noncomputable def profitU (P : Params) (ps pu : ℝ) : ℝ :=
  (pu - cu P) * (∫ q in ppuSet P ps pu, q) / P.qm

def IsPriceEq (P : Params) (ps pu : ℝ) : Prop :=
  pu ≤ P.a ∧
    (∀ ps' : ℝ, profitS P ps' pu ≤ profitS P ps pu) ∧
    (∀ pu' : ℝ, pu' ≤ P.a → profitU P ps pu' ≤ profitU P ps pu)

noncomputable def deltaBar (a qm c : ℝ) : ℝ :=
  if c ≤ a * qm / 3 then c / (2 * qm)
  else a - c / qm - 2 * a * ((a * qm - c) / (a * qm + c)) ^ 2

noncomputable def psStar (P : Params) : ℝ :=
  if P.c ≤ P.qm * (P.a / 2 - P.delta)
  then (3 * P.c + 2 * P.delta * P.qm) / 2
  else (P.c + P.a * P.qm) / 2

noncomputable def puStar (P : Params) : ℝ :=
  if P.c ≤ P.qm * (P.a / 2 - P.delta)
  then 2 * (P.c / P.qm + P.delta)
  else P.a

noncomputable def profSStar (P : Params) : ℝ :=
  if P.c ≤ P.qm * (P.a / 2 - P.delta)
  then (P.c + 2 * P.delta * P.qm) ^ 2 / (8 * (P.c + P.delta * P.qm))
  else (P.a * P.qm - P.c) ^ 2 / (4 * P.qm * P.a)

noncomputable def profUStar (P : Params) : ℝ :=
  if P.c ≤ P.qm * (P.a / 2 - P.delta)
  then (3 * P.c + 2 * P.delta * P.qm) ^ 2 / (32 * (P.c + P.delta * P.qm))
  else (P.qm * (P.a - P.delta) - P.c) * (P.a * P.qm + P.c) ^ 2 /
    (8 * P.qm ^ 2 * P.a ^ 2)

end SellVsPPU.Duopoly


