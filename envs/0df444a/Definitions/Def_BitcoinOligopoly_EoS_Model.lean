-- Prove2me | Definitions.Def_BitcoinOligopoly_EoS_Model
-- name    : BitcoinOligopoly_EoS_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:13:43.364726+00:00
-- url     : https://prove2.me/theorems/571d28bc-1785-44de-accf-c571becaba74
-- title:
--   §§3–4 — the economies-of-scale mining contest
-- statement:
--   There are $n\ge2$ miners competing for a prize of value one. Miner $i$ chooses a nonnegative investment $q_i$ and pays $c_iq_i$, where $c_i>0$. The economies-of-scale exponent is $\alpha\ge1$. The miner's market share and utility are
--
--   $$
--   x_i(q)=\begin{cases}q_i^\alpha/\sum_jq_j^\alpha,&\sum_jq_j^\alpha>0,\\0,&q_j=0\text{ for all }j,\end{cases}
--   \qquad U_i(q)=x_i(q)-c_iq_i.
--   $$
--
--   An equilibrium is a pure Nash equilibrium: no miner gains by replacing its investment with any other nonnegative amount. The auxiliary function $f_\alpha(x)=x^{1-1/\alpha}(1-x)$ is the function introduced in the proof of Proposition 1. These definitions fix the contest used by Theorem 2 and its supporting results.
--
--   **Formalization Note** Miners are indexed by `Fin n`. Real exponentiation uses `Real.rpow`. The zero-investment profile has zero share for every miner, as the paper specifies. The standing assumptions are kept in a predicate and imposed by every paper theorem; cost sorting is only a relabelling convention and is not imposed.
-- source:
--   Arnosti & Weinberg, Bitcoin: A Natural Oligopoly, arXiv:1811.08572v1, pp. 5–6 (PDF 6–7), §3 model; pp. 9–10 (PDF 10–11), §4 model and proof of Proposition 1

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_PureGame

namespace BitcoinOligopoly.EoS

/-- The number of miners, their unit costs, and the exponent in the contest success function. -/
structure Params (n : ℕ) where
  c : Fin n → ℝ
  α : ℝ

/-- The standing assumptions in §§3–4: at least two miners, exponent at least one,
and strictly positive unit costs. -/
def Params.Standing {n : ℕ} (P : Params n) : Prop :=
  2 ≤ n ∧ 1 ≤ P.α ∧ ∀ i, 0 < P.c i

/-- Miner `i`'s share of the unit prize, zero when all investments are zero. -/
noncomputable def share {n : ℕ} (P : Params n) (q : Fin n → ℝ) (i : Fin n) : ℝ :=
  if (∑ j, q j ^ P.α) = 0 then 0 else q i ^ P.α / ∑ j, q j ^ P.α

/-- Miner `i`'s share of the prize minus linear investment cost. -/
noncomputable def utility {n : ℕ} (P : Params n) (q : Fin n → ℝ) (i : Fin n) : ℝ :=
  share P q i - P.c i * q i

/-- The EoS model's pure Nash equilibrium over nonnegative investments. -/
def IsEquilibrium {n : ℕ} (P : Params n) (q : Fin n → ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash
    (fun _ : Fin n => {x : ℝ | 0 ≤ x}) (fun i q' => utility P q' i) q

/-- The function `f(x) = x^(1 - 1/α) (1 - x)` from the proof of Proposition 1. -/
noncomputable def fShape (α x : ℝ) : ℝ := x ^ (1 - 1 / α) * (1 - x)

end BitcoinOligopoly.EoS


