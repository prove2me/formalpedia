-- Prove2me | Definitions.Def_PCLAssort_DFeasible
-- name    : PCLAssort_DFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:02.03807+00:00
-- url     : https://prove2.me/theorems/050ee82c-8faa-4092-8882-813e46637b18
-- title:
--   Feasible set of the LP (D)
-- statement:
--   The LP (D) is obtained from the dual D$(z)$ of LP$(z)$ by making $z$ a variable and adding a constraint. Its feasible set consists of the $(\alpha,\beta,\gamma,\delta,z)$ with
--
--   1. $\alpha_{ij}+\beta_{ij}\ge w_{ij}(z)$ for every $(i,j)\in E$;
--   2. $-\sum_{j\mid(i,j)\in E}\alpha_{ij}+\sum_{j\mid(j,i)\in E}\beta_{ji}+\gamma_i+s_i\delta\ge 0$ for every $i\in[n]$;
--   3. $\sum_{(i,j)\in E}\beta_{ij}+\sum_{i\in[n]}\gamma_i+c\delta=v_0z$;
--   4. $\alpha,\beta,\gamma,\delta\ge 0$, with $z$ free.
--
--   Minimizing the dual objective over this set finds the fixed point of $g(\cdot)/v_0$ (Lemma 9).
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §4.2, (D), p.793 (PDF p.9)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_pclEdges
import Definitions.Def_PCLAssort_pclWeight
import Definitions.Def_PCLAssort_DualVars
import Definitions.Def_PCLAssort_dualObjective

namespace PCLAssort

/-- Feasible set of the LP (D) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §4.2, p.793), obtained from the dual D(z) of LP(z) by making
`z` a decision variable:
`α_ij + β_ij ≥ w_ij(z)` for `(i,j) ∈ E`;
`−∑_{j|(i,j)∈E} α_ij + ∑_{j|(j,i)∈E} β_ji + γ_i + s_i δ ≥ 0` for `i ∈ [n]`;
`∑_{(i,j)∈E} β_ij + ∑_{i∈[n]} γ_i + cδ = v_0 z`; `α, β, γ, δ ≥ 0`, `z` free. -/
def DFeasible {n : ℕ} (I : PCLInstance n) (s : Fin n → ℝ) (c : ℝ) : Set (DualVars n) :=
  {d | (∀ e ∈ pclEdges n, pclWeight I d.z e ≤ d.α e + d.β e) ∧
    (∀ i : Fin n, 0 ≤ -(∑ e ∈ (pclEdges n).filter (fun e => e.1 = some i), d.α e) +
      ∑ e ∈ (pclEdges n).filter (fun e => e.2 = some i), d.β e + d.γd i + s i * d.δ) ∧
    dualObjective c d = I.v0 * d.z ∧
    (∀ e ∈ pclEdges n, 0 ≤ d.α e ∧ 0 ≤ d.β e) ∧ (∀ i, 0 ≤ d.γd i) ∧ 0 ≤ d.δ}

end PCLAssort


