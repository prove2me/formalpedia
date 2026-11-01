-- Prove2me | Definitions.Def_TaylorInv_InClass
-- name    : TaylorInv_InClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:56.399884+00:00
-- url     : https://prove2.me/theorems/d2458dca-73fa-47be-b337-0586318d972c
-- title:
--   The class of systems over which Theorem 1's constants are uniform
-- statement:
--   Fix bounds $h_0,\underline h,\bar h,\bar b,\underline\ell,\bar u,\bar D,\bar\epsilon,\bar B,\bar M,\bar\sigma$. A $J$-retailer system is **in the class** if it satisfies Assumptions 1–3 and the cost order with the bounds $\bar D,\bar\epsilon,\bar B,\bar M,\bar\sigma$, its warehouse cost equals $h_0$, and for every retailer
--   $$
--   \underline h\le h'_j\le\bar h\le b_j\le\bar b,\qquad \underline\ell\le\ell_j,\qquad u_j\le\bar u .
--   $$
--
--   The paper calls $\alpha$, $\underline p$, $\underline t$, $\bar t$, $\underline\ell$, $\underline h$, $\bar h$, $\bar b$ "constants" in the proof of Theorem 1; this class makes "$O(\cdot)$" precise as a bound that depends only on these numbers and $P$, uniformly in $J$.
--
--   **Formalization Note** The paper's $\underline h,\bar h,\bar b$ are the min and max over retailers; here they are bounds fixed in advance, which every system with $\max_jh'_j\le\min_jb_j$ satisfies for suitable values.
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, Theorem 1, p.16; constants of its proof, pp.OA7–OA12

import Mathlib
import Definitions.Def_TaylorInv_Model

open MeasureTheory

namespace TaylorInv

/-- The class of systems over which the constants of Theorem 1 are uniform (Huang, Shang, Yang &
Zhou, SSRN 3993516 (Jan 29 2023), Theorem 1, p.16, and the constants of its proof, pp.OA7–OA12):
the system satisfies Assumptions 1–3 and the cost order with the bounds `D̄, ϵ̄, B̄, M̄, σ̄`, its
warehouse cost is `h₀`, its retailer costs satisfy `h̲ ≤ h′_j ≤ h̄ ≤ b_j ≤ b̄`, and its density bounds
satisfy `ℓ̲ ≤ ℓ_j` and `u_j ≤ ū`.

**Formalization Note** The paper's `h̲, h̄, b̄` are the min and max over the retailers, and its
`ℓ̲ = min_j ℓ_j`, `α = max_j u_j/ℓ_j` are called constants; here they are bounds fixed in advance, so
that "`O(·)`" means a constant depending only on these bounds and `P`, uniform in `J`. -/
structure Model.InClass {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model J P Ω)
    (μ : Measure Ω) (h₀ hlow hbar bbar ℓlow ubar Dbar ϵbar Bbar Mbar σbar : ℝ) : Prop where
  /-- Assumptions 1–3 and the cost order of p.8. -/
  assumptions : M.Assumptions Dbar ϵbar Bbar Mbar σbar μ
  /-- The warehouse holding cost is `h₀`. -/
  h₀_eq : M.h₀ = h₀
  /-- `h̲ ≤ h′_j ≤ h̄`. -/
  h'_mem : ∀ j, hlow ≤ M.h' j ∧ M.h' j ≤ hbar
  /-- `h̄ ≤ b_j ≤ b̄`. -/
  b_mem : ∀ j, hbar ≤ M.b j ∧ M.b j ≤ bbar
  /-- `ℓ̲ ≤ ℓ_j`. -/
  ℓ_ge : ∀ j, ℓlow ≤ M.ℓ j
  /-- `u_j ≤ ū`. -/
  u_le : ∀ j, M.u j ≤ ubar

end TaylorInv


