-- Prove2me | Definitions.Def_MNLStability_step
-- name    : MNLStability_step
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:01.123993+00:00
-- url     : https://prove2.me/theorems/5405aa75-129f-4787-8265-f7f7e862215e
-- title:
--   One MNL purchase decision facing the current stock
-- statement:
--   Let $V$ be the current stock vector and $S=\{i: V_i>0\}$ the set of products in stock. One arriving customer chooses according to the **Multinomial Logit** model:
--
--   1. she buys one unit of product $i\in S$ with probability $\dfrac{w_i}{w_0+w(S)}$;
--   2. she leaves without buying with probability $\dfrac{w_0}{w_0+w(S)}$.
--
--   Products out of stock are never chosen. This one-step law drives the dynamic demand process.
--
--   **Formalization Note** The outcome is an `Option (Fin n)`, with `none` the no-purchase option. For positive weights the masses sum to $1$ (proved in the mission's sanity file); for weights that are not positive, which no statement admits, the definition returns the point mass at `none`.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §1.1, p.4

import Mathlib
import Definitions.Def_MNLStability_Weights

open scoped ENNReal

namespace MNLStability

variable {n : ℕ}

/-- The products in stock under the stock vector `V`: `S = {i | 0 < V i}`. -/
def inStock (V : Fin n → ℕ) : Finset (Fin n) := Finset.univ.filter fun i => 0 < V i

/-- The MNL choice masses of one customer facing the stock vector `V` (SSRN:3498325, §1.1, p.4):
`none` (no purchase) has mass `w₀ / (w₀ + w(S))`, `some i` has mass `wᵢ / (w₀ + w(S))` when
`i ∈ S`, and `0` otherwise, where `S` is the set of products in stock. -/
noncomputable def stepMass (wts : Weights n) (V : Fin n → ℕ) : Option (Fin n) → ℝ≥0∞
  | none => ENNReal.ofReal (wts.w0 / (wts.w0 + wts.wsum (inStock V)))
  | some i =>
    if 0 < V i then ENNReal.ofReal (wts.w i / (wts.w0 + wts.wsum (inStock V))) else 0

/-- The purchase decision of one arriving customer facing the stock vector `V`, under the
Multinomial Logit model (SSRN:3498325, §1.1, p.4): `none` is the no-purchase option, `some i` a
purchase of one unit of product `i`.

**Formalization Note.** For positive weights the masses `stepMass` sum to `1`, and this is the MNL
choice law. For weights that are not positive (excluded by every statement of the mission) the
masses may fail to sum to `1`, and the definition falls back to the point mass at `none`. -/
noncomputable def step (wts : Weights n) (V : Fin n → ℕ) : PMF (Option (Fin n)) :=
  if h : ∑ a, stepMass wts V a = 1 then PMF.ofFintype (stepMass wts V) h else PMF.pure none

end MNLStability


