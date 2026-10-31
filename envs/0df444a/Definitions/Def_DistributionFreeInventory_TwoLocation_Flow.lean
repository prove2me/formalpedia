-- Prove2me | Definitions.Def_DistributionFreeInventory_TwoLocation_Flow
-- name    : DistributionFreeInventory_TwoLocation_Flow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:29:01.03871+00:00
-- url     : https://prove2.me/theorems/8150fc69-e582-4870-8d6c-dc417d826030
-- title:
--   Transportation recourse: feasible flows and extended cost
-- statement:
--   For $m$ supply nodes and $n$ demand locations, a feasible shipment matrix $z$ has nonnegative entries, row sums at most the inventories $y_i$, and column sums at most demands $d_j$. Its objective is
--   $$J=h\sum_i(y_i-\sum_jz_{ij})+p\sum_j(d_j-\sum_iz_{ij})+\sum_{i,j}s_{ij}z_{ij}.$$
--   The recourse value $C(y,d)$ is the infimum of $J$ over these flows. This is a separate transportation model, independent of a hierarchy or a moment law.
--
--   **Formalization Note** Indices are zero-based finite types. The value is nonnegative extended real: an infeasible flow problem costs $+\infty$. The objective is embedded with `ENNReal.ofReal`, which changes no feasible value when $h,p,s_{ij}>0$, the domain of every theorem using this model. Negative objective values outside that cost domain are clipped to zero by this definition; no theorem uses that off-domain convention. No optimizer, closed-form identity or finiteness assumption is built into the definition.
-- source:
--   Govindarajan, Sinha & Uichanco, Distribution-Free Inventory Risk Pooling in a Multilocation Newsvendor, DOI 10.1287/mnsc.2020.3719, held source.pdf, equation (2), printed p. 2 (PDF 2)

import Mathlib
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section

namespace DistributionFreeInventory.TwoLocation

/-- Feasible nonnegative shipments with supply and demand upper bounds, (2). -/
def FeasibleFlow {m n : ℕ} (y : Fin m → ℝ) (d : Fin n → ℝ)
    (z : Fin m → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ z i j) ∧ (∀ i, ∑ j, z i j ≤ y i) ∧
    (∀ j, ∑ i, z i j ≤ d j)

/-- Holding, shortage and shipment costs in the transportation recourse problem. -/
def flowObjective {m n : ℕ} (h p : ℝ) (s : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ) (d : Fin n → ℝ) (z : Fin m → Fin n → ℝ) : ℝ :=
  h * (∑ i, (y i - ∑ j, z i j)) + p * (∑ j, (d j - ∑ i, z i j)) +
    ∑ i, ∑ j, s i j * z i j

/-- On positive costs every feasible objective is nonnegative; infeasibility gives infinity. -/
def recourse {m n : ℕ} (h p : ℝ) (s : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ) (d : Fin n → ℝ) : ℝ≥0∞ :=
  ⨅ (z : Fin m → Fin n → ℝ) (_ : FeasibleFlow y d z),
    ENNReal.ofReal (flowObjective h p s y d z)

end DistributionFreeInventory.TwoLocation


