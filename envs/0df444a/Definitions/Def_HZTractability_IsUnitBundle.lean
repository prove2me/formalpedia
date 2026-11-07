-- Prove2me | Definitions.Def_HZTractability_IsUnitBundle
-- name    : HZTractability_IsUnitBundle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:49.044752+00:00
-- url     : https://prove2.me/theorems/d3db82f6-9884-4f66-a514-e7d8aeee4842
-- title:
--   Budget-one unit bundles and the optimal utility $V_i(p)$
-- statement:
--   In an HZ market with goods $j$ and prices $p\ge 0$, a **budget-one unit bundle** is a vector $y$ with
--   $$
--   y_j\ge 0\ \text{for every good } j,\qquad \sum_j y_j = 1,\qquad \sum_j p_j y_j\le 1 .
--   $$
--   The **budget-one optimal utility** of buyer $i$ with utilities $u_{ij}$ is the value of the linear program (OptBundle)
--   $$
--   V_i(p)=\max_y \sum_j u_{ij}y_j \quad\text{over budget-one unit bundles } y .
--   $$
--   The predicate "$v$ is $V_i(p)$" says that some budget-one unit bundle gives buyer $i$ utility $v$ and none gives more.
--
--   $V_i(p)$ is the benchmark of the approximate equilibrium notion and the primal value of the demand dual.
--
--   **Formalization Note** The maximum is stated as attained and maximal, so there is no supremum junk value. At normalized prices (some price zero) the program is feasible and bounded, so $V_i(p)$ exists.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §2.2, display (OptBundle), p.7 (PDF p.9)

import Mathlib

namespace HZTractability

/-- **A budget-one unit bundle** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848, held version,
sha256 74b7bf9f…, §2.2, display (OptBundle), p.7 (PDF 9)): a vector `y` of quantities of the goods
with `y_j ≥ 0` for every good `j`, total quantity `∑_j y_j = 1`, and cost `∑_j p_j y_j ≤ 1` at the
prices `p`.

**Formalization Note** Goods form an arbitrary finite type `G`; prices and quantities are real. -/
def IsUnitBundle {G : Type} [Fintype G] (p : G → ℝ) (y : G → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ ∑ j, y j = 1 ∧ ∑ j, p j * y j ≤ 1

/-- **The budget-one optimal utility** `V_i(p)` (arXiv:2610.35848, §2.2, (OptBundle), p.7 (PDF 9)):
`IsOptValue u p i v` says that `v` is the value of the linear program
`max_y ∑_j u_ij y_j` subject to `∑_j y_j = 1`, `∑_j p_j y_j ≤ 1`, `y ≥ 0`, i.e. some budget-one unit
bundle has utility `v` for buyer `i` and none has more.

**Formalization Note** The maximum is stated as "attained and an upper bound" instead of a
supremum, so there is no junk value: at prices with no affordable unit bundle no `v` qualifies. At
normalized prices (some price is zero) the program is feasible and bounded, so `V_i(p)` exists. -/
def IsOptValue {B G : Type} [Fintype G] (u : B → G → ℝ) (p : G → ℝ) (i : B) (v : ℝ) : Prop :=
  (∃ y, IsUnitBundle p y ∧ ∑ j, u i j * y j = v) ∧
    ∀ y, IsUnitBundle p y → ∑ j, u i j * y j ≤ v

end HZTractability


