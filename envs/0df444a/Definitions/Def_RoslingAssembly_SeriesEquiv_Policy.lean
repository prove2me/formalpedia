-- Prove2me | Definitions.Def_RoslingAssembly_SeriesEquiv_Policy
-- name    : RoslingAssembly_SeriesEquiv_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:37.612138+00:00
-- url     : https://prove2.me/theorems/57f9a9f5-9d03-488b-9e5f-72c1585d4b86
-- title:
--   Finite-history inventory policy
-- statement:
--   For fixed initial inventory and pipeline positions, a policy gives an order-up-to position for each item in each period as a function of the demands already observed. In paper period $t$, the available demand history is $(\xi_1,\ldots,\xi_{t-1})$, and the decision is $Y_{it}$.
--
--   $$Y_{it}=\pi_{t-1}(\xi_1,\ldots,\xi_{t-1};i).$$
--
--   This general policy interface prevents a decision from using the current or future demand.
--
--   **Formalization Note** Lean period $k=t-1$ has a history indexed by `Fin k`; measurability is a separate predicate. Decisions are evaluated only for $t\ge 1$.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4), 1989, pp. 566–567, §1, ordering sequence and paragraph before Problem P

import Mathlib

namespace RoslingAssembly.SeriesEquiv

/-- A deterministic decision rule at period `k + 1`, using exactly the `k` demands
already observed. The output is indexed by an item number. -/
abbrev Policy : Type := (k : ℕ) → (Fin k → ℝ) → ℕ → ℝ

/-- The decision for item `i` in the paper's period `t`, along the demand path `ω`.
Lean coordinate `j` of `ω` is the paper's demand `ξ_(j+1)`. -/
def decision (π : Policy) (ω : ℕ → ℝ) (i t : ℕ) : ℝ :=
  π (t - 1) (fun j => ω j.val) i

/-- Every coordinate decision is measurable in its finite demand history. -/
def MeasurablePolicy (π : Policy) : Prop :=
  ∀ k i, Measurable (fun h : Fin k → ℝ => π k h i)

end RoslingAssembly.SeriesEquiv


