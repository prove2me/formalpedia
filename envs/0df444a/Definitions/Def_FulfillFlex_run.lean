-- Prove2me | Definitions.Def_FulfillFlex_run
-- name    : FulfillFlex_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:31.371606+00:00
-- url     : https://prove2.me/theorems/7e041ebd-3539-494d-b744-799475953301
-- title:
--   The sample path of a spillover limit policy
-- statement:
--   A **spillover limit policy** fixes a limit $\theta_{j'j}$ for each link $(j',j)\in A$ with $j\ne j'$, on the amount of inventory at DC $j'$ that may fill spillover demand from DC $j$. When an order arrives at DC $j$:
--
--   1. if DC $j$ has inventory, the order is filled locally;
--   2. otherwise, if the customer abandons, the order is a lost sale;
--   3. otherwise the order is filled from the lowest cost flexible DC $j'$ that has inventory and is under its limit $\theta_{j'j}$, and it is lost if there is no such DC.
--
--   The policy satisfies the local no-holdback requirement by construction, and it never declines an eligible spillover. `run` is its final state on an arrival sequence: remaining inventory, and the counts of local fulfillments, spillover fulfillments and lost sales.
--
--   **Formalization Note** Inventory is real and each shipment uses one unit, so a DC has inventory when its remaining stock is at least $1$; for integer inventories this is the paper's model. A DC $j'$ is under its limit when the number of DC $j$ orders it has already filled, plus one, is at most $\theta_{j'j}$, so it fills at most $\theta_{j'j}$ of them. Cost ties go to the smallest index. The aggregate per-DC limit $\theta_j$ of the paper is omitted, which the paper treats as non-binding when unspecified.
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), §2.2, pp.11–12

import Mathlib
import Definitions.Def_FulfillFlex_DC

namespace FulfillFlex

/-- The state of the fulfillment system along a sample path: remaining inventory, and the counts
of local fulfillments, of spillover fulfillments (`spill j' j` units of DC `j` demand filled from
DC `j'`) and of lost sales. -/
structure State (N : ℕ) where
  /-- Remaining inventory at each DC. -/
  inv : DC N → ℝ
  /-- Demand at each DC filled by that DC's own inventory. -/
  localFill : DC N → ℕ
  /-- `spill j' j` is the amount of DC `j` demand filled from DC `j'` inventory. -/
  spill : DC N → DC N → ℕ
  /-- Lost sales at each DC. -/
  lost : DC N → ℕ

/-- The state at time 0: inventory `r` and all counts zero. -/
def initState {N : ℕ} (r : DC N → ℝ) : State N :=
  ⟨r, 0, 0, 0⟩

/-- Fill one unit of DC `j` demand locally. -/
noncomputable def State.fillLocal {N : ℕ} (s : State N) (j : DC N) : State N :=
  { s with
    inv := Function.update s.inv j (s.inv j - 1)
    localFill := Function.update s.localFill j (s.localFill j + 1) }

/-- Fill one unit of DC `j` demand from DC `k`. -/
noncomputable def State.fillSpill {N : ℕ} (s : State N) (k j : DC N) : State N :=
  { s with
    inv := Function.update s.inv k (s.inv k - 1)
    spill := Function.update s.spill k (Function.update (s.spill k) j (s.spill k j + 1)) }

/-- Lose one unit of DC `j` demand. -/
noncomputable def State.loseOrder {N : ℕ} (s : State N) (j : DC N) : State N :=
  { s with lost := Function.update s.lost j (s.lost j + 1) }

open Classical in
/-- The flexible DCs eligible to fill a DC `j` order: every `k ≠ j` with `(k, j) ∈ A` that has
inventory and is still under its spillover limit `θ k j`.

**Formalization Note** "Has inventory" means at least one unit in stock, and "under the limit"
means `spill k j + 1 ≤ θ k j`, so that at most `θ k j` units of DC `j` demand are ever filled from
DC `k`. -/
noncomputable def eligible {N : ℕ} (A : Set (DC N × DC N)) (θ : DC N → DC N → ℝ) (s : State N)
    (j : DC N) : Finset (DC N) :=
  Finset.univ.filter fun k =>
    k ≠ j ∧ (k, j) ∈ A ∧ 1 ≤ s.inv k ∧ ((s.spill k j : ℝ) + 1 ≤ θ k j)

open Classical in
/-- The lowest cost DC of `E` for a DC `j` order, ties going to the smallest index; `none` exactly
when `E` is empty. -/
noncomputable def lowestCostSource {N : ℕ} (c : DC N → DC N → ℝ) (j : DC N) (E : Finset (DC N)) :
    Option (DC N) :=
  if h : (E.filter fun k => ∀ k' ∈ E, c k j ≤ c k' j).Nonempty then
    some ((E.filter fun k => ∀ k' ∈ E, c k j ≤ c k' j).min' h)
  else none

/-- **One step of a spillover limit policy.**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), §2.2, p.11: "When a demand arrives at DC
j, the demand is fulfilled locally if DC j has inventory. Otherwise, the policy fulfills the demand
from the lowest cost flexible DC j′ that has inventory and has not fulfilled more than θj′j units
of spillover demand from DC j already (subject to any random abandonment that may occur in the
process of spillover fulfillment). If no such flexible DC exists, the demand is lost."

An arrival is a pair `(j, b)` of its DC and its abandonment coin (`b = true` means the customer
abandons if the order is not filled locally). If DC `j` has at least one unit, the order is filled
locally. Otherwise, if the customer abandons, the order is lost. Otherwise it is filled from the
lowest cost eligible DC, and it is lost if there is none.

**Formalization Note** Inventory is real and each shipment uses one unit, so a DC has inventory
when its remaining stock is at least 1. The aggregate per-DC limit `θ_j` of pp.11–12 is omitted;
the paper sets unspecified limits non-binding (p.12). -/
noncomputable def step {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ)
    (θ : DC N → DC N → ℝ) (s : State N) (a : DC N × Bool) : State N :=
  if 1 ≤ s.inv a.1 then
    s.fillLocal a.1
  else if a.2 then
    s.loseOrder a.1
  else
    match lowestCostSource c a.1 (eligible A θ s a.1) with
    | some k => s.fillSpill k a.1
    | none => s.loseOrder a.1

/-- **The sample path of a spillover limit policy.** The final state of the policy with limits `θ`
from initial inventory `r` on the arrival sequence `w`. -/
noncomputable def run {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ)
    (θ : DC N → DC N → ℝ) (r : DC N → ℝ) (w : List (DC N × Bool)) : State N :=
  w.foldl (step A c θ) (initState r)

end FulfillFlex


