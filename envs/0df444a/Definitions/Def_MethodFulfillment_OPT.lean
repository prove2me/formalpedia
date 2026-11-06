-- Prove2me | Definitions.Def_MethodFulfillment_OPT
-- name    : MethodFulfillment_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:49.46751+00:00
-- url     : https://prove2.me/theorems/67fc984e-19d7-4866-9964-5d98fedda6bc
-- title:
--   Offline optimum $\mathrm{OPT}(D)$ of the integer program (1)–(4)
-- statement:
--   Fix an arrival sequence $\omega$. An **offline plan** chooses a method $a_t$ in every period: no pairs when no order arrives, and a method $a_t\in M(q)$ when an order of type $q$ arrives (constraints (2) and (4)); it is **feasible** when each pair $(i,k)$ is used in at most $S_{ik}$ periods (constraint (3)). Its cost is $\sum_t c_{a_t}$ over the periods with an arrival (objective (1)). The **offline optimum** is
--   $$\mathrm{OPT}(\omega)=\min\Big\{\sum_{t:\,\omega_t\ne\varnothing}c_{a_t}\;:\;a\text{ feasible for }\omega\Big\}.$$
--   It is the cost of a clairvoyant platform that knows all arrivals in advance.
--
--   **Formalization Note** The minimum is written as the real infimum of the costs of feasible plans. There are finitely many plans, and under `Valid` the plan using the discard method in every period is feasible (as the paper notes on p.10), so the infimum is attained. The helper definitions `PlanFeasible` and `offCost` are the feasibility conditions (2)–(4) and the objective (1).
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), (1)–(4), pp.9–10

import Mathlib
import Definitions.Def_MethodFulfillment_Instance

namespace MethodFulfillment

/-- Feasibility of an offline plan for the integer program (1)–(4) (Amil, Makhdoumi & Wei,
manuscript, PDF sha256 197c13b9…, (1)–(4), pp.9–10). Given the arrival sequence `ω`, a plan
`a : Fin T → Finset (I × K)` picks one method per period: no pairs when no order arrives, a method
of `q` when `q` arrives ((2) and (4)), and it uses each pair `(i, k)` in at most `S i k` periods
((3)). -/
def PlanFeasible {I K Q : Type} [DecidableEq I] [DecidableEq K] {T : ℕ} (P : Instance I K Q T)
    (ω : Fin T → Option Q) (a : Fin T → Finset (I × K)) : Prop :=
  (∀ t, ω t = none → a t = ∅) ∧ (∀ t q, ω t = some q → a t ∈ P.methods q) ∧
    ∀ i k, (Finset.univ.filter fun t => (i, k) ∈ a t).card ≤ P.S i k

/-- The objective (1) of an offline plan: the sum over periods of the cost of the method used for
the arriving order, `0` in periods without an arrival. -/
def offCost {I K Q : Type} {T : ℕ} (P : Instance I K Q T) (ω : Fin T → Option Q)
    (a : Fin T → Finset (I × K)) : ℝ :=
  ∑ t, match ω t with
    | none => 0
    | some q => P.c q (a t)

/-- The offline optimum `OPT(D)` of the integer program (1)–(4) (Amil, Makhdoumi & Wei,
manuscript, PDF sha256 197c13b9…, (1)–(4), pp.9–10), for the arrival sequence `ω`.

**Formalization Note.** `OPT` is the real infimum of the costs of the feasible plans. Plans range
over the finite type `Fin T → Finset (I × K)`, so this set is finite; under `Valid` it is nonempty
(the plan using the discard method `∅` in every period is feasible, as the paper notes on p.10),
so the infimum is attained and is the minimum of (1). The junk value of `sInf ∅` is never reached
under `Valid`. -/
noncomputable def OPT {I K Q : Type} [DecidableEq I] [DecidableEq K] {T : ℕ}
    (P : Instance I K Q T) (ω : Fin T → Option Q) : ℝ :=
  sInf {v | ∃ a, PlanFeasible P ω a ∧ offCost P ω a = v}

end MethodFulfillment


