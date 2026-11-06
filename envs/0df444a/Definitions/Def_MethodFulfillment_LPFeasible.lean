-- Prove2me | Definitions.Def_MethodFulfillment_LPFeasible
-- name    : MethodFulfillment_LPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:53.006411+00:00
-- url     : https://prove2.me/theorems/e28e7279-2c63-404e-b1ab-f332a0714df7
-- title:
--   Feasibility for the expected LP (6)–(9)
-- statement:
--   A vector $x=(x_m)$ indexed by the methods of all order types is **feasible for the expected LP** when
--
--   1. $x_m\ge0$ for every method $m$ (constraint (9));
--   2. $\sum_{m\in M(q)}x_m=p_a(q)$ for every order type $q$ (constraint (7));
--   3. $\sum_{q}\sum_{m\in M(q),\,(i,k)\in m}x_m\le S_{ik}$ for every item $i$ and facility $k$ (constraint (8)).
--
--   The LP is the relaxation of (1)–(4) in which the arrivals are replaced by their expectations and aggregated over time.
--
--   **Formalization Note** The variable is a function of the order type and the set of pairs; only its values at methods $m\in M(q)$ are read. Constraint (8) ranges over real facilities, as in the paper.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), (7)–(9), p.11

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_pa

namespace MethodFulfillment

/-- Feasibility for the method-based expected LP (6)–(9) (Amil, Makhdoumi & Wei, manuscript,
PDF sha256 197c13b9…, (7)–(9), p.11): `x q m ≥ 0` for every method `m` of `q` ((9)),
`∑_{m ∼ q} x_m = pa(q)` for every order type `q` ((7)), and `∑_{m ∋ (i,k)} x_m ≤ S_{ik}` for every
pair ((8)).

**Formalization Note.** The variable `x : Q → Finset (I × K) → ℝ` is read only at methods
`m ∈ methods q`; its values elsewhere are irrelevant. Constraint (8) ranges over real facilities
only, as on p.11 (the dummy facility is implicit). -/
def LPFeasible {I K Q : Type} [DecidableEq I] [DecidableEq K] [Fintype Q] {T : ℕ}
    (P : Instance I K Q T) (x : Q → Finset (I × K) → ℝ) : Prop :=
  (∀ q, ∀ m ∈ P.methods q, 0 ≤ x q m) ∧ (∀ q, ∑ m ∈ P.methods q, x q m = pa P q) ∧
    ∀ i k, ∑ q, ∑ m ∈ (P.methods q).filter (fun m => (i, k) ∈ m), x q m ≤ P.S i k

end MethodFulfillment


