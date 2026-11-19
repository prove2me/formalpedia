-- Prove2me | Definitions.Def_DualSepClusterLP_LinearProgram
-- name    : DualSepClusterLP_LinearProgram
-- status  : Definition
-- author  : @hypercube
-- created : 2026-11-18T17:39:44.08903+00:00
-- url     : https://prove2.me/theorems/55a8b0c5-9d0e-4f94-a80b-3ff08501f9c2
-- title:
--   Column costs and the primal and dual cluster LP
-- statement:
--   A subset pays for its internal negative pairs and half of its positive boundary. Nonnegative real primal weights cover each vertex exactly once. The dual allows signed prices and bounds each subset's price by its cost.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, STOC 2027 paper #79, §2, equations (1)–(3). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/79.pdf

import Mathlib
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_DualSepClusterLP_Setting

namespace DualSepClusterLP

/-- Each negative pair internal to S counts once. Each positive pair crossing S counts one half.
Only the upper triangle of the sign matrix encodes edges. -/
noncomputable def subsetCost {n : ℕ} (G : Graph n) (S : Finset (Fin n)) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then
    if G i j then (if decide (i ∈ S) != decide (j ∈ S) then (1 : ℝ) / 2 else 0)
    else (if i ∈ S ∧ j ∈ S then 1 else 0)
  else 0

/-- Primal constraints (2), including every subset and an equality for every vertex. -/
def PrimalFeasible {n : ℕ} (z : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ z S) ∧ ∀ i : Fin n, (∑ S : Finset (Fin n), if i ∈ S then z S else 0) = 1

noncomputable def primalValue {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), subsetCost G S * z S

/-- Dual constraints (3). The vertex prices are unrestricted in sign. -/
def DualFeasible {n : ℕ} (G : Graph n) (q : Fin n → ℝ) : Prop :=
  ∀ S : Finset (Fin n), (∑ i ∈ S, q i) ≤ subsetCost G S

end DualSepClusterLP


