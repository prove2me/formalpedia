-- Prove2me | Definitions.Def_DualSepClusterLP_SparseInput
-- name    : DualSepClusterLP_SparseInput
-- status  : Definition
-- author  : @hypercube
-- created : 2026-11-18T17:40:49.754193+00:00
-- url     : https://prove2.me/theorems/5ed56735-49bb-4879-8b9f-dc613de75695
-- title:
--   Explicit sparse fractional cluster-LP solutions
-- statement:
--   Encode a list of distinct subsets with positive rational weights. The induced primal vector is zero outside the list and must have exact unit vertex marginals.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, STOC 2027 paper #79, §7 and Appendix F, explicitly represented primal solution. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/79.pdf

import Mathlib
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_DualSepClusterLP_LinearProgram
import Definitions.Def_DualSepClusterLP_SeparationEncoding

namespace DualSepClusterLP

/-- A list of subsets and their explicitly represented rational LP weights. -/
abbrev SparseWeights (n : ℕ) := List (Finset (Fin n) × ℚ)

/-- The vector indexed by all subsets, extended by zero off the listed support. -/
def weightAt {n : ℕ} (L : SparseWeights n) (S : Finset (Fin n)) : ℚ :=
  (L.map fun e => if e.1 = S then e.2 else 0).sum

/-- A sparse representation contains each support set once with its positive weight. -/
def ValidSupport {n : ℕ} (L : SparseWeights n) : Prop :=
  (L.map Prod.fst).Nodup ∧ (∀ e ∈ L, 0 < e.2) ∧
    PrimalFeasible (fun S => (weightAt L S : ℝ))

/-- Graph header (accuracy field zero), self-delimiting support length, then an n-bit
membership mask and a self-delimiting rational weight for each listed subset. -/
def roundingInput {n : ℕ} (G : Graph n) (L : SparseWeights n) : List Bool :=
  graphInput 0 G ++ lengthPrefixedNat L.length ++
    L.flatMap (fun e => (List.finRange n).map (fun i => decide (i ∈ e.1)) ++ priceBits e.2)

end DualSepClusterLP


