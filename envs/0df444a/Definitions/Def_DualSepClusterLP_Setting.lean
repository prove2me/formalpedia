-- Prove2me | Definitions.Def_DualSepClusterLP_Setting
-- name    : DualSepClusterLP_Setting
-- status  : Definition
-- author  : @hypercube
-- created : 2026-11-18T17:39:18.157206+00:00
-- url     : https://prove2.me/theorems/6d3438d5-0c06-494b-bfef-9647d0ddf1c0
-- title:
--   Complete signed graphs, partitions and disagreement costs
-- statement:
--   Finite vertices are labeled 0 through n−1. Upper-triangular signs give the complete graph and equal labels give the partition. The input encodes an accuracy index and the graph. The output records the partition by its equality matrix.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, STOC 2027 paper #79, §1 and §2, complete unweighted MinDisagree. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/79.pdf

import Mathlib
import Mathlib.Computability.TuringMachine.Computable

namespace DualSepClusterLP

/-- Only entries i < j are used. True denotes a positive unordered edge. -/
abbrev Graph (n : ℕ) := Fin n → Fin n → Bool

/-- Equal labels define the blocks of the partition. -/
abbrev Clustering (n : ℕ) := Fin n → Fin n

def disagreements {n : ℕ} (G : Graph n) (C : Clustering n) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i < j ∧ G i j ≠ decide (C i = C j) then 1 else 0

def matrixBits {n : ℕ} (entry : Fin n → Fin n → Bool) : List Bool :=
  (List.finRange n).flatMap fun i => (List.finRange n).map (entry i)

/-- The two self-delimiting unary fields give the accuracy index and size. -/
def graphInput {n : ℕ} (t : ℕ) (G : Graph n) : List Bool :=
  List.replicate t true ++ [false] ++ List.replicate n true ++ [false] ++
    matrixBits (fun i j => if i < j then G i j else false)

def partitionOutput {n : ℕ} (C : Clustering n) : List Bool :=
  matrixBits fun i j => decide (C i = C j)

end DualSepClusterLP


