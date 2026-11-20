-- Prove2me | Definitions.Def_DualSepClusterLP_DenseTrials
-- name    : DualSepClusterLP_DenseTrials
-- status  : Definition
-- author  : @hypercube
-- created : 2026-11-19T14:50:20.034244+00:00
-- url     : https://prove2.me/theorems/6958bb46-6493-4bae-b9fa-dd19d7f37242
-- title:
--   Affine-sampling greedy trials for dense quadratic minimization
-- statement:
--   The quadratic objective sums arbitrary rational vertex costs and one pair coefficient for every earlier–later pair of retained vertices. A trial uses an affine map modulo p and a bit vector to estimate the interaction with later retained vertices, then scans the vertices in order and makes greedy decisions. A direct bit mask handles short lists.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, Lemma 5.3 (Section 5.2) and Appendix B, https://arxiv.org/abs/2607.27829. This proof gives an alternative implementation using pairwise independent affine samples and greedy completion.

import Mathlib

namespace DualSepClusterLP.Dense
variable {ι : Type} (A : ι → ι → ℚ)

def row (i : ι) (Y : List ι) : ℚ := (Y.map (A i)).sum

def value (b : ι → ℚ) : List ι → ℚ
  | [] => 0
  | i::Y => b i + row A i Y + value b Y

def greedy (est : ι → ℚ) : (xs : List ι) → (ι → ℚ) → List ι
  | [], _ => []
  | i::xs, b => if b i+est i≤0 then i::greedy est xs (fun j => b j+A i j)
    else greedy est xs b

section
variable [DecidableEq ι]

def small (U : List ι) (bits : List Bool) := U.filter (fun i => bits[U.idxOf i]?.getD false)

def rawEstimate (A : ι → ι → ℚ) (U : List ι) (k p a d : ℕ) (bits : List Bool) (i : ι) : ℚ :=
  (p:ℚ)/k * ((List.range k).map (fun l =>
    let z := (a*l+d)%p
    if U.idxOf i < z ∧ bits[l]?.getD false then U[z]?.elim 0 (A i) else 0)).sum

end
end DualSepClusterLP.Dense


