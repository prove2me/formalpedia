-- Prove2me | Definitions.Def_DualSepClusterLP_CutSearch
-- name    : DualSepClusterLP_CutSearch
-- status  : Definition
-- author  : @hypercube
-- created : 2026-11-19T14:06:20.567125+00:00
-- url     : https://prove2.me/theorems/37cb03d0-9f99-4bf7-80d6-b5e1fddc90e3
-- title:
--   Projected cut search for the cluster LP
-- statement:
--   At each target dual objective, ask the approximate separator for a violated column and update the prices while keeping their sum fixed. A full list of cuts gives rational primal weights, with singletons filling the remaining deficits. Grid search pairs that primal with the last accepted dual vector. An exact support reduction is used when the inverse accuracy is at least the number of vertices.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, Theorem 2.1 and Corollary 2.4, https://arxiv.org/abs/2607.27829. The projected updates below give an alternative proof of the oracle-to-LP reduction.

import Definitions.Def_DualSepClusterLP_SparseInput


namespace DualSepClusterLP.CutRecovery
def visits {n : ℕ} (Cs : List (Finset (Fin n))) (i : Fin n) : ℚ :=
  (Cs.map (fun S => if i ∈ S then 1 else 0)).sum
def mean {n : ℕ} (Cs : List (Finset (Fin n))) : ℚ := (∑ i, visits Cs i) / n
end DualSepClusterLP.CutRecovery

namespace DualSepClusterLP.CutRecovery
def peak {n : ℕ} (Cs : List (Finset (Fin n))) : ℚ :=
  ((List.finRange n).map (visits Cs)).foldr max 0
def raw {n : ℕ} (Cs : List (Finset (Fin n))) : SparseWeights n :=
  Cs.map (fun S => (S,(1:ℚ)/peak Cs)) ++
    (List.finRange n).map (fun i => ({i}, (peak Cs-visits Cs i)/peak Cs))
def clean {n : ℕ} (L : SparseWeights n) : SparseWeights n :=
  (((L.map Prod.fst).dedup).filter (fun S => 0<weightAt L S)).map (fun S => (S,weightAt L S))
def make {n : ℕ} (Cs : List (Finset (Fin n))) : SparseWeights n := clean (raw Cs)
end DualSepClusterLP.CutRecovery

namespace DualSepClusterLP.Master
open Finset
def adj {n : ℕ} (G : Graph n) (i j : Fin n) : Prop := i=j ∨ G (min i j) (max i j) = true
instance {n : ℕ} (G : Graph n) (i j : Fin n) : Decidable (adj G i j) := by unfold adj; infer_instance
def EquivalenceGraph {n : ℕ} (G : Graph n) : Prop :=
  ∀ i j k, adj G i j → adj G j k → adj G i k
def block {n : ℕ} (G : Graph n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (adj G i)
end DualSepClusterLP.Master

namespace DualSepClusterLP.Master
open Finset
def blockList {n : ℕ} (G : Graph n) := ((List.finRange n).map (block G)).dedup
def zeroList {n : ℕ} (G : Graph n) : SparseWeights n :=
  (blockList G).map (fun S => (S,(1:ℚ)))
instance decEqGraph {n : ℕ} (G : Graph n) : Decidable (EquivalenceGraph G) := by
  unfold EquivalenceGraph; infer_instance
end DualSepClusterLP.Master
namespace DualSepClusterLP.CutRecovery
open Finset
end DualSepClusterLP.CutRecovery

namespace DualSepClusterLP.Compression
def active {N : ℕ} (w : Fin N → ℚ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => 0 < w i)
def moment {N d : ℕ} (A : Fin d → Fin N → ℕ) (w : Fin N → ℚ) (r : Fin d) : ℚ :=
  ∑ i, w i * A r i
def addDir {N k : ℕ} (idx : Fin k → Fin N) (v : Fin k → ℚ) (i : Fin N) : ℚ :=
  ∑ j, if idx j=i then v j else 0
abbrev digits {d : ℕ} (D : ℕ) := ((d+1)*D+1)^d + 1
def difference {d B : ℕ} (s t : Fin (d+1) → Fin B) (j : Fin (d+1)) : ℚ :=
  (s j).val - (t j).val
def changed {d N B : ℕ} (w : Fin N → ℚ) (idx : Fin (d+1) → Fin N)
    (s t : Fin (d+1) → Fin B) (j : Fin (d+1)) (i : Fin N) : ℚ :=
  w i - w (idx j) / difference s t j * addDir idx (difference s t) i
def improves {N d : ℕ} (A : Fin d → Fin N → ℕ) (w z : Fin N → ℚ) : Prop :=
  (∀ i, 0 ≤ z i) ∧ (active z).card < (active w).card ∧ ∀ r, moment A z r = moment A w r
instance {N d : ℕ} (A : Fin d → Fin N → ℕ) (w z : Fin N → ℚ) : Decidable (improves A w z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def tuples (k m : ℕ) : List (Fin k → Fin m) :=
  (List.finRange (m^k)).map finFunctionFinEquiv.symm
def candidates {d N : ℕ} (D : ℕ) (w : Fin N → ℚ) : List (Fin N → ℚ) :=
  let digitsList := tuples (d+1) (digits (d:=d) D)
  (tuples (d+1) N).flatMap fun idx => digitsList.flatMap fun s =>
    digitsList.flatMap fun t => (List.finRange (d+1)).map (fun j => changed w idx s t j)
def compressStep {d N : ℕ} (A : Fin d → Fin N → ℕ) (D : ℕ) (w : Fin N → ℚ) : Fin N → ℚ :=
  if (active w).card ≤ d then w else
    ((candidates (d:=d) D w).find? (fun z => decide (improves A w z))).getD w
def run {d N : ℕ} (A : Fin d → Fin N → ℕ) (D : ℕ) : ℕ → (Fin N → ℚ) → (Fin N → ℚ)
  | 0, w => w
  | k+1, w => run A D k (compressStep A D w)
end DualSepClusterLP.Compression

namespace DualSepClusterLP.Compression
def twiceEntry {n : ℕ} (G : Graph n) (S : Finset (Fin n)) (i j : Fin n) : ℕ :=
  if i < j then if G i j then (if decide (i∈S) != decide (j∈S) then 1 else 0)
    else (if i∈S ∧ j∈S then 2 else 0)
  else 0
def twiceCost {n : ℕ} (G : Graph n) (S : Finset (Fin n)) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, twiceEntry G S i j
def column {n : ℕ} (G : Graph n) (S : Finset (Fin n)) : Fin (n+1) → ℕ :=
  Fin.cases (twiceCost G S) (fun i => if i ∈ S then 1 else 0)
def coeff {n : ℕ} (G : Graph n) (L : SparseWeights n) (r : Fin (n+1)) (i : Fin L.length) : ℕ :=
  column G (L.get i).1 r
def indexWeights {n : ℕ} (L : SparseWeights n) (i : Fin L.length) : ℚ := (L.get i).2
def rawList {n : ℕ} (L : SparseWeights n) (w : Fin L.length → ℚ) : SparseWeights n :=
  (List.finRange L.length).map (fun i => ((L.get i).1,w i))
def emit {n : ℕ} (L : SparseWeights n) (w : Fin L.length → ℚ) : SparseWeights n :=
  ((List.finRange L.length).filter (fun i => decide (0<w i))).map (fun i => ((L.get i).1,w i))
def compress {n : ℕ} (G : Graph n) (L : SparseWeights n) : SparseWeights n :=
  emit L (run (coeff G L) (2*n*n+1) L.length (indexWeights L))
end DualSepClusterLP.Compression

namespace DualSepClusterLP.CutRecovery
abbrev Prices (n : ℕ) := Fin n → ℚ
abbrev Oracle (n : ℕ) := Prices n → Option (Finset (Fin n))
def scaleIndex (t : ℕ) := 8*(t+1)
def tolerance (t : ℕ) : ℚ := 1/(scaleIndex t : ℚ)
def rate (t n : ℕ) : ℚ := 1/((scaleIndex t : ℚ)*(n+1)^2)
def cutLimit (t n : ℕ) := 4*(scaleIndex t)^2*(n+1)^7
def levels (t n : ℕ) := 2*(scaleIndex t)*(n+1)^2
def levelValue (t j : ℕ) : ℚ := j * tolerance t
def prices {n : ℕ} (V η : ℚ) (Cs : List (Finset (Fin n))) (i : Fin n) : ℚ :=
  V / n - η * (visits Cs i - mean Cs)
def search {n : ℕ} (oracle : Oracle n) (V η : ℚ) :
    ℕ → List (Finset (Fin n)) → Prices n ⊕ List (Finset (Fin n))
  | 0, Cs => .inr Cs
  | f+1, Cs =>
    let q := prices V η Cs
    match oracle q with
    | none => .inl q
    | some S => search oracle V η f (S::Cs)
def grid {n : ℕ} (t : ℕ) (oracle : Oracle n) :
    ℕ → Prices n ⊕ (SparseWeights n × Prices n)
  | 0 => .inl (fun _ => 0)
  | j+1 =>
    match grid t oracle j with
    | .inr answer => .inr answer
    | .inl lower =>
      match search oracle (levelValue t (j+1)) (rate t n) (cutLimit t n) [] with
      | .inl q => .inl (fun i => q i / (1+tolerance t))
      | .inr Cs => .inr (make Cs,lower)
def goodOracle {n : ℕ} (t : ℕ) (G : Graph n) (oracle : Oracle n) : Prop :=
  ∀ q, match oracle q with
    | some S => subsetCost G S < ∑ i∈S, (q i : ℝ)
    | none => DualFeasible G (fun i => (q i : ℝ) / (1+(tolerance t : ℝ)))
end DualSepClusterLP.CutRecovery

namespace DualSepClusterLP.CutRecovery
def untrimmed {n : ℕ} (G : Graph n) (t : ℕ) (o : Oracle n) : SparseWeights n × Prices n :=
  if Master.EquivalenceGraph G then (Master.zeroList G,fun _ => 0)
  else match grid t o (levels t n) with
    | .inr ans => ans
    | .inl q => ([],q)
def solve {n : ℕ} (G : Graph n) (t : ℕ) (o : Oracle n) : SparseWeights n × Prices n :=
  let (L,q) := untrimmed G t o
  (if n≤t then Compression.compress G L else L,q)
end DualSepClusterLP.CutRecovery

namespace DualSepClusterLP.CutRecovery

abbrev OracleFamily := (u n : ℕ) → Graph n → Oracle n

def oracleRuns (O : OracleFamily) (M : Turing.TM2ComputableAux Bool Bool) (A a b : ℕ) : Prop :=
  ∀ (u n : ℕ) (G : Graph n) (q : Prices n),
    Nonempty (Turing.TM2OutputsInTime M.tm ((separationInput u G q).map M.inputAlphabet.symm)
      (some ((separationOutput (O u n G q)).map M.outputAlphabet.symm))
      (2^(A*(u+1)^a)*(n+(pricesBits q).length+1)^b))


end DualSepClusterLP.CutRecovery


