-- Prove2me | Definitions.Def_WeightedThreeSetPacking_Main_Repairs
-- name    : WeightedThreeSetPacking_Main_Repairs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:44.305946+00:00
-- url     : https://prove2.me/theorems/224e4fcc-fe29-49be-8bde-10923c256e58
-- title:
--   Compatible repair instance and scaled Berman search
-- statement:
--   Repairs are independent entering families of one to three sets with strictly positive original-weight gain. Their auxiliary ground sets are their unions, so compatible repairs have disjoint ground unions. Duplicate unions retain a maximum-gain representative with fixed computable code order for ties.
--
--   The auxiliary optimum is a maximum over finitely many feasible subfamilies, including the empty packing. The selected family comes from explicitly scaled squared-weight search with $\eta=1/11$, rather than an assumed approximation certificate. Integer floor scaling discards zero weights. Search stops at the first state without an improving exchange; its finite fuel bounds possible distinct states, rather than asserting a runtime theorem.
--
--   Both declared gain and actual gain are computed from their respective sums and simultaneous replacement. They are not defined to be equal.
-- source:
--   Tong and Xu, arXiv:2610.10036v1, Algorithm 1, p. 11; Lemmas 4.9–4.10, pp. 23–24; §4.3, pp. 25–26; https://arxiv.org/abs/2610.10036v1

import Definitions.Def_WeightedThreeSetPacking_Main_Analysis
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace WeightedThreeSetPacking.Main
noncomputable section
open Classical
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]

def gain (D : Analysis V) (X : Finset V) : ℝ := mass D X - mass D (neighbors D X D.A)

def repairCandidates (D : Analysis V) : Finset (Finset V) :=
  (Finset.univ \ D.A).powerset.filter fun X =>
    independent D X ∧ 1 ≤ X.card ∧ X.card ≤ 3 ∧ 0 < gain D X

def groundUnion (sets : V → Finset ℕ) (X : Finset V) : Finset ℕ :=
  X.biUnion sets

def auxiliaryFamily (D : Analysis V) (sets : V → Finset ℕ) : Finset (Finset ℕ) :=
  (repairCandidates D).image (groundUnion sets)

/-- Merging identical unions retains maximum declared gain. A fixed enumeration
breaks ties; no optimum or claw is used in this choice. -/
def representative (D : Analysis V) (sets : V → Finset ℕ) (U : Finset ℕ) : Finset V :=
  (((repairCandidates D).toList.filter fun X => groundUnion sets X = U).mergeSort
    (fun X Y => decide (Encodable.encode (X.image sets) ≤ Encodable.encode (Y.image sets)))).foldl
    (fun best X => if gain D best < gain D X then X else best) ∅

def auxiliaryWeight (D : Analysis V) (sets : V → Finset ℕ) (U : Finset ℕ) : ℝ :=
  gain D (representative D sets U)

/-- A maximum value of a finite auxiliary family. The empty packing is included;
no default supremum or attainment hypothesis is involved. -/
def auxiliaryOptimum (D : Analysis V) (sets : V → Finset ℕ) : ℝ :=
  ((auxiliaryFamily D sets).powerset.toList.filter fun P =>
    HyperMatchDelay.Batching.IsMatching (auxiliaryFamily D sets) P).foldl
      (fun best P => max best (HyperMatchDelay.Batching.weight (auxiliaryWeight D sets) P)) 0

/-- Structural, source-compatible set representation. Does not assert any
approximation, local optimality, or running-time guarantee. -/
def Represents (D : Analysis V) (sets : V → Finset ℕ) : Prop :=
  Function.Injective sets ∧ (∀ v, (sets v).Nonempty ∧ (sets v).card ≤ 3) ∧
  (∀ u v, D.graph.Adj u v ↔ u ≠ v ∧ ¬ Disjoint (sets u) (sets v))

/-- Generic squared local search for the auxiliary rank-nine instance.
The fuel is the number of subfamilies; strict improvements cannot revisit one.
The recursion stops immediately when no improving exchange exists. -/
def hyperWeight (w : Finset ℕ → ℝ) (P : Finset (Finset ℕ)) : ℝ :=
  HyperMatchDelay.Batching.weight w P

def hyperNeighbors (X P : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  P.filter fun F => F ∈ X ∨ ∃ H ∈ X, ¬ Disjoint F H

def hyperGreedy (E : Finset (Finset ℕ)) (w : Finset ℕ → ℝ) : Finset (Finset ℕ) :=
  (E.toList.mergeSort (fun F H => decide (w H < w F ∨
    (w H = w F ∧ Encodable.encode F ≤ Encodable.encode H)))).foldl
    HyperMatchDelay.Batching.greedyStep ∅

def hyperSearch (E : Finset (Finset ℕ)) (w : Finset ℕ → ℝ) :
    ℕ → Finset (Finset ℕ) → Finset (Finset ℕ)
  | 0, P => P
  | fuel+1, P =>
    let ordered := (E \ P).powerset.toList.mergeSort
      (fun X Y => decide (Encodable.encode X ≤ Encodable.encode Y))
    let next := ordered.find? (fun X => decide (
      X.card ≤ 9 ∧ HyperMatchDelay.Batching.IsMatching E X ∧
      hyperWeight (fun F => w F ^ 2) (hyperNeighbors X P) <
        hyperWeight (fun F => w F ^ 2) X))
    match next with
    | none => P
    | some X => hyperSearch E w fuel ((P \ hyperNeighbors X P) ∪ X)

/-- Standard Berman scaling with fixed eta=1/11: floor weights at scale
M/(eta*w(greedy)), delete zeros, then perform squared-weight claw search.
No approximation conclusion is assumed in this definition. -/
def scaledBerman (E : Finset (Finset ℕ)) (w : Finset ℕ → ℝ) : Finset (Finset ℕ) :=
  if E = ∅ then ∅ else
  let scale := (11 * E.card : ℝ) / hyperWeight w (hyperGreedy E w)
  let scaled := fun F => (⌊scale * w F⌋ : ℝ)
  let surviving := E.filter fun F => 0 < scaled F
  hyperSearch surviving scaled (2 ^ surviving.card) (hyperGreedy surviving scaled)

def selectedRepairs (D : Analysis V) (sets : V → Finset ℕ) : Finset (Finset V) :=
  (scaledBerman (auxiliaryFamily D sets) (auxiliaryWeight D sets)).image (representative D sets)

def repairedPacking (D : Analysis V) (sets : V → Finset ℕ) : Finset V :=
  (D.A \ (selectedRepairs D sets).biUnion (fun X => neighbors D X D.A)) ∪
    (selectedRepairs D sets).biUnion id

def declaredGain (D : Analysis V) (sets : V → Finset ℕ) : ℝ :=
  ∑ X ∈ selectedRepairs D sets, gain D X

def actualGain (D : Analysis V) (sets : V → Finset ℕ) : ℝ :=
  mass D (repairedPacking D sets) - mass D D.A

end
end WeightedThreeSetPacking.Main


