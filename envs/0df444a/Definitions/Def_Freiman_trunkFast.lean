-- Prove2me | Definitions.Def_Freiman_trunkFast
-- name    : Freiman_trunkFast
-- status  : Definition
-- author  : @wamlart
-- created : 2026-09-12T09:53:55.833802+00:00
-- url     : https://prove2.me/theorems/a05abfe4-ccdc-4b3a-907e-d2dff425f4d4
-- title:
--   Fast lookup and certificate predicates for Freiman’s trunk catalog
-- statement:
--   This module supplies a reusable executable interface for the existing Freiman trunk certificate catalog. Array-chain lookup reads individual witnesses and bounds directly from their original chunks. The finite leaf, tree and group predicates retain the original threshold, rectangle, polarity and branch requirements while using this lookup and a raw parent enumeration. The separate correctness theorem justifies passage to the original group predicate when the raw parent enumeration agrees with the catalog’s deduplicated parents. The module contains definitions and essential decidability instances; it introduces no new mathematical assumptions.
-- source:
--   Freiman Hall ray report, Section 15, trunk certificate and Proposition 4.1. The symbolic array-chain lookup and mirror-predicate proof architecture are adapted with attribution from Marac’s accepted public submission https://prove2.me/submissions/93a6c511-3ed0-48c3-bbd0-ecae49532be4; this reusable interface generalizes the group correspondence from a single state to every state under an explicit raw-parent equality hypothesis.

-- Reusable checking infrastructure for the existing Freiman trunk certificate catalog.
-- Generic array-chain and certificate soundness proofs are adapted with attribution from
-- Marac's accepted public submission 93a6c511-3ed0-48c3-bbd0-ecae49532be4.
import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases

open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Freiman.TrunkFast

def chainGet? {α : Type} : List (Array α) → ℕ → Option α
  | [], _ => none
  | A::As, j => if j < A.size then A[j]? else chainGet? As (j - A.size)

def fastWitness? (n : ℕ) : Option TrunkWitness :=
  if n-1 < trunkWitnessData01.size then trunkWitnessData01[n-1]?
  else chainGet? [trunkWitnessData02,trunkWitnessData03,trunkWitnessData04,trunkWitnessData05,trunkWitnessData06,
       trunkWitnessData07,trunkWitnessData08,trunkWitnessData09,trunkWitnessData10,trunkWitnessData11,
       trunkWitnessData12,trunkWitnessData13,trunkWitnessData14,trunkWitnessData15,trunkWitnessData16,
       trunkWitnessData17,trunkWitnessData18,trunkWitnessData19,trunkWitnessData20,trunkWitnessData21,
       trunkWitnessData22,trunkWitnessData23,trunkWitnessData24,trunkWitnessData25,trunkWitnessData26,
       trunkWitnessData27,trunkWitnessData28,trunkWitnessData29,trunkWitnessData30,trunkWitnessData31,
       trunkWitnessData32,trunkWitnessData33,trunkWitnessData34,trunkWitnessData35] (n-1-trunkWitnessData01.size)

def fastWitness (n : ℕ) : TrunkWitness := (fastWitness? n).getD ⟨0,0,⟨0,1,0,1⟩,0,0⟩

def fastBound? (n : ℕ) : Option CertBound :=
  if n-1 < trunkBoundData01.size then trunkBoundData01[n-1]?
  else chainGet? [trunkBoundData02,trunkBoundData03,trunkBoundData04] (n-1-trunkBoundData01.size)

def fastBound (n : ℕ) : CertBound := (fastBound? n).getD lowerHistoryZero

def trunkUseBoundsFast (w : TrunkWitness) (l u : CertBound) : Prop :=
  l.lower = true ∧ u.lower = false ∧
  l.threshold = (fastBound w.lowerId).threshold ∧
  u.threshold = (fastBound w.upperId).threshold ∧
  ((w.diagonal = 0 ∧ 0 < w.margin) ∨ l.strict = true ∨ u.strict = true)

def trunkLeafBoundFast (R : CertRectangle) (bs : List CertBound) (id : ℕ) (sign : ℤ) : Prop :=
  0 < id ∧ id ≤ 8656 ∧
  (fastWitness id).diagonal = sign ∧
  section14RectangleContains (fastWitness id).rectangle R ∧
  ∃ l ∈ bs, ∃ u ∈ bs, trunkUseBoundsFast (fastWitness id) l u

def trunkTreeBoundFast (R : CertRectangle) (bs : List CertBound) : TrunkTree → Prop
  | .pair id => trunkLeafBoundFast R bs id 0
  | .split axis left right =>
    trunkTreeBoundFast (trunkRectangleHalf R axis false) bs left ∧
    trunkTreeBoundFast (trunkRectangleHalf R axis true) bs right
  | .diagonal negative positive => trunkLeafBoundFast R bs negative (-1) ∧ trunkLeafBoundFast R bs positive 1
  | .boundary => trunkBoundaryBound R bs

instance decTrunkTreeBoundFast (R : CertRectangle) (bs : List CertBound) :
    ∀ t : TrunkTree, Decidable (trunkTreeBoundFast R bs t)
  | .pair id => by unfold trunkTreeBoundFast trunkLeafBoundFast trunkUseBoundsFast section14RectangleContains; infer_instance
  | .split axis left right => by
      unfold trunkTreeBoundFast
      have := decTrunkTreeBoundFast (trunkRectangleHalf R axis false) bs left
      have := decTrunkTreeBoundFast (trunkRectangleHalf R axis true) bs right
      infer_instance
  | .diagonal negative positive => by
      unfold trunkTreeBoundFast trunkLeafBoundFast trunkUseBoundsFast section14RectangleContains
      infer_instance
  | .boundary => by unfold trunkTreeBoundFast trunkBoundaryBound certThresholdDataValid; infer_instance

def trunkRawParents (C : LowerHistoryContext) : List (List CertBound) :=
  let a := trunkBranches C ⟨([2],[]),true,([1],[]),false,false,[]⟩
  let b := trunkBranches C ⟨([1],[]),true,([2],[]),false,false,[]⟩
  a.flatMap fun (ca,ga) => b.filterMap fun (cb,gb) =>
    let base := ca++cb++[lowerHistoryHN,lowerHistoryZero]
    match ga,gb with
    | .impossible,_ | _,.impossible => none
    | .automatic,.automatic => some base
    | .bound g,.automatic | .automatic,.bound g => some (g::base)
    | .bound g,.bound h => some (g::h::base)

def trunkResidualFast (S : TrunkState) (plan parent goal : ℕ) (branch : ℤ) : List CertBound :=
  let b := trunkBranch S plan goal branch
  (trunkPlanAt S plan).cuts ++ (trunkRawParents S.context)[parent]?.getD [] ++ b.1 ++
    match b.2 with | .bound a => [lowerHistoryComplement a] | _ => []

def trunkGroupValidFast (k : Fin 16) (g : TrunkGroup) : Prop :=
  let S := trunkCatalog.states k
  g.plan < (trunkSourcePlans S.context).length ∧ g.goal ≤ (trunkSpecs (trunkPlanAt S g.plan)).length ∧
  (∀ p ∈ g.parents, p < (trunkRawParents S.context).length) ∧
  ∀ bt ∈ g.branches,
    ((g.goal = 0 ∧ bt.1 = -1) ∨ (0 < g.goal ∧ 0 ≤ bt.1 ∧ bt.1.toNat < (trunkGoalBranches S g.plan g.goal).length)) ∧
    (trunkBranch S g.plan g.goal bt.1).2 ≠ LowerHistoryComparison.automatic ∧
    ∀ p ∈ g.parents, trunkTreeBoundFast S.rectangle (trunkResidualFast S g.plan p g.goal bt.1) bt.2

end Freiman.TrunkFast


