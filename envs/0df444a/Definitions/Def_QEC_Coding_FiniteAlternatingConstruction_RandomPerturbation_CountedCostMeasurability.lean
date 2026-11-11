-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T23:04:39.549324+00:00
-- url     : https://prove2.me/theorems/93205c2e-b058-41d4-ab18-b10086cc2672
-- title:
--   Counted Cost Measurability
-- statement:
--   Definitions and structural lemmas for Counted Cost Measurability, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
def countedMasterKeyQuery (P : TannerSquarePresentation) (e : MasterEvent P) : List ℕ × ℕ :=
  let raw := mapQuery (fun t => indexQuery t (triangleInputList P)) e.val.toList
  let sorted := sortQuery (fun a b : ℕ => (decide (a ≤ b), 1)) raw.1
  (sorted.1, raw.2 + sorted.2)
def countedMasterCompareQuery (P : TannerSquarePresentation)
    (e f : MasterEvent P) : Bool × ℕ :=
  let E := countedMasterKeyQuery P e
  let F := countedMasterKeyQuery P f
  let q := lexLEQuery E.1 F.1
  (q.1, E.2 + F.2 + q.2)
def countedMasterEqQuery (P : TannerSquarePresentation) (e f : MasterEvent P) : Bool × ℕ :=
  let forward := countedMasterCompareQuery P e f
  let backward := countedMasterCompareQuery P f e
  (forward.1 && backward.1, forward.2 + backward.2 + 1)
local instance countedLabelListMeasurable (A : Type*) [Countable A] :
    MeasurableSpace (List A) := ⊤
local instance countedLabelListSingleton (A : Type*) [Countable A] :
    MeasurableSingletonClass (List A) := ⟨fun _ => trivial⟩
def countedMasterCandidateQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (L : List (Triangle P)) : Option (MasterEvent P) × ℕ :=
  let q := eligibleListQuery P J r L
  if hc : L.toFinset.card = 4 then
    (if q.1.2 then some ⟨L.toFinset, hc⟩ else none, q.2 + 1)
  else (none, q.2 + 1)
def countedMasterRawUniverseQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) : List (MasterEvent P) × ℕ :=
  let tuples := fourTuplesQuery (triangleInputList P)
  let events := filterMapQuery (countedMasterCandidateQuery P J r) tuples.1
  (events.1, tuples.2 + events.2)
def countedMasterUniverseQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) : List (MasterEvent P) × ℕ :=
  let raw := countedMasterRawUniverseQuery P J r
  let unique := dedupQuery (countedMasterEqQuery P) raw.1
  let sorted := sortQuery (countedMasterCompareQuery P) unique.1
  (sorted.1, raw.2 + unique.2 + sorted.2)
def countedMasterAnchorQuery (P : TannerSquarePresentation)
    (e : MasterEvent P) : Option (Triangle P) × ℕ :=
  match e.val.toList with
  | [] => (none, 1)
  | a :: L => let q := anchorFoldQuery P a L; (some q.1, q.2 + 1)
def countedMasterStateEventQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (K : ℕ) (e : MasterEvent P) (R : StateRows P) : Bool × ℕ :=
  let net := gridListQuery K
  let anchor := countedMasterAnchorQuery P e
  let query := listAnyQuery (fun g : Grid K =>
    let center := fullCenterQuery P J lambda K anchor.1 g
    let triangles := listAllQuery (fun a : e.val =>
      stateTriangleQuery P J lambda a.val R center.1) (Finset.univ.toList : List e.val)
    (triangles.1, center.2 + triangles.2 + 8)) net.1
  (query.1, net.2 + anchor.2 + query.2 + 1)
def countedMasterSupportQuery (P : TannerSquarePresentation)
    (e : MasterEvent P) : List (Vertex P) × ℕ := by
  classical
  let raw := flatMapQuery (fun t : Triangle P =>
    ([triangleVertex P t 0, triangleVertex P t 1, triangleVertex P t 2], 6)) e.val.toList
  let unique := dedupQuery (fun v w : Vertex P => (decide (v = w), 1)) raw.1
  exact (unique.1, raw.2 + unique.2)
def countedMasterRefreshCost (P : TannerSquarePresentation) (e : MasterEvent P) : ℕ :=
  let support := countedMasterSupportQuery P e
  support.2 + (mapQuery (fun v : Vertex P =>
    ((), (memberQuery (fun v w : Vertex P => (decide (v = w), 1)) v support.1).2 + 6))
    (vertexInputList P)).2
end QEC.Coding.BDL26RandomPerturbation


