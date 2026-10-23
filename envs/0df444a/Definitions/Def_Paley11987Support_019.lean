-- Prove2me | Definitions.Def_Paley11987Support_019
-- name    : Paley11987Support_019
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T01:01:41.027347+00:00
-- url     : https://prove2.me/theorems/c2d750d7-9f55-4de1-a5bc-b45ac423d60e
-- title:
--   Nested Boolean families and tolerant rows
-- statement:
--   Defines nested Boolean families, the joint sensitivity functional counting coordinates sensitive for both functions, tournaments, recursive child inputs, tolerant target and guard sets, tolerant rows and tolerant families. Structural identities connect flips of parent and child coordinates.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module BooleanTransferFoundation.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module BooleanTransferFoundation, SHA256 d873df15ddf34254fda57ae3742d6727e5a14f23f0375f927f7cf1b57b20b6c9

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Paley11987Support_000
import Definitions.Def_Paley11987Support_001
import Definitions.Def_Paley11987Support_002
import Definitions.Def_Paley11987Support_003
import Definitions.Def_Paley11987Support_004
import Definitions.Def_Paley11987Support_005
import Definitions.Def_Paley11987Support_006
import Definitions.Def_Paley11987Support_007
import Definitions.Def_Paley11987Support_008
import Definitions.Def_Paley11987Support_009
import Definitions.Def_Paley11987Support_010
import Definitions.Def_Paley11987Support_011
import Definitions.Def_Paley11987Support_012
import Definitions.Def_Paley11987Support_013
import Definitions.Def_Paley11987Support_014
import Definitions.Def_Paley11987Support_015
import Definitions.Def_Paley11987Support_016
import Definitions.Def_Paley11987Support_017
import Definitions.Def_Paley11987Support_018

set_option autoImplicit false
set_option Elab.async false
section z29

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
noncomputable section
open scoped Classical BigOperators
namespace OAI.Paper320

structure NestedFamily {h : ℕ} {I : Type}
    (F : Fin h → (I → Bool) → Bool) : Prop where
  accepts_of_le : ∀ {q q' : Fin h} {x}, q ≤ q' → F q' x = true → F q x = true



def jointSensitivityAt {I : Type} [Fintype I]
    (f g : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i =>
    f (flip x {i}) ≠ f x ∧ g (flip x {i}) ≠ g x).card

theorem flip_prod_same {I J : Type} (x : J × I → Bool) (j : J) (i : I) :
    (fun a => flip x {(j, i)} (j, a)) = flip (fun a => x (j, a)) {i} := by
  funext a
  simp [flip]

theorem flip_prod_other {I J : Type} (x : J × I → Bool) {j k : J} (i : I) (hk : k ≠ j) :
    (fun a => flip x {(j, i)} (k, a)) = fun a => x (k, a) := by
  funext a
  simp [flip, hk]

structure Tournament (k : ℕ) extends Digraph (Fin k) where
  loopless : ∀ i, ¬ Adj i i
  edge_compl : ∀ {i j}, i ≠ j → (Adj i j ↔ ¬ Adj j i)

namespace Tournament
variable {k : ℕ} (T : Tournament k)

theorem ne_of_adj {i j : Fin k} (h : T.Adj i j) : i ≠ j := by
  rintro rfl
  exact T.loopless i h







end Tournament

def recursiveChild {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) : I → Bool :=
  fun a => x ((j, c), a)

theorem recursiveChild_flip_same {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) (a : I) :
    recursiveChild (flip x {((j, c), a)}) j c = flip (recursiveChild x j c) {a} :=
  flip_prod_same x (j, c) a

theorem recursiveChild_flip_other {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j j' : Fin k) (c c' : Fin r) (a : I)
    (h : (j', c') ≠ (j, c)) :
    recursiveChild (flip x {((j, c), a)}) j' c' = recursiveChild x j' c' :=
  flip_prod_other x a h

def childLift {J I : Type} (j : J) (A : Finset I) : Finset (J × I) :=
  A.map ⟨fun a => (j, a), fun _ _ h => congrArg (fun p : J × I => p.2) h⟩





def childJointChanges {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q q' : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    Finset ((Fin k × Fin r) × I) :=
  childLift (j, c) (Finset.univ.filter fun a =>
    F q (flip (recursiveChild x j c) {a}) ≠ F q (recursiveChild x j c) ∧
    F q' (flip (recursiveChild x j c) {a}) ≠ F q' (recursiveChild x j c))





end OAI.Paper320
namespace Sensitivity205
open OAI.Paper320

def PairBound {n : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (b : Bool) (V : Fin n → Fin n → ℕ) : Prop :=
  ∀ (q q' : Fin n), q ≤ q' → ∀ x, F q x = b → F q' x = b →
    jointSensitivityAt (F q) (F q') x ≤ V q q'





end Sensitivity205
namespace Sensitivity2075
open OAI.Paper320 Sensitivity205

def missingTargets {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Finset (Fin r) :=
  Finset.univ.filter fun c => F A (recursiveChild x i c) = false

def failedGuards {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Finset (Fin k) :=
  Finset.univ.filter fun j => T.Adj i j ∧ F G (recursiveChild x j (label i j)) = true

def tolerantRow {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Bool :=
  decide ((∀ c, F A (recursiveChild x i c) = true) ∧
    (failedGuards T label F G x i).card ≤ q)

def tolerantFamily {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) : Bool :=
  decide (∃ i, tolerantRow T label F A G q x i = true)

def tolerantTargets {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => (missingTargets F A x i).card = 1 ∧
    (failedGuards T label F G x i).card ≤ q

def tolerantGuards {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => missingTargets F A x i = ∅ ∧
    (failedGuards T label F G x i).card = q+1







theorem tolerantRow_true {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    tolerantRow T label F A G q x i = true ↔
      (∀ c, F A (recursiveChild x i c) = true) ∧
      (failedGuards T label F G x i).card ≤ q := by
  simp only [tolerantRow, decide_eq_true_eq]

theorem tolerantFamily_true {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) :
    tolerantFamily T label F A G q x = true ↔
      ∃ i, tolerantRow T label F A G q x i = true := by
  simp only [tolerantFamily, decide_eq_true_eq]

theorem tolerantFamily_false {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) :
    tolerantFamily T label F A G q x = false ↔
      ∀ i, tolerantRow T label F A G q x i = false := by
  simp [tolerantFamily]

section Flips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

















end Flips

section RowFlips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)





end RowFlips

section Nesting
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F)





end Nesting

def missingWitness {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k) : Fin r :=
  if h : (missingTargets F A x i).Nonempty then h.choose else ⟨0, hr⟩









section JointCandidates








end JointCandidates





end Sensitivity2075
end
end z29


