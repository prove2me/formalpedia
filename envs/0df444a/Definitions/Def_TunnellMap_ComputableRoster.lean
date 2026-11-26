-- Prove2me | Definitions.Def_TunnellMap_ComputableRoster
-- name    : TunnellMap_ComputableRoster
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T16:03:25.481473+00:00
-- url     : https://prove2.me/theorems/b60be9c4-b7ba-55f0-9bf1-c1746ff83c7a
-- title:
--   Computable Roster
-- statement:
--   Definitions and structural lemmas for Computable Roster, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Theorems.Thm_TunnellMap_tripleLexLtExec_iff
attribute [local simp] TunnellMap.tripleLexLtExec_iff


set_option autoImplicit true
namespace TunnellMap
def SourceUsedTriple (w : Triple) : Prop :=
  (8 : ℤ) ∣ (w.x + 2 * w.z + w.y) ∨ (8 : ℤ) ∣ (w.y - w.x + 2 * w.z) ∨ (4 : ℤ) ∣ w.x
instance sourceUsedTripleDecidable (w : Triple) : Decidable (SourceUsedTriple w) := by
  unfold SourceUsedTriple
  infer_instance
theorem directSourceUsed_iff {n : ℤ} (p : BOddRep n) :
    DirectSourceUsed p ↔ SourceUsedTriple p.1 := by
  unfold DirectSourceUsed SourceUsedTriple DirectPredicate1 DirectPredicate2
    DirectPredicate3
  exact Iff.rfl
def intRangeSym (m : ℤ) : List ℤ :=
  (List.range (2 * m.toNat + 1)).map (fun i : ℕ => (i : ℤ) - m)
def zCandidates (r : ℤ) : List ℤ :=
  if r < 0 then []
  else if 8 * (isqrtK (r / 8) * isqrtK (r / 8)) = r then
    (if isqrtK (r / 8) = 0 then [0]
      else [-isqrtK (r / 8), isqrtK (r / 8)])
  else []
def sourceTriples (n : ℤ) : List Triple :=
  (intRangeSym n).flatMap fun x =>
    (intRangeSym n).flatMap fun y =>
      (zCandidates (n - 2 * (x * x) - y * y)).map fun z => ⟨x, y, z⟩
def IsSourceRosterTriple (n : ℤ) (w : Triple) : Prop :=
  (bForm w = n ∧ Odd w.z) ∧ ¬ SourceUsedTriple w ∧
    tripleLexLtExec w (negTriple w) = true
instance isSourceRosterTripleDecidable (n : ℤ) (w : Triple) :
    Decidable (IsSourceRosterTriple n w) := by
  unfold IsSourceRosterTriple
  infer_instance
def sourceRosterUnsorted (n : ℤ) : List (BResidual n) :=
  (sourceTriples n).filterMap fun w =>
    if h : IsSourceRosterTriple n w then
      some ⟨⟨w, h.1⟩, fun hc =>
        h.2.1 ((directSourceUsed_iff (⟨w, h.1⟩ : BOddRep n)).mp hc)⟩
    else none
def BLexLe {n : ℤ} (a b : BResidual n) : Prop :=
  (!tripleLexLtExec b.1.1 a.1.1) = true
instance bLexLeDecidable {n : ℤ} : DecidableRel (BLexLe (n := n)) :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))
theorem bLexLe_iff {n : ℤ} (a b : BResidual n) :
    BLexLe a b ↔ bResidualLexKey a ≤ bResidualLexKey b := by
  unfold BLexLe bResidualLexKey
  rw [Bool.not_eq_true', ← Bool.not_eq_true, tripleLexLtExec_iff, not_lt]
instance bLexLeTotal {n : ℤ} : Std.Total (BLexLe (n := n)) :=
  ⟨fun a b => by
    rcases le_total (bResidualLexKey a) (bResidualLexKey b) with h | h
    · exact Or.inl ((bLexLe_iff a b).mpr h)
    · exact Or.inr ((bLexLe_iff b a).mpr h)⟩
instance bLexLeTrans {n : ℤ} : IsTrans (BResidual n) BLexLe :=
  ⟨fun a b c hab hbc =>
    (bLexLe_iff a c).mpr (le_trans ((bLexLe_iff a b).mp hab) ((bLexLe_iff b c).mp hbc))⟩
def sourceRosterExec (n : ℤ) : List (BResidual n) :=
  List.insertionSort BLexLe (sourceRosterUnsorted n).dedup
section Structural
variable {n : ℤ} [Fintype (BOddRep n)]
open RecordDA
end Structural
end TunnellMap


