-- Prove2me | Definitions.Def_TunnellMap_ComputableTargetRoster
-- name    : TunnellMap_ComputableTargetRoster
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T16:04:22.744586+00:00
-- url     : https://prove2.me/theorems/e77c58af-fb08-514d-9921-9055f787e08f
-- title:
--   Computable Target Roster
-- statement:
--   Definitions and structural lemmas for Computable Target Roster, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean

import Definitions.Def_TunnellMap_ComputableRoster
import Theorems.Thm_TunnellMap_directTargetUsed_iff
import Theorems.Thm_TunnellMap_tripleLexLtExec_iff
attribute [local simp] TunnellMap.tripleLexLtExec_iff


set_option autoImplicit true
namespace TunnellMap
instance aRepDecidableEq (n : ℤ) : DecidableEq (ARep n) :=
  inferInstanceAs (DecidableEq {p : Triple // aForm p = n})
instance aResidualDecidableEq (n : ℤ) : DecidableEq (AResidual n) :=
  inferInstanceAs (DecidableEq {p : ARep n // ¬ DirectTargetUsed p})
def wCandidates (r : ℤ) : List ℤ :=
  if r < 0 then []
  else if 32 * (isqrtK (r / 32) * isqrtK (r / 32)) = r then
    (if isqrtK (r / 32) = 0 then [0]
      else [-isqrtK (r / 32), isqrtK (r / 32)])
  else []
def targetTriples (n : ℤ) : List Triple :=
  (intRangeSym n).flatMap fun x =>
    (intRangeSym n).flatMap fun y =>
      (wCandidates (n - 2 * (x * x) - y * y)).map fun z => ⟨x, y, z⟩
def IsTargetRosterTriple (n : ℤ) (w : Triple) : Prop :=
  aForm w = n ∧ ¬ ImageUsedTriple w ∧ tripleLexLtExec w (negTriple w) = true
instance isTargetRosterTripleDecidable (n : ℤ) (w : Triple) :
    Decidable (IsTargetRosterTriple n w) := by
  unfold IsTargetRosterTriple
  infer_instance
def targetRosterUnsorted (n : ℤ) : List (AResidual n) :=
  (targetTriples n).filterMap fun w =>
    if h : IsTargetRosterTriple n w then
      some ⟨⟨w, h.1⟩, fun hc =>
        h.2.1 ((directTargetUsed_iff (⟨w, h.1⟩ : ARep n)).mp hc)⟩
    else none
def ALexLe {n : ℤ} (a b : AResidual n) : Prop :=
  (!tripleLexLtExec b.1.1 a.1.1) = true
instance aLexLeDecidable {n : ℤ} : DecidableRel (ALexLe (n := n)) :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))
theorem aLexLe_iff {n : ℤ} (a b : AResidual n) :
    ALexLe a b ↔ aResidualLexKey a ≤ aResidualLexKey b := by
  unfold ALexLe aResidualLexKey
  rw [Bool.not_eq_true', ← Bool.not_eq_true, tripleLexLtExec_iff, not_lt]
instance aLexLeTotal {n : ℤ} : Std.Total (ALexLe (n := n)) :=
  ⟨fun a b => by
    rcases le_total (aResidualLexKey a) (aResidualLexKey b) with h | h
    · exact Or.inl ((aLexLe_iff a b).mpr h)
    · exact Or.inr ((aLexLe_iff b a).mpr h)⟩
instance aLexLeTrans {n : ℤ} : IsTrans (AResidual n) ALexLe :=
  ⟨fun a b c hab hbc =>
    (aLexLe_iff a c).mpr (le_trans ((aLexLe_iff a b).mp hab) ((aLexLe_iff b c).mp hbc))⟩
def targetRosterExec (n : ℤ) : List (AResidual n) :=
  List.insertionSort ALexLe (targetRosterUnsorted n).dedup
end TunnellMap


