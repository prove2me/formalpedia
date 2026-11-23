-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FormalPointSubstitutionSeriesValueAtTwoPoints
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FormalPointSubstitutionSeriesValueAtTwoPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:09.386489+00:00
-- url     : https://prove2.me/theorems/b5fa8b26-9ef7-4cf8-ae32-039a801975ae
-- title:
--   Formal Point Substitution Series Value At Two Points
-- statement:
--   Definitions and structural lemmas for Formal Point Substitution Series Value At Two Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_evHom_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
namespace GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable (k d) in

def Q (n : ℕ) : AddSubgroup (Pt k n d) where
  carrier := {p | ∀ i, constantCoeff (p i) = 0}
  add_mem' := fun ha hb i => by rw [Pi.add_apply, map_add, ha i, hb i, add_zero]
  zero_mem' := fun _ => map_zero _
  neg_mem' := fun ha i => by rw [Pi.neg_apply, map_neg, ha i, neg_zero]
variable {n l : ℕ}
def gen (j : Fin n) : Q k d n := ⟨pt k d j, CZ.pt j⟩
theorem czQ (b : Fin n → Q k d l) : CZ (fun j => (b j).1) := by
  intro j i
  exact (b j).2 i
def sb (b : Fin n → Q k d l) : PS k n d →+* PS k l d := evHom (czQ b)
theorem sb_apply (b : Fin n → Q k d l) (f : PS k n d) : sb b f = ev (fun j => (b j).1) f := by
  unfold sb
  exact evHom_apply (czQ b) f
def sq (b : Fin n → Q k d l) : Q k d n →+ Q k d l where
  toFun p := ⟨fun i => sb b (p.1 i), fun i =>
    (congrArg constantCoeff (sb_apply b _)).trans (constantCoeff_ev (czQ b) (p.2 i))⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)
def E2 (f : PS k 2 d) (u v : Q k d n) : PS k n d := sb ![u, v] f
def E3 (f : PS k 3 d) (u v w : Q k d n) : PS k n d := sb ![u, v, w] f
def ac (A : Q k d 1) (u : Q k d n) : Q k d n := sq ![u] A
def op (F : Q k d 2) (u v : Q k d n) : Q k d n := sq ![u, v] F
end GlobalTheory.FrameBiextId


