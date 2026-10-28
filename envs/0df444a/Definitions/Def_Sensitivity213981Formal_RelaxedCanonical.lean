-- Prove2me | Definitions.Def_Sensitivity213981Formal_RelaxedCanonical
-- name    : Sensitivity213981Formal_RelaxedCanonical
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:07:51.938989+00:00
-- url     : https://prove2.me/theorems/7ea8a063-947e-4368-8bab-aa9107044e1b
-- title:
--   Relaxed Canonical — sensitivity certificate definitions
-- statement:
--   The definitions for Relaxed Canonical in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRelaxedCanonical.canonical`, `ThreeBoundRelaxedCanonical.orderKey_injective`, `ThreeBoundRelaxedCanonical.ofOrientation`, `ThreeBoundRelaxedCanonical.key`, `ThreeBoundRelaxedCanonical.key_injective`, `ThreeBoundRelaxedCanonical.stateOrder`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedCanonical.lean, lines 1–130.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q3RecordFields
import Definitions.Def_Sensitivity213981Formal_RelaxedStateSearch
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Canonical sorting preserves every coordinate of the relaxed q3 record. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRelaxedCanonical
open ThreeBoundQ3 ThreeBoundRelaxed

theorem orderKey_injective : Function.Injective orderKey := by
  intro a b h
  apply Fin.ext
  unfold orderKey at h
  have ha := a.isLt
  have hb := b.isLt
  omega

def key (s : State) : ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (orderKey s.kind,toLex (s.out,s.incoming))

theorem key_injective : Function.Injective key := by
  intro a b h
  have hk : a.kind=b.kind := orderKey_injective (congrArg (fun p => (ofLex p).1) h)
  have ho : a.out=b.out := congrArg (fun p => (ofLex (ofLex p).2).1) h
  have hi : a.incoming=b.incoming := congrArg (fun p => (ofLex (ofLex p).2).2) h
  cases a
  cases b
  simp only [State.mk.injEq]
  exact ⟨hk,ho,hi⟩

instance stateOrder : LinearOrder State := LinearOrder.lift' key key_injective







def canonical (ss : List State) : List State := ss.mergeSort (· ≤  ·)

















def ofOrientation (ts : List Kind) (ds : List Bool) : List State :=
  (List.finRange ts.length).map fun v =>
    ⟨ts.get v,outCount (edges ts.length) ds v,ThreeBoundQ3RecordFields.incoming ts ds v⟩







end ThreeBoundRelaxedCanonical





end
end Sensitivity213981Formal


