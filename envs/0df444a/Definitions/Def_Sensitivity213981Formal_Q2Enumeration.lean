-- Prove2me | Definitions.Def_Sensitivity213981Formal_Q2Enumeration
-- name    : Sensitivity213981Formal_Q2Enumeration
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:08:36.806071+00:00
-- url     : https://prove2.me/theorems/b178317b-258e-4a88-a0a4-6cf73ad8aec9
-- title:
--   Q2 Enumeration — sensitivity certificate definitions
-- statement:
--   The definitions for Q2 Enumeration in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundQ2.positivePrefix`, `ThreeBoundQ2.spend`, `ThreeBoundQ2.outCount`, `ThreeBoundQ2.orientations`, `ThreeBoundQ2.edges`, `ThreeBoundQ2.allowedTypes`, `ThreeBoundQ2.instDecidableAllowedTypes`, `ThreeBoundQ2.Kind`, `ThreeBoundQ2.directedEdges`, `ThreeBoundQ2.budget`, `ThreeBoundQ2.positiveLevel`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Q2Enumeration.lean, lines 1–214.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort

namespace Sensitivity213981Formal
section
/-
An executable, exhaustive enumerator of the eight q <= 2 high-row types and
their budget-feasible tournament orientations.  The completeness proof is
structural, not an assertion that a foreign program enumerated all cases.

This module supplies finite combinatorial coverage.  It does not prove the
semantic charging inequalities for the sensitivity transfer.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundQ2

/-- P0, P1-only, P2-only, G0-only, G1-only, G2, H1, H2. -/
abbrev Kind := Fin 8

def budget (t : Kind) : ℕ :=
  match t.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 1
  | _ => 2



def positiveLevel (t : Kind) : Option ℕ :=
  match t.val with
  | 0 => some 0
  | 1 => some 1
  | 2 => some 2
  | 6 => some 1
  | 7 => some 2
  | _ => none

def positivePrefix (q : ℕ) (t : Kind) : Bool :=
  match positiveLevel t with
  | some b => b ≤ q
  | none => false





section Orientations
variable {V : Type} [DecidableEq V]

def spend (b : V → ℕ) (v : V) : V → ℕ :=
  fun w => if w = v then b w - 1 else b w

/-- A false bit directs an edge from its first endpoint to its second. -/
def outCount : List (V × V) → List Bool → V → ℕ
  | [], _, _ => 0
  | _::_, [], _ => 0
  | e::es, d::ds, v =>
      (if (if d then e.2 else e.1) = v then 1 else 0) + outCount es ds v

/-- Prune a partial orientation exactly when it would exceed a vertex budget. -/
def orientations (b : V → ℕ) : List (V × V) → List (List Bool)
  | [] => [[]]
  | e::es =>
      (if 0 < b e.1 then (orientations (spend b e.1) es).map (List.cons false) else []) ++
      (if 0 < b e.2 then (orientations (spend b e.2) es).map (List.cons true) else [])



end Orientations

/-- Each unordered vertex pair occurs once, with the smaller index first. -/
def edges (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => i < j).map fun j => (i,j)

def allowedTypes (ts : List Kind) : Prop :=
  ts.length * (ts.length - 1) / 2 ≤ (ts.map budget).sum ∧
  (ts.filter (positivePrefix 0)).length ≤ 1 ∧
  (ts.filter (positivePrefix 1)).length ≤ 3 ∧
  (ts.filter (positivePrefix 2)).length ≤ 5

instance _root_.Sensitivity213981Formal.ThreeBoundQ2.instDecidableAllowedTypes (ts : List Kind) : Decidable (allowedTypes ts) := by
  unfold allowedTypes
  infer_instance







def directedEdges {V : Type} (es : List (V × V)) (ds : List Bool) : List (V × V) :=
  (es.zip ds).map fun z => if z.2 then (z.1.2,z.1.1) else z.1







end ThreeBoundQ2





end
end Sensitivity213981Formal


