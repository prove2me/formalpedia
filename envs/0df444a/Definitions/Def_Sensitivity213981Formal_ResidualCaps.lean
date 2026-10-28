-- Prove2me | Definitions.Def_Sensitivity213981Formal_ResidualCaps
-- name    : Sensitivity213981Formal_ResidualCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:13:04.989418+00:00
-- url     : https://prove2.me/theorems/0170219c-3283-4f0c-b6ed-b497eb1ed612
-- title:
--   Residual Caps — sensitivity certificate definitions
-- statement:
--   The definitions for Residual Caps in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ResidualCaps.DominatorCardBound`, `ResidualCaps.MarkedGood`, `ResidualCaps.MarkedCardBound`, `ResidualCaps.residual`, `ResidualCaps.deletedHeads`, `ResidualCaps.cleanedHeads`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ResidualCaps.lean, lines 1–223.

import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Q2Enumeration
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace Sensitivity213981Formal
section
/-
Source, double-dominator, and zero-mismatch residual caps for actual graded
target candidates. The residuals are actual failed guards left after all arcs
inside the full high-row tournament have been charged.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ResidualCaps
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation
noncomputable section

variable {V X : Type} [Fintype V] [DecidableEq V]

/-- The number of failed guards not forced by outgoing arcs to the high set. -/
def residual (R : V → V → Prop) (ell : V → V → Bool)
    (guard : X → Prop) (children : V → Bool → X) (H : Finset V) (v : V) : ℕ :=
  (guardFailures R ell guard children v).card - (outNeighbors R H v).card

def deletedHeads (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) : Finset V :=
  M.biUnion (mismatch R ell A color)

def cleanedHeads (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) : Finset V :=
  A \ deletedHeads R ell A M color

/-- This is the common exact-cardinality consequence of the source and
    double-dominator exclusions: m=1 is a source, m=2 is a double dominator. -/
def DominatorCardBound (R : V → V → Prop) (ell : V → V → Bool) (m a : ℕ) : Prop :=
  ∀ (A M : Finset V) (color : V → Bool), Disjoint A M → M.card = m →
    (∀ v ∈ M, ∀ w ∈ A, R v w) →
    (∀ v ∈ A ∪ M, (mismatch R ell A color v).card = 0) → A.card < a

/-- The marked exclusions used by the q2 generator all use an empty positive
    marker set; every marker therefore has the extra unit of budget. -/
def MarkedGood (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (q B : ℕ) (color : V → Bool) : Prop :=
  (∀ v ∈ A, (mismatch R ell A color v).card + (outNeighbors R M v).card ≤ q) ∧
  (∀ v ∈ M, (outNeighbors R M v).card + (mismatch R ell A color v).card ≤ q+1) ∧
  (∑ v ∈ M, (mismatch R ell A color v).card) ≤ B

def MarkedCardBound (R : V → V → Prop) (ell : V → V → Bool)
    (q m B a : ℕ) : Prop :=
  ∀ (A M : Finset V) (color : V → Bool), Disjoint A M → M.card = m →
    MarkedGood R ell A M q B color → A.card < a























end
end ResidualCaps







end
end Sensitivity213981Formal


