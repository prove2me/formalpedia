-- Prove2me | Definitions.Def_Sensitivity213981Formal_GlobalAccounting
-- name    : Sensitivity213981Formal_GlobalAccounting
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T18:24:52.315813+00:00
-- url     : https://prove2.me/theorems/058ecb4d-7636-4f08-924b-626d2ba1aebc
-- title:
--   Global Accounting — sensitivity certificate definitions
-- statement:
--   The definitions for Global Accounting in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundAccounting.hist`, `ThreeBoundAccounting.typeCount`, `ThreeBoundAccounting.externalHeads`, `ThreeBoundAccounting.hits`, `ThreeBoundAccounting.externalBits`, `ThreeBoundAccounting.incoming`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; GlobalAccounting.lean, lines 1–209.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Actual coordinate accounting: incoming arcs are deduplicated to child
positions, external arcs have residual multiplicity, and histograms are
derived identities. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundAccounting
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical BigOperators
noncomputable section
variable {V I K : Type} [Fintype V] [Fintype I] [Fintype K]

def hits (R : V → V → Prop) (ell : V → V → Bool) (G : Finset V) (w : V) : Finset Bool :=
  (G.filter fun v => R v w).image fun v => ell v w

def incoming (R : V → V → Prop) (G : Finset V) (w : V) : ℕ :=
  (G.filter fun v => R v w).card









def hist (H : Finset V) (tag : V → K) (inc : V → ℕ) (k : K) (h : ℕ) : ℕ :=
  (H.filter fun v => tag v = k ∧ min 2 (inc v) = h).card

def typeCount (H : Finset V) (tag : V → K) (k : K) : ℕ :=
  (H.filter fun v => tag v = k).card















variable {L : Type} [Preorder L]

def externalHeads (S : Stage L I V) (F : L → (I → Bool) → Bool) (j : L)
    (x : ((V × Bool) × I) → Bool) (H : Finset V) (v : V) : Finset V :=
  failed S F j x v \ H





def externalBits (S : Stage L I V) (F : L → (I → Bool) → Bool) (j : L)
    (x : ((V × Bool) × I) → Bool) (G H : Finset V) : Finset ((V × Bool) × I) :=
  G.biUnion fun v => (externalHeads S F j x H v).biUnion fun w =>
    liftBits w (S.label v w) (flipsTo (F (S.guard j)) false (child x w (S.label v w)))





end
end ThreeBoundAccounting




end
end Sensitivity213981Formal


