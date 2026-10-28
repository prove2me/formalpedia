-- Prove2me | Definitions.Def_Sensitivity213303_ResidualCaps
-- name    : Sensitivity213303_ResidualCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:20:17.722412+00:00
-- url     : https://prove2.me/theorems/d53695f8-10d6-41be-b05b-5424939e4bc8
-- title:
--   Residual guard budgets and marker-based coherence bounds
-- statement:
--   The residual of a vertex is its actual guard-failure count minus its outgoing degree into the high-head set. Given selected markers, deletedHeads is the union of their color-mismatching heads and cleanedHeads is the surviving candidate set. DominatorCardBound(m,a) excludes coherent sets of size at least a dominated by m disjoint markers. MarkedCardBound(q,m,B,a) bounds a disjoint marked configuration with ordinary mismatch budget q, marker budget q+1 and total marker-to-candidate mismatch allowance B. These predicates turn labeling exclusions into target-count bounds with explicit residual costs.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module ResidualCaps; source SHA256 ec03db09ea4a2f3cbd1fc6c44684bdf2e0853b238640ccde652c9ebbdb8a911c.

/-
Source, double-dominator, and zero-mismatch residual caps for actual graded
target candidates. The residuals are actual failed guards left after all arcs
inside the full high-row tournament have been charged.
-/
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
namespace CandidateCoherence
end CandidateCoherence
namespace GuardAugmentation
end GuardAugmentation
namespace TournamentHighRows
end TournamentHighRows


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


