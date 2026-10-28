-- Prove2me | Definitions.Def_Sensitivity213303_CandidateCoherence
-- name    : Sensitivity213303_CandidateCoherence
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:54:49.585566+00:00
-- url     : https://prove2.me/theorems/23820360-0657-4fd8-9147-c9a6fe154b73
-- title:
--   Colored mismatch budgets and ordinary exclusion thresholds
-- statement:
--   For a labelled directed graph, a candidate set T and a binary head color, mismatch(v) consists of outgoing heads in T whose edge label disagrees with the head color. OrdinaryGood(T,q) requires at most q such mismatches from every vertex of T. NoOrdinary(q,a) asserts that no set of exactly a vertices admits such a coloring. These predicates express the finite labeling exclusion used to bound actual target candidates with accepted complementary children.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module CandidateCoherence; source SHA256 c389062dc583cd307e3b5ebc46a8b3f3386215560a89a02cd6a0b7f6300c678f.

/-
The graded-target to labeling-exclusion bridge.

Targets at different rows may use different lower thresholds. A geometric
one-child candidate has an accepted partner; coloring its row by the other
position makes every label mismatch an actual guard failure. This argument
is independent of fixed versus graded targets and applies to min/max targets.
-/
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
namespace MinmaxLocal
end MinmaxLocal
namespace TournamentHighRows
end TournamentHighRows


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CandidateCoherence
open scoped Classical
open MinmaxLocal TournamentHighRows

variable {N : ℕ} {V X : Type}











noncomputable def mismatch (R : V → V → Prop) (ell : V → V → Bool)
    (T : Finset V) (color : V → Bool) (v : V) : Finset V := by
  classical
  exact T.filter fun w => R v w ∧ ell v w ≠ color w

def OrdinaryGood (R : V → V → Prop) (ell : V → V → Bool)
    (T : Finset V) (q : ℕ) (color : V → Bool) : Prop :=
  ∀ v ∈ T, (mismatch R ell T color v).card ≤ q

/-- An exact-size ordinary exclusion, in the same coloring semantics as the
    accepted labeling construction. -/
def NoOrdinary (R : V → V → Prop) (ell : V → V → Bool) (q a : ℕ) : Prop :=
  ∀ T : Finset V, T.card = a → ∀ color : V → Bool, ¬ OrdinaryGood R ell T q color







section ActualGuards
variable [Fintype V]











end ActualGuards
end CandidateCoherence


