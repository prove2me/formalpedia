-- Prove2me | Definitions.Def_Sensitivity213303_GlobalAccounting
-- name    : Sensitivity213303_GlobalAccounting
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:21:09.591273+00:00
-- url     : https://prove2.me/theorems/61c3dfd1-1d85-4f1f-bd99-16f3a0ae15b0
-- title:
--   Actual type histograms and external guard-repair sets
-- statement:
--   For a head set H, a type map and incoming counts, typeCount counts each type and hist counts each type at capped incoming count min(2,r). For guard sources G, externalHeads(v) consists of actual failed guards outside H, and externalBits is the union of their selected-child downward-sensitivity sets lifted into parent coordinates. These definitions keep internal head repairs and residual external repairs separate before taking cardinalities.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module GlobalAccounting; source SHA256 8368f847d33d41b253e3289693d4dc50d871ab3b4b05626890fae7d30bb69fc4.

/- Actual coordinate accounting: incoming arcs are deduplicated to child
positions, external arcs have residual multiplicity, and histograms are
derived identities. -/
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundAccounting
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical BigOperators
noncomputable section
variable {V I K : Type} [Fintype V] [Fintype I] [Fintype K]













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


