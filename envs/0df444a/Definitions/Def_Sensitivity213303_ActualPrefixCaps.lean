-- Prove2me | Definitions.Def_Sensitivity213303_ActualPrefixCaps
-- name    : Sensitivity213303_ActualPrefixCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:22:20.051957+00:00
-- url     : https://prove2.me/theorems/a672338a-9b82-415b-86d4-5173529e1055
-- title:
--   Eligible and outside high vertices for candidate-prefix bounds
-- statement:
--   Given a high-head set H and target-prefix set T, outsideHigh(q) is the subset of H outside T with at most q actual guard failures. eligibleHigh(q) is the subset of H with at most q+1 guard failures. Their cardinalities determine how many high vertices can be adjoined to a coherent target set, or chosen as markers, when applying ordinary and marked labeling exclusions.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module ActualPrefixCaps; source SHA256 15e2833fdff4d4215491198840a2619655a555ecbfb70e9c46e73a4055444e85.

/- All prefix-cap ingredients are consequences of actual failed-guard sets
and the separately proved labeling exclusions. -/
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GlobalAccounting
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
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
namespace CandidateCoherence
end CandidateCoherence
namespace GuardAugmentation
end GuardAugmentation
namespace MarkedCandidateCaps
end MarkedCandidateCaps
namespace ResidualCaps
end ResidualCaps
namespace ThreeBoundMarkers
end ThreeBoundMarkers
namespace TournamentHighRows
end TournamentHighRows


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundPrefixCaps
open scoped Classical BigOperators
open TournamentHighRows CandidateCoherence GuardAugmentation ResidualCaps
open MarkedCandidateCaps ThreeBoundMarkers
noncomputable section
variable {V X : Type} [Fintype V] [DecidableEq V]

def outsideHigh (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X) (H T : Finset V) (q : ℕ) : Finset V :=
  (H \ T).filter fun v => (guardFailures R ell P children v).card ≤ q

def eligibleHigh (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X) (H : Finset V) (q : ℕ) : Finset V :=
  H.filter fun v => (guardFailures R ell P children v).card ≤ q+1









end
end ThreeBoundPrefixCaps


