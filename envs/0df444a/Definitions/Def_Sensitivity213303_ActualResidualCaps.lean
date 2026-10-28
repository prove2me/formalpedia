-- Prove2me | Definitions.Def_Sensitivity213303_ActualResidualCaps
-- name    : Sensitivity213303_ActualResidualCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:24:49.958297+00:00
-- url     : https://prove2.me/theorems/b62278ca-761e-4b37-9b55-b9c3ce574373
-- title:
--   Sorted residual prefix sums of the actual high-head tournament
-- statement:
--   For every high head w, form its actual failed-guard count minus its outgoing degree within the high-head set. residualPrefix(m) sorts these natural residuals and sums the smallest m values. Selecting markers with these smallest residuals gives the numerical improvement in the source, double-dominator and marked target-prefix bounds.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module ActualResidualCaps; source SHA256 51b59f64dad351405b415f3034ed5f5d52a9cd317d6020adfa4c1fc557a46782.

/- Residual marker bounds in the coordinates of the actual Boolean stage. -/
import Definitions.Def_Sensitivity213303_ActualPrefixCaps
import Definitions.Def_Sensitivity213303_ActualTargetAccounting
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GlobalAccounting
import Definitions.Def_Sensitivity213303_GradedCandidates
import Definitions.Def_Sensitivity213303_GradedGlobalCover
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_HeadCosts
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_Q2EnumerationBridge
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
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundActualEnumeration
end ThreeBoundActualEnumeration
namespace ThreeBoundActualHeadCosts
end ThreeBoundActualHeadCosts
namespace ThreeBoundActualTargets
end ThreeBoundActualTargets
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
namespace ThreeBoundGradedCover
end ThreeBoundGradedCover
namespace ThreeBoundPrefixCaps
end ThreeBoundPrefixCaps
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundActualResidualCaps
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundGradedCandidates
open ThreeBoundGradedCover ThreeBoundActualHeadCosts ThreeBoundActualEnumeration
open ThreeBoundActualTargets ThreeBoundPrefixCaps
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def residualPrefix (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (m : ℕ) : ℕ :=
  let H := highHeads S F t j x
  (((H.toList.map fun w => (failed S F j x w).card-(H.filter (S.Adj w)).card).mergeSort
    (· ≤ ·)).take m).sum







end
end ThreeBoundActualResidualCaps


