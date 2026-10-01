-- Prove2me | Definitions.Def_LocalConjugacy_Proof_QuaternionCohomology
-- name    : LocalConjugacy_Proof_QuaternionCohomology
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:24:49.539165+00:00
-- url     : https://prove2.me/theorems/a8de449f-1a79-4d5e-bb96-48a205b57156
-- title:
--   Two cocycles for the quaternion example
-- statement:
--   The identity cocycle and the explicit nontrivial sign cocycle for the quaternion action, represented in the canonical finite-cocycle interface.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization interface.

import Mathlib
import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Quaternion

/-! Supporting definitions and the structural proofs required by their types and values. -/

section


/-!
The finite cohomology assertions for the quaternion counterexample. The original
cocycle calculation is promoted to the actual quotient H¹. A small subgroup
classification proves vanishing on every proper subgroup, hence every Sylow.
-/
namespace LocalConjugacy.Proof.QuaternionCohomology
open LocalConjugacy.QuaternionExample
set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Identity-valued cocycle for the explicit quaternion action. -/
def identityCocycle : FiniteCocycle action := ⟨fun _ => 1, by simp⟩
/-- The central sign cocycle supplies the second cohomology class. -/
def nontrivialCocycle : FiniteCocycle action := ⟨signCocycle, sign_isCocycle⟩











end LocalConjugacy.Proof.QuaternionCohomology

end


