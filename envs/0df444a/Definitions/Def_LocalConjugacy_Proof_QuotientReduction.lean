-- Prove2me | Definitions.Def_LocalConjugacy_Proof_QuotientReduction
-- name    : LocalConjugacy_Proof_QuotientReduction
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T14:26:58.526694+00:00
-- url     : https://prove2.me/theorems/492fa51f-8ad2-4d78-a519-2c3ab2e2f0a9
-- title:
--   The normal stabilizer condition
-- statement:
--   The stabilizer condition used in the quotient-reduction step of the cocycle extension argument.
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

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

/-! Algebraic quotient reduction from the earlier local development, rechecked here. -/

namespace LocalConjugacy

open Subgroup QuotientGroup

variable {G : Type*} [Group G]

/-- The repaired hypothesis: `N ⊓ H` is normalised by `N`.
For `H = G_α` a point stabiliser this says the stabiliser `N_α = N ⊓ G_α` is normal in `N`. -/
abbrev StabNormal := @IntersectionNormal









end LocalConjugacy

end LocalConjugacy.Proof

end


