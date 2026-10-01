-- Prove2me | Definitions.Def_LocalConjugacy_Proof_AbelianComplement
-- name    : LocalConjugacy_Proof_AbelianComplement
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T14:24:04.851559+00:00
-- url     : https://prove2.me/theorems/d4ca839c-a605-4d92-b097-c1a81c3da9a9
-- title:
--   Projection along a complement
-- statement:
--   The normal-factor projection associated to a decomposition $G=NH$ with $N\cap H=1$. Uniqueness of the decomposition specifies the projection used to compare complements.
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

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
namespace AbelianComplement

variable {G : Type*} [Group G] (N H : Subgroup G) [N.Normal]
  (hc : Subgroup.IsComplement' N H)

noncomputable def projection (x : G) : N := (hc.equiv x).1















end AbelianComplement
end LocalConjugacy

end LocalConjugacy.Proof

end


