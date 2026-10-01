-- Prove2me | Definitions.Def_LocalConjugacy_Proof_Compactness
-- name    : LocalConjugacy_Proof_Compactness
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T14:11:51.784466+00:00
-- url     : https://prove2.me/theorems/bde87b28-46ba-4b9f-893e-83e484b80606
-- title:
--   Closed conjugacy transporter sets
-- statement:
--   For subgroups $H,K$ of a group, the transporter consists of elements $g$ satisfying $gHg^{-1}\le K$. This set is the object used in the compactness arguments.
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

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The closed set of elements sending every element of `H` into `K`
by conjugation. -/
def transporter (H K : Subgroup G) : Set G :=
  {g | ∀ h ∈ H, g * h * g⁻¹ ∈ K}





end LocalConjugacy

end LocalConjugacy.Proof

end


