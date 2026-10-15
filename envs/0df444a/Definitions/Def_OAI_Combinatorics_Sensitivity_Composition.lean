-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
-- name    : OAI_Combinatorics_Sensitivity_Composition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:38:21.024171+00:00
-- url     : https://prove2.me/theorems/3b85f53b-993f-49af-bfd9-403991386eac
-- title:
--   Block composition of Boolean functions
-- statement:
--   Let $I$ and $J$ be sets, identify Boolean values with $\{0,1\}$, and let $f : \{0,1\}^I \to \{0,1\}$ and $g : \{0,1\}^J \to \{0,1\}$ be Boolean functions. Their block composition is the Boolean function on $\{0,1\}^{I \times J}$ obtained by feeding $|I|$ disjoint copies of $g$ into $f$:
--
--   $$
--   (f \circ g)(x) = f\Big( \big( g(x_{i,\cdot}) \big)_{i \in I} \Big), \qquad x_{i,\cdot} = \big( x_{(i,j)} \big)_{j \in J} \in \{0,1\}^J .
--   $$
--
--   The $i$-th copy of $g$ reads only its own block of coordinates $\{i\} \times J$, so different copies share no inputs.
--
--   Block composition is the standard way of combining Boolean functions in sensitivity and query complexity: its sensitivity is at most the product of the sensitivities, and its block sensitivity at the all-zero input is at least the product of the zero block sensitivities when $g$ vanishes at the all-zero input. Composing an OR gate with copies of a function is used to balance the sensitivities on 0-inputs and 1-inputs.
--
--   **Formalization Note** The definition is `compose f g : (I × J → Bool) → Bool`; this file contains only the definition, and the theorems about it are stated separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/Composition.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/Composition.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SensitivitySeparation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic

namespace OAI

/-! Disjoint Boolean composition, with each child retaining its own raw coordinates. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320

variable {I J : Type}

def compose (f : (I → Bool) → Bool) (g : (J → Bool) → Bool) :
    (I × J → Bool) → Bool :=
  fun x => f (fun i => g (fun j => x (i, j)))

section Finite
variable [Fintype I] [Fintype J]

end Finite
end Paper320

end

end OAI


