-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_Reindex
-- name    : OAI_Combinatorics_Sensitivity_Reindex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:41:23.827533+00:00
-- url     : https://prove2.me/theorems/9d735469-6250-4b05-bdca-804e583f88f9
-- title:
--   Renaming the coordinates of a Boolean function along a bijection
-- statement:
--   Identify Boolean values with $\{0,1\}$. Let $I$ and $J$ be sets and let $e : I \to J$ be a bijection. For a Boolean function $f : \{0,1\}^I \to \{0,1\}$, its reindexing along $e$ is the Boolean function $f^{e} : \{0,1\}^J \to \{0,1\}$ given by
--   $$
--   f^{e}(x) = f(x \circ e), \qquad (x \circ e)_i = x_{e(i)} \quad (i \in I).
--   $$
--   Thus $f^{e}$ is $f$ with the variable indexed by $i$ renamed $e(i)$. Reindexing back along the inverse bijection recovers the original function:
--   $$
--   \big(f^{e}\big)^{e^{-1}} = f .
--   $$
--
--   Reindexing transports a Boolean function built on a structured coordinate set, such as a product of tower coordinates, to the standard index set $\{0, 1, \dots, n-1\}$. For finite $I$ and $J$ it preserves sensitivity, block sensitivity and the value at the all-zero input; these invariance statements are proved separately.
--
--   **Formalization Note** The definition is `reindex e f` for an equivalence `e : I ≃ J`, and the identity above is the simp lemma `reindex_symm`. No finiteness is needed for the definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/Reindex.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/Reindex.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_OAI_Combinatorics_Sensitivity_Or

namespace OAI

/-! Coordinate equivalences preserve the two literal Boolean complexity measures. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J : Type}

def reindex (e : I ≃ J) (f : (I → Bool) → Bool) : (J → Bool) → Bool :=
  fun x => f (fun i => x (e i))

@[simp] theorem reindex_symm (e : I ≃ J) (f : (I → Bool) → Bool) :
    reindex e.symm (reindex e f) = f := by
  funext x
  simp [reindex]

section Finite
variable [Fintype I] [Fintype J]

end Finite
end Paper320

end

end OAI


