-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
-- name    : OAI_Combinatorics_Sensitivity_ProfileArithmetic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:35:42.429899+00:00
-- url     : https://prove2.me/theorems/c7b82c51-5b96-402b-9362-8929c71cb6ff
-- title:
--   Normalized maximum of a pair of sensitivity profiles
-- statement:
--   For a real number $M$, a level $n \in \mathbb{N}$ and two real numbers $s_0, s_1$ (typically the sensitivity profile of a family on rejected and on accepted inputs at level $n$ of the recursive construction), the normalized maximum is
--
--   $$
--   \nu_M(n; s_0, s_1) = \max\Big( \frac{s_0}{M^n},\ \frac{s_1}{M^{n+1}} \Big).
--   $$
--
--   The profiles are expected to grow like $M^n$ on rejected inputs and like $M^{n+1}$ on accepted inputs, so dividing by these powers puts both on a common scale. Applied to the side profiles and to the joint profiles, the four linear recurrences of the construction turn into two coupled scalar recurrences for the normalized quantities, which are then shown to stay bounded.
--
--   **Formalization Note** The definition is `normalizedMax M n s₀ s₁` over the reals; by Lean's convention division by zero gives $0$, which only matters when $M = 0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/ProfileArithmetic.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/ProfileArithmetic.lean by skeleton subtraction
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

namespace OAI

/-! The four raw recurrences imply the two normalized scalar recurrences. -/

noncomputable section

namespace Paper320

def normalizedMax (M : ℝ) (n : ℕ) (s₀ s₁ : ℝ) : ℝ :=
  max (s₀ / M ^ n) (s₁ / M ^ (n + 1))

end Paper320

end

end OAI


