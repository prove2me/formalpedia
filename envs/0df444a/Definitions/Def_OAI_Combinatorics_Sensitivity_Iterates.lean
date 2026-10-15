-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_Iterates
-- name    : OAI_Combinatorics_Sensitivity_Iterates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:52:22.827891+00:00
-- url     : https://prove2.me/theorems/5cd47354-f5cb-4dc9-b063-f1aad14769b5
-- title:
--   Coordinate sets of iterated block compositions
-- statement:
--   Let $I$ be a set. Define sets $I^{(m)}$, $m \in \mathbb{N}$, by recursion:
--   $$
--   I^{(0)} = \{\ast\}, \qquad I^{(m+1)} = I \times I^{(m)} ,
--   $$
--   where $\{\ast\}$ is a one-point set. An element of $I^{(m)}$ is a nested tuple $(i_1, (i_2, \dots, (i_m, \ast)\dots))$ with $i_1, \dots, i_m \in I$, so $I^{(m)}$ is a copy of $I^m$ in which one factor is split off at each step. When $I$ is finite, every $I^{(m)}$ is finite, with $|I|^m$ elements.
--
--   These are the coordinate sets of iterated block composition. For a Boolean function $f$ on $\{0,1\}^I$ (Boolean values identified with $\{0,1\}$), the $m$-fold composite $f^{\circ m}$ is a Boolean function on $\{0,1\}^{I^{(m)}}$: $f^{\circ 0}$ returns the single coordinate of its input, and $f^{\circ (m+1)} = f \circ f^{\circ m}$ is the block composition of $f$ with $|I|$ disjoint copies of $f^{\circ m}$, whose coordinate set is $I \times I^{(m)} = I^{(m+1)}$. For finite $I$, writing $s$ for sensitivity and $\mathrm{bs}(\cdot, \mathbf{0})$ for block sensitivity at the all-zero input $\mathbf{0}$, one has $s(f^{\circ m}) \le s(f)^m$, and $\mathrm{bs}(f^{\circ m}, \mathbf{0}) \ge \mathrm{bs}(f, \mathbf{0})^m$ when $f(\mathbf{0}) = 0$; these facts are proved separately.
--
--   **Formalization Note** The definition is the abbreviation `IterateCoord I m`, by recursion on `m` with base case `Unit`, together with the recursive `Fintype` instance `iterateCoordFintype`. The iterated composition itself and the cardinality formula are stated separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/Iterates.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/Iterates.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_Sensitivity_Reindex
import Definitions.Def_OAI_Combinatorics_Sensitivity_Construction
import Definitions.Def_OAI_Combinatorics_Sensitivity_FixedCoordinates
import Definitions.Def_OAI_Combinatorics_Sensitivity_LabelingEvents
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCyclic

namespace OAI

/-! Repeated disjoint composition with explicit finite raw-coordinate types. -/

noncomputable section
open scoped Classical

namespace Paper320

abbrev IterateCoord (I : Type) : ℕ → Type
  | 0 => Unit
  | m + 1 => I × IterateCoord I m

instance iterateCoordFintype {I : Type} [Fintype I] :
    (m : ℕ) → Fintype (IterateCoord I m)
  | 0 => inferInstanceAs (Fintype Unit)
  | m + 1 =>
    letI : Fintype (IterateCoord I m) := iterateCoordFintype (I := I) m
    inferInstanceAs (Fintype (I × IterateCoord I m))

variable {I : Type} [Fintype I]

end Paper320

end

end OAI


