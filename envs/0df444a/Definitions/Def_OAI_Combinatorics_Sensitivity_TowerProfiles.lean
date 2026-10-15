-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
-- name    : OAI_Combinatorics_Sensitivity_TowerProfiles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:35:01.699358+00:00
-- url     : https://prove2.me/theorems/e48dd29f-a47b-4f2e-80bb-1b6aecc76d1d
-- title:
--   Sensitivity profiles along the levels of the tower
-- statement:
--   Fix a tournament $T$, a labeling $\lambda$ with $r$ labels, a finite coordinate set $I$, and a base assigning to every $h$ a family of $h$ predicates on $\{0,1\}^I$. Let $F^{(n,h)}$ be the tower family, the family of $h$ predicates on the level-$n$ coordinates obtained from $\mathrm{base}(h+n)$ by $n$ levels of the row-clause construction, and let $S_b$ and $J_b$, $b \in \{0,1\}$, be the side and joint sensitivity profiles of a family. For a total index budget $D$ and a level $n$ define
--
--   $$
--   \mathrm{Side}_D(n, b) = S_b\big(F^{(n, D-n)}\big), \qquad \mathrm{Joint}_D(n, b) = J_b\big(F^{(n, D-n)}\big).
--   $$
--
--   For $n \le D$ these are the profiles of the family of $D - n$ predicates reached after $n$ levels starting from $\mathrm{base}(D)$. At level $0$ they reduce to the profiles of the base family itself: $\mathrm{Side}_D(0,b) = S_b(\mathrm{base}(D))$ and $\mathrm{Joint}_D(0,b) = J_b(\mathrm{base}(D))$.
--
--   These four sequences ($b = 0, 1$) are the quantities governed by the four linear recurrences of the construction, from which the sensitivity of the terminal predicate is bounded.
--
--   **Formalization Note** The definitions are `towerSide` and `towerJoint`, with the level-zero simplifications `towerSide_zero` and `towerJoint_zero`. The index count $D - n$ uses natural-number subtraction, which truncates to $0$ when $n > D$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/TowerProfiles.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/TowerProfiles.lean by skeleton subtraction
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

namespace OAI

/-! The fixed-initial-height profiles and their exact four recurrences. -/

noncomputable section
open scoped Classical

namespace Paper320

def towerSide {k r : ℕ} {I : Type} [Fintype I] (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D n : ℕ) (b : Bool) : ℕ :=
  sideSensitivity (towerFamily T label base n (D - n)) b

def towerJoint {k r : ℕ} {I : Type} [Fintype I] (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D n : ℕ) (b : Bool) : ℕ :=
  jointSensitivity (towerFamily T label base n (D - n)) b

@[simp] theorem towerSide_zero {k r : ℕ} {I : Type} [Fintype I] (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D : ℕ) (b : Bool) : towerSide T label base D 0 b = sideSensitivity (base D) b := by
  rfl

@[simp] theorem towerJoint_zero {k r : ℕ} {I : Type} [Fintype I] (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D : ℕ) (b : Bool) : towerJoint T label base D 0 b = jointSensitivity (base D) b := by
  rfl

end Paper320

end

end OAI


