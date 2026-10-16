-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_SignedTests__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:08:10.873769+00:00
-- url     : https://prove2.me/theorems/010f85f6-18e6-4b5c-a57a-80c4313f6ca4
-- title:
--   Exceptional record maximisers, total variation and pairings of signed weights on a finite set
-- statement:
--   This file introduces elementary notions for signed weight vectors on a finite index set and for record functions.
--
--   1. **Exceptional element.** Let $D$ and $S$ be sets and $r:D\times S\to\mathbb{N}$. An element $e\in D$ is exceptional for $j\in S$ if it is the unique strict maximiser of $r(\cdot,j)$:
--   $$r(g,j)<r(e,j)\qquad\text{for all } g\in D,\ g\neq e .$$
--
--   Let now $S$ be a finite set and $\mu:S\to\mathbb{R}$ a signed weight vector.
--
--   2. **Total variation.** $\|\mu\|_{\mathrm{TV}}=\sum_{j\in S}|\mu_j|$.
--   3. **Variation on a subset.** For $E\subseteq S$, the variation of $\mu$ on $E$ is $\sum_{j\in E}|\mu_j|$.
--   4. **Pairing.** For $f:S\to\mathbb{R}$, $\langle\mu,f\rangle=\sum_{j\in S}\mu_j\,f_j$.
--
--   Signed weights on finitely many points (such as coefficient vectors of elements of a Lipschitz-free space supported on a finite set) are tested against real functions through the pairing, and the total variation and the variation on a subset measure the size of such weight vectors, globally and on a distinguished set of indices. Applied to a record function $r(e,j)$ indexed by ports $e$ and states $j$, the exceptional-element condition singles out, for a given state, the port whose record is strictly longer than that of every other port (if there is one).
--
--   **Formalization Note** The definitions are `Exceptional r e j`, `totalVariation μ`, `variationOn μ E` (for a set `E`, using classical decidability of membership) and `pairing μ f`, the last three over a `Fintype` index type $S$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/SignedTests.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/SignedTests.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coefficients
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Words__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths__RealL1Renorming

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Signed variation, scalar extension, and incidence averaging
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

section Records

variable {D S : Type*}

def Exceptional (r : D → S → ℕ) (e : D) (j : S) : Prop :=
  ∀ g : D, g ≠ e → r g j < r e j

end Records

section SignedTests

variable {S : Type*} [Fintype S]

def totalVariation (μ : S → ℝ) : ℝ := ∑ j, |μ j|

def variationOn (μ : S → ℝ) (E : Set S) : ℝ := by
  classical
  exact ∑ j, if j ∈ E then |μ j| else 0

def pairing (μ f : S → ℝ) : ℝ := ∑ j, μ j * f j

end SignedTests
section

variable {N : Type*} [MetricSpace N]

end

variable {X D S : Type*} [Fintype X] [Fintype D] [Fintype S]

end DiscreteFree

end

end OAI


