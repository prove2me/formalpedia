-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
-- name    : OAI_Analysis_LipschitzFree_SignedTests
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:11:04.917986+00:00
-- url     : https://prove2.me/theorems/16d9b057-cff4-4df8-983e-452aa724f83f
-- title:
--   Exceptional records, total variation, variation on a subset and pairings of signed weights
-- statement:
--   This file introduces elementary notions for record functions and for real weight vectors on a finite set.
--
--   1. **Exceptional entries.** Let $D$ and $S$ be sets and $r:D\times S\to\mathbb{N}$ a record function. An element $e\in D$ is *exceptional* at $j\in S$ if $r(e,j)$ is the strict unique maximum of $r(\cdot,j)$:
--   $$r(g,j)<r(e,j)\qquad\text{for all } g\in D \text{ with } g\neq e .$$
--
--   Now let $S$ be finite and $\mu:S\to\mathbb{R}$ a signed weight vector.
--
--   2. **Total variation:** $\displaystyle \|\mu\|_{\mathrm{TV}}=\sum_{j\in S}|\mu_j|$.
--   3. **Variation on a subset** $E\subseteq S$: $\displaystyle \|\mu\|_{E}=\sum_{j\in E}|\mu_j|$.
--   4. **Pairing** with a function $f:S\to\mathbb{R}$: $\displaystyle \langle\mu,f\rangle=\sum_{j\in S}\mu_j\,f(j)$.
--
--   These are the quantities in which the incidence-averaging obstruction of the construction is phrased: Lipschitz test functions are paired with the coefficient vectors that an operator produces at the vertices of a graph, the total variation of these vectors is bounded, and the variation on sets of exceptional states is averaged over the edges of a port graph.
--
--   **Formalization Note** `Exceptional r e j` is the displayed condition; `totalVariation`, `variationOn` and `pairing` are finite sums over a `Fintype S`, and `variationOn μ E` is written as $\sum_{j\in S}$ of $|\mu_j|$ if $j\in E$ and $0$ otherwise, for an arbitrary `Set S`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/SignedTests.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/SignedTests.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths

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


