-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
-- name    : OAI_RepresentationTheory_Saxl_YoungRule
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:36:21.433124+00:00
-- url     : https://prove2.me/theorems/46b31f85-444c-40b4-9e1b-d42bac9f313b
-- title:
--   The list of the first $k$ row lengths of a Young diagram
-- statement:
--   Let $\theta$ be a Young diagram with row lengths $\theta_0\ge\theta_1\ge\cdots$ (rows are indexed from $0$, and $\theta_i=0$ for rows below the diagram). For $k\in\mathbb{N}$ the file defines the finite sequence of its first $k$ row lengths,
--   $$w_k(\theta)=(\theta_0,\theta_1,\dots,\theta_{k-1}),$$
--   recursively by $w_0(\theta)=()$ and $w_{k+1}(\theta)=w_k(\theta)$ followed by the single entry $\theta_k$. In particular $w_k(\theta)$ has length exactly $k$, and when $k$ is at least the number $\ell(\theta)$ of rows of $\theta$, its entries are the parts of $\theta$ followed by $k-\ell(\theta)$ zeros.
--
--   The sequence $w_k(\theta)$ is the list of prescribed strip sizes in Young's rule: if $\tau$ dominates $\theta$ and $|\tau|=|\theta|$, one builds a chain of horizontal strips from the empty diagram to $\tau$ whose successive strips have $\theta_0,\theta_1,\dots$ cells. Such a chain in turn produces a word of content $\theta$ (letter $j$ used $\theta_j$ times) and a nonzero linear functional on the Specht module of shape $\tau$ that is invariant under all permutations fixing that word.
--
--   **Formalization Note** The sequence is `rowWeights θ k : List ℕ`, built with list append, and `rowWeights_length` states that its length is `k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/YoungRule.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/YoungRule.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Horizontal-strip chains recording the exact ordered strip sizes. -/
def rowWeights (θ : YoungDiagram) : ℕ → List ℕ
  | 0 => []
  | k+1 => rowWeights θ k ++ [θ.rowLen k]

/- The actual constructive sufficiency step in Young's rule. No tableau,
Pieri, or representation hypothesis is assumed by this combinatorial theorem. -/
lemma rowWeights_length (θ : YoungDiagram) (k : ℕ) : (rowWeights θ k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rowWeights, List.length_append, List.length_singleton, ih]

/- Young's sufficiency in the exact form needed for the repeated-row quotient:
a dominant Specht has a nonzero invariant functional for a word of the
prescribed content. -/
end Saxl

end

end OAI


