-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
-- name    : OAI_RepresentationTheory_Saxl_SizedStrips
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:34:39.012983+00:00
-- url     : https://prove2.me/theorems/4d9586cd-f537-4def-ab77-0e401f00f6e0
-- title:
--   Chains of horizontal strips with prescribed sizes
-- statement:
--   Chains of Young diagrams obtained by successively adding horizontal strips of prescribed sizes.
--
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$) closed under moving up or to the left, and $|\mu|$ is its number of cells; $\nu\subseteq\mu$ denotes inclusion of cell sets. The skew shape $\mu/\eta$ is a horizontal strip when $\eta\subseteq\mu$ and $\mu\setminus\eta$ has at most one cell in each column. A tableau of shape $\mu$ on the positions $[n]=\{0,\dots,n-1\}$ is a bijection $[n]\to\mu$.
--
--   1. **Sized strip chains.** For a list $\mathbf b=(b_1,\dots,b_k)$ of natural numbers and Young diagrams $\nu,\mu$, the relation $\mathrm{Chain}(\mathbf b,\nu,\mu)$ is defined inductively: the empty list relates every $\mu$ to itself, and if $\mathrm{Chain}(\mathbf b,\nu,\eta)$ holds, $\mu/\eta$ is a horizontal strip and $|\eta|+b=|\mu|$, then $\mathrm{Chain}((b_1,\dots,b_k,b),\nu,\mu)$ holds. Equivalently, $\mathrm{Chain}(\mathbf b,\nu,\mu)$ means that there are Young diagrams
--   $$
--   \nu=\mu^{(0)}\subseteq\mu^{(1)}\subseteq\cdots\subseteq\mu^{(k)}=\mu
--   $$
--   such that each $\mu^{(j)}/\mu^{(j-1)}$ is a horizontal strip with exactly $b_j$ cells (a value $b_j=0$ forces $\mu^{(j)}=\mu^{(j-1)}$). In particular every such chain has $\nu\subseteq\mu$.
--
--   2. **Shape tableau.** For a Young diagram $\mu$, the fixed (canonical) tableau $[\,|\mu|\,]\to\mu$ used as the reference enumeration of the cells of $\mu$.
--
--   Chains of horizontal strips of sizes $b_1,\dots,b_k$ index iterated Pieri restrictions: along such a chain one obtains a surjective map from the Specht module of $\mu$ onto that of $\nu$ that is equivariant for the permutations preserving each added strip, the strips being distinguished by colors.
--
--   **Formalization Note** The relation is the inductive predicate `SizedStripChain bs ν μ` with constructors `nil` and `snoc` (which appends the new size at the end of the list), the horizontal-strip condition is `HorizontalStrip η μ`, and `SizedStripChain.le` gives `ν ≤ μ`. The shape tableau is `shapeTableau μ = canonicalTableau μ rfl`, a `Tableau μ.card μ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/SizedStrips.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/SizedStrips.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

inductive SizedStripChain : List ℕ → YoungDiagram → YoungDiagram → Prop
  | nil (μ) : SizedStripChain [] μ μ
  | snoc {bs ν η μ b} : SizedStripChain bs ν η → HorizontalStrip η μ →
      η.card + b = μ.card → SizedStripChain (bs ++ [b]) ν μ

lemma SizedStripChain.le {bs ν μ} (hs : SizedStripChain bs ν μ) : ν ≤ μ := by
  induction hs with
  | nil => exact le_rfl
  | snoc hs hh hc ih => exact ih.trans hh.1

abbrev shapeTableau (μ : YoungDiagram) : Tableau μ.card μ := canonicalTableau μ rfl

/- Iterated positive Pieri, with an explicit coloring of the added strips.
The map is surjective and equivariant for all permutations preserving each
strip, not just for the smaller symmetric group. -/
end Saxl

end

end OAI


