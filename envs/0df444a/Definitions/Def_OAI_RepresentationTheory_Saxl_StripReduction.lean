-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_StripReduction
-- name    : OAI_RepresentationTheory_Saxl_StripReduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:53:08.524679+00:00
-- url     : https://prove2.me/theorems/33ec8b72-21ab-42fd-9161-921a08ff30ed
-- title:
--   Chains of nonempty horizontal strips and the row lengths of the staircase
-- statement:
--   For Young diagrams $\eta,\mu$ (finite sets of cells $(i,j)\in\mathbb{N}^2$ closed under moving up or left), $\mu/\eta$ is a horizontal strip if $\eta\subseteq\mu$ and the skew cells $\mu\setminus\eta$ contain at most one cell in each column.
--
--   1. **Strip chains.** For $q\in\mathbb{N}$ and Young diagrams $\nu,\mu$, the relation $\nu\xrightarrow{\,q\,}\mu$ ("a chain of $q$ nonempty horizontal strips from $\nu$ up to $\mu$") is defined inductively: $\mu\xrightarrow{\,0\,}\mu$, and if $\nu\xrightarrow{\,q\,}\eta$, $\mu/\eta$ is a horizontal strip and $\eta\neq\mu$, then $\nu\xrightarrow{\,q+1\,}\mu$. Equivalently, there are diagrams
--   $$\nu=\eta_0\subsetneq\eta_1\subsetneq\cdots\subsetneq\eta_q=\mu$$
--   with each $\eta_{r+1}/\eta_r$ a nonempty horizontal strip.
--   2. **Rows of the staircase.** The staircase $\delta_m=\{(i,j):i+j<m\}$ has row lengths $(\delta_m)_i=m-i$ for $i\le m$ and $(\delta_m)_i=0$ for $i\ge m$.
--
--   Strip chains organize the induction on $m$ in the analysis of Specht modules of staircase size: a diagram $\mu$ with $|\mu|=|\delta_m|$ and $m\ge2$ that is not dominated by $\delta_m$ can be reduced either by one horizontal strip to a diagram of size $|\delta_{m-1}|$ or, when $m\ge5$, by a chain of at most four nonempty horizontal strips to a diagram of size $|\delta_{m-2}|$.
--
--   **Formalization Note** The relation is the inductive predicate `StripChain q ν μ`, built from `HorizontalStrip η μ`; the row-length formula is the simp lemma `staircase_rowLen`, stated with truncated natural-number subtraction $m-i$, which is $0$ for $i\ge m$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/StripReduction.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/StripReduction.lean by skeleton subtraction
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
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_RepeatedProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseSign
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedQuotient
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedSupport

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
inductive StripChain : ℕ → YoungDiagram → YoungDiagram → Prop
  | nil (μ) : StripChain 0 μ μ
  | snoc {q ν η μ} : StripChain q ν η → HorizontalStrip η μ → η ≠ μ → StripChain (q+1) ν μ

/- Sweeps remove any prescribed number within the first q-row capacity. -/
@[simp] lemma staircase_rowLen (m i : ℕ) : (staircase m).rowLen i = m-i := by
  have hh : ∀ j, j < (staircase m).rowLen i ↔ j < m-i := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_staircase]
    omega
  have h₁ := hh ((staircase m).rowLen i)
  have h₂ := hh (m-i)
  omega

/- The exact capacity alternative used by the main induction. -/
end Saxl

end

end OAI


