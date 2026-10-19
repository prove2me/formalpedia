-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval
-- name    : OAI_RepresentationTheory_Saxl_HorizontalRemoval
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:35:28.89761+00:00
-- url     : https://prove2.me/theorems/b2f0b5bb-2897-476c-a6b8-9204413cabd1
-- title:
--   Dominance order, interlacing strip removal and row truncation for Young diagrams
-- statement:
--   This file introduces partial row sums and the dominance order on Young diagrams, an operation that removes a horizontal strip from a diagram by shortening its longest columns, and the truncation of a diagram to its first rows. A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both indexed from $0$) that is closed under moving up or to the left; $\mu_i$ denotes the length of row $i$, so $\mu_0\ge\mu_1\ge\cdots$ and $\mu_i=0$ for rows below the diagram.
--
--   1. **Row prefix sums.** For $k\in\mathbb{N}$, $P_\mu(k)=\sum_{i<k}\mu_i$ is the number of cells of $\mu$ in its first $k$ rows.
--   2. **Dominance.** A diagram $\mu$ dominates $\nu$, written $\nu\trianglelefteq\mu$, if
--   $$P_\nu(k)\le P_\mu(k)\qquad\text{for every }k\in\mathbb{N}.$$
--   No equality of sizes is built in; taking $k$ large shows that $\nu\trianglelefteq\mu$ forces $|\nu|\le|\mu|$.
--   3. **Interlacing row lengths.** For $t\in\mathbb{N}$ and a row index $i$, put
--   $$s_{\mu,t}(i)=\max(\mu_i-t,\,0)+\min(t,\mu_{i+1})=\mu_i-\bigl(\min(\mu_i,t)-\min(\mu_{i+1},t)\bigr).$$
--   These numbers interlace with the rows of $\mu$, $\mu_{i+1}\le s_{\mu,t}(i)\le\mu_i$, and are non-increasing in $i$.
--   4. **Strip removal.** $\mu^{(t)}=\{(i,j)\in\mu : j<s_{\mu,t}(i)\}$ is the Young diagram whose row $i$ has length $s_{\mu,t}(i)$. By interlacing, $\mu\setminus\mu^{(t)}$ is a horizontal strip: row $i$ loses $\min(\mu_i,t)-\min(\mu_{i+1},t)$ cells, which is the number of columns among the first $t$ whose lowest cell lies in row $i$. Thus the column lengths of $\mu^{(t)}$ are those of $\mu$ with the $t$ longest columns each shortened by one cell, and $\min(t,\mu_0)$ cells are removed in total. For $t=0$ nothing is removed; for $t\ge\mu_0$ the result has rows $\mu_1,\mu_2,\dots$.
--   5. **Row truncation.** $\mu_{<k}=\{(i,j)\in\mu : i<k\}$ keeps the first $k$ rows of $\mu$.
--
--   Dominance and strip removal are the combinatorial tools for peeling horizontal strips off a Young diagram. They are used to build chains of horizontal strips whose sizes are prescribed by a dominated shape (the sufficiency half of Young's rule) and to reduce diagrams of staircase size by one or more strips in the inductive analysis of the tensor square of the staircase Specht module.
--
--   **Formalization Note** `rowPrefix μ k` is $P_\mu(k)$ and `Dominates μ ν` means that $\mu$ dominates $\nu$ (note the argument order). `stripRow μ t i` is $s_{\mu,t}(i)$, written with truncated natural-number subtraction as `μ.rowLen i - t + min t (μ.rowLen (i+1))`; `stripRemove μ t` is $\mu^{(t)}$ and `rowTruncate μ k` is $\mu_{<k}$. The lemmas `stripRow_bounds`, `stripRow_antitone`, `mem_stripRemove`, `stripRemove_rowLen` and `mem_rowTruncate` record the interlacing bounds, the monotonicity, cell membership and row lengths.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/HorizontalRemoval.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/HorizontalRemoval.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
def rowPrefix (μ : YoungDiagram) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, μ.rowLen i

def Dominates (μ ν : YoungDiagram) : Prop := ∀ k, rowPrefix ν k ≤ rowPrefix μ k

/- Tallest-column bottom deletion, expressed by interlacing rows. -/
def stripRow (μ : YoungDiagram) (t i : ℕ) := μ.rowLen i - t + min t (μ.rowLen (i+1))

lemma stripRow_bounds (μ : YoungDiagram) (t i : ℕ) :
    μ.rowLen (i+1) ≤ stripRow μ t i ∧ stripRow μ t i ≤ μ.rowLen i := by
  have h := μ.rowLen_anti i (i+1) (by omega)
  dsimp [stripRow]
  omega

lemma stripRow_antitone (μ : YoungDiagram) (t : ℕ) : Antitone (stripRow μ t) := by
  intro i j hij
  exact Nat.add_le_add (Nat.sub_le_sub_right (μ.rowLen_anti i j hij) t)
    (min_le_min_left t (μ.rowLen_anti (i+1) (j+1) (by omega)))

def stripRemove (μ : YoungDiagram) (t : ℕ) : YoungDiagram where
  cells := μ.cells.filter (fun x => x.2 < stripRow μ t x.1)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    exact ⟨μ.up_left_mem hxy.1 hxy.2 hy.1,
      lt_of_le_of_lt hxy.2 (lt_of_lt_of_le hy.2 (stripRow_antitone μ t hxy.1))⟩

@[simp] lemma mem_stripRemove {μ : YoungDiagram} {t i j : ℕ} :
    (i,j) ∈ stripRemove μ t ↔ j < stripRow μ t i := by
  change (i,j) ∈ μ.cells.filter _ ↔ _
  simp only [Finset.mem_filter, YoungDiagram.mem_cells]
  exact ⟨And.right, fun h => ⟨YoungDiagram.mem_iff_lt_rowLen.mpr
    (lt_of_lt_of_le h (stripRow_bounds μ t i).2), h⟩⟩

@[simp] lemma stripRemove_rowLen (μ : YoungDiagram) (t i : ℕ) :
    (stripRemove μ t).rowLen i = stripRow μ t i := by
  have hh : ∀ j, j < (stripRemove μ t).rowLen i ↔ j < stripRow μ t i := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_stripRemove]
  have h₁ := hh ((stripRemove μ t).rowLen i)
  have h₂ := hh (stripRow μ t i)
  omega

def rowTruncate (μ : YoungDiagram) (k : ℕ) : YoungDiagram where
  cells := μ.cells.filter (fun x => x.1 < k)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    exact ⟨μ.up_left_mem hxy.1 hxy.2 hy.1, lt_of_le_of_lt hxy.1 hy.2⟩

@[simp] lemma mem_rowTruncate {μ : YoungDiagram} {k i j : ℕ} :
    (i,j) ∈ rowTruncate μ k ↔ (i,j) ∈ μ ∧ i < k := by
  change (i,j) ∈ μ.cells.filter (fun x => x.1 < k) ↔ (i,j) ∈ μ.cells ∧ i < k
  exact Finset.mem_filter

end Saxl

end

end OAI


