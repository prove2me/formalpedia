-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_DegreeBounds
-- name    : OAI_Probability_ThorpShuffle_DegreeBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T04:04:31.552778+00:00
-- url     : https://prove2.me/theorems/90801f8b-b1d9-4774-b347-f41af96c2c77
-- title:
--   Deleting the first row, orienting a Young diagram, and positivity of Specht degrees
-- statement:
--   This module provides two operations on Young diagrams and the basic lower bound for Specht degrees.
--
--   Let $D$ be a Young diagram, a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) such that $(i,j)\in D$, $i'\le i$ and $j'\le j$ imply $(i',j')\in D$. Let $\lambda_1$ be the length of its first row (row $0$), $\ell$ the length of its first column (the number of rows), and $D^{\mathsf T}=\{(j,i):(i,j)\in D\}$ the conjugate diagram.
--
--   1. *Row tail.* $\mathrm{tail}(D)=\{(i,j)\in\mathbb{N}^2:\ (i+1,j)\in D\}$ is the Young diagram obtained by deleting the first row of $D$ and moving the remaining rows up by one. The map $(i,j)\mapsto(i+1,j)$ is a bijection from the cells of $\mathrm{tail}(D)$ onto $\mathrm{Lower}(D)=\{(i,j)\in D:\ i\ne 0\}$.
--   2. *Orientation.*
--   $$
--   \mathrm{orient}(D)=\begin{cases}D,&\ell\le\lambda_1,\\ D^{\mathsf T},&\ell>\lambda_1,\end{cases}
--   $$
--   and the Boolean $\mathrm{orientation}(D)$ records whether $\ell\le\lambda_1$. Thus $\mathrm{orient}(D)$ is the one of $D$ and $D^{\mathsf T}$ whose first row has length $\max(\lambda_1,\ell)$.
--   3. *Degrees.* For a partition $p$ of $n$, let $D_p$ be its Young diagram and $\deg(p)$ the dimension of its Specht module, the complex span of the $S_n$-translates of the polytabloid of a fixed bijection $\{0,\dots,n-1\}\to D_p$. Let $\mathrm{Ext}(D_p)$ be the set of linear extensions of the cell poset of $D_p$ under the componentwise order, i.e. the standard Young tableaux of shape $D_p$. Then
--   $$
--   |\mathrm{Ext}(D_p)|\le\deg(p)\qquad\text{and}\qquad \deg(p)>0 .
--   $$
--
--   The row tail and the orientation are used to bound the number of partitions $p$ of $n$ whose diagram $D_p$ satisfies $n-\max(\lambda_1,\ell)=u$ by twice the number of partitions of $u$. Positivity of $\deg(p)$ ensures that the terms $1/\deg(p)$ of the reciprocal-degree sums are genuine reciprocals.
--
--   **Formalization Note** The definitions are `rowTail` (with the membership lemma `mem_rowTail`), `rowTailCells : Cells (rowTail D) ≃ Lower D`, `orient`, and `orientation`, which is the `Bool` value `decide (D.colLen 0 ≤ D.rowLen 0)`. Item 3 consists of `extensions_le_degree` and `degree_pos`. Here `degree p` is `Module.finrank ℂ` of the Specht submodule for `canonicalTableau p`, a fixed but non-explicit bijection between `Fin n` and the cells of the diagram.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/DegreeBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/DegreeBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

def rowTail (D : YoungDiagram) : YoungDiagram where
  cells := (D.cells.filter (fun p => p.1 ≠ 0)).image (fun p => (p.1 - 1, p.2))
  isLowerSet := by
    intro y x hxy hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hpD, hp0⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_image.mpr
    refine ⟨(x.1 + 1, x.2), Finset.mem_filter.mpr ⟨?_, by omega⟩, ?_⟩
    · exact D.up_left_mem (by have := hxy.1; omega) hxy.2 hpD
    · simp

lemma mem_rowTail (D : YoungDiagram) (i j : ℕ) : (i, j) ∈ rowTail D ↔ (i + 1, j) ∈ D := by
  change (i, j) ∈ (D.cells.filter (fun p => p.1 ≠ 0)).image (fun p => (p.1 - 1, p.2)) ↔ _
  constructor
  · intro h
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp h
    obtain ⟨hpD, hp0⟩ := Finset.mem_filter.mp hp
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    have hp : p = (i + 1, j) := Prod.ext (by dsimp at h₁; omega) h₂
    simpa only [← hp, YoungDiagram.mem_cells] using hpD
  · intro h
    exact Finset.mem_image.mpr ⟨(i + 1, j), Finset.mem_filter.mpr ⟨h, by omega⟩, by simp⟩

def rowTailCells (D : YoungDiagram) : Cells (rowTail D) ≃ Lower D where
  toFun x := ⟨⟨(x.val.1 + 1, x.val.2), (mem_rowTail D _ _).mp x.property⟩, by simp⟩
  invFun x := ⟨(x.val.val.1 - 1, x.val.val.2), (mem_rowTail D _ _).mpr (by
    have h : x.val.val.1 - 1 + 1 = x.val.val.1 := by have := x.property; omega
    simpa only [h, YoungDiagram.mem_cells, Prod.mk.eta] using x.val.property)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext
    exact Prod.ext (by have := x.property; dsimp; omega) rfl

def orient (D : YoungDiagram) : YoungDiagram :=
  if D.colLen 0 ≤ D.rowLen 0 then D else D.transpose

def orientation (D : YoungDiagram) : Bool := decide (D.colLen 0 ≤ D.rowLen 0)

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
open Thorp.Young

lemma extensions_le_degree {n : ℕ} (p : NShape n) :
    Fintype.card (Extensions (Cells (ofPartition p))) ≤ degree p :=
  extensions_card_le_degree (ofPartition p) (canonicalTableau p)

lemma degree_pos {n : ℕ} (p : NShape n) : 0 < degree p := by
  let := extensions_nonempty (Cells (ofPartition p))
  exact (Fintype.card_pos).trans_le (extensions_le_degree p)

end Thorp.Specht

end

end OAI


