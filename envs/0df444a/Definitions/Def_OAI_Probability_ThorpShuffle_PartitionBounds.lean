-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds
-- name    : OAI_Probability_ThorpShuffle_PartitionBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T04:03:43.28627+00:00
-- url     : https://prove2.me/theorems/47727800-8ec1-4d17-9e22-1333b2543830
-- title:
--   The Young diagram formed by an order ideal of cells
-- statement:
--   This module turns an order ideal of the cells of a Young diagram into a Young diagram in its own right.
--
--   Let $D$ be a Young diagram, a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) such that $(i,j)\in D$, $i'\le i$ and $j'\le j$ imply $(i',j')\in D$. Order its cells componentwise: $(i',j')\le(i,j)$ iff $i'\le i$ and $j'\le j$. Let $s\subseteq D$ be an order ideal (lower set) of this poset: if $y\in s$, $x\in D$ and $x\le y$, then $x\in s$.
--
--   1. *Ideal diagram.* $D|_s$ is the Young diagram whose set of cells is $s$ itself, viewed as a subset of $\mathbb{N}^2$; it is a Young diagram because $D$ is down-closed in $\mathbb{N}^2$ and $s$ is down-closed in $D$.
--   2. *Membership.* For every $p\in\mathbb{N}^2$,
--   $$
--   p\in D|_s\iff p\in D\ \text{and}\ p\in s .
--   $$
--   3. *Cells.* The identity of $\mathbb{N}^2$ induces an order isomorphism between the cell poset of $D|_s$ and $s$ with the order inherited from $D$.
--
--   The construction is used to trim a Young diagram to an order ideal of its cells, for instance the first row together with part of the cells below it, without increasing the number of linear extensions (standard Young tableaux). Lower bounds on linear extensions proved for the trimmed diagram therefore transfer back to $D$, and from there to Specht degrees.
--
--   **Formalization Note** `idealDiagram D s hs` takes the proof `hs : IsLowerSet s` as an argument, and its cell set is the image of `s` under the inclusion of `Cells D` into pairs of natural numbers. Item 2 is `mem_idealDiagram` and item 3 is `idealCells : Cells (idealDiagram D s hs) ≃o s`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/PartitionBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/PartitionBounds.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

def idealDiagram (D : YoungDiagram) (s : Set (Cells D)) (hs : IsLowerSet s) : YoungDiagram where
  cells := (Finset.univ.filter (· ∈ s)).image Subtype.val
  isLowerSet := by
    intro y x hxy hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
    have hyD : y ∈ D := by rw [← hzy]; exact z.property
    have hxD : x ∈ D := D.isLowerSet hxy hyD
    refine Finset.mem_image.mpr ⟨⟨x, hxD⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    apply hs (show (⟨x, hxD⟩ : Cells D) ≤ z from by change x ≤ z.val; rwa [hzy])
    exact (Finset.mem_filter.mp hz).2

lemma mem_idealDiagram (D : YoungDiagram) (s : Set (Cells D)) (hs : IsLowerSet s) (p : ℕ × ℕ) :
    p ∈ idealDiagram D s hs ↔ ∃ h : p ∈ D, (⟨p, h⟩ : Cells D) ∈ s := by
  constructor
  · intro hp
    obtain ⟨x, hx, hxp⟩ := Finset.mem_image.mp hp
    subst p
    exact ⟨x.property, (Finset.mem_filter.mp hx).2⟩
  · rintro ⟨h, hp⟩
    exact Finset.mem_image.mpr ⟨⟨p, h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩

def idealCells (D : YoungDiagram) (s : Set (Cells D)) (hs : IsLowerSet s) :
    Cells (idealDiagram D s hs) ≃o s where
  toFun x := ⟨⟨x.val, (mem_idealDiagram D s hs x.val).mp x.property |>.choose⟩,
    (mem_idealDiagram D s hs x.val).mp x.property |>.choose_spec⟩
  invFun x := ⟨x.val.val, (mem_idealDiagram D s hs x.val.val).mpr ⟨x.val.property, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end Thorp.Young

namespace Thorp.Young
open scoped Classical

end Thorp.Young

namespace Thorp.Young
open scoped Classical

end Thorp.Young

end

end OAI


