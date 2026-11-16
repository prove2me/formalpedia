-- Prove2me | Definitions.Def_TangleStructTree_Supplement_GraphSep
-- name    : TangleStructTree_Supplement_GraphSep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:08:36.576384+00:00
-- url     : https://prove2.me/theorems/16e848d9-86e2-4cb8-8200-b5b0dff6734e
-- title:
--   Separations of a finite graph, their order and their usual order function
-- statement:
--   Let $G$ be a finite graph with vertex set $V$. A **separation** of $G$ is a pair $(A,B)$ of vertex sets with $A\cup B=V$ and no edge between $A\setminus B$ and $B\setminus A$. The separations form a separation system with
--
--   $$(A',B')\le(A,B)\iff A'\supseteq A\ \text{and}\ B'\subseteq B,\qquad (A,B)^*=(B,A),$$
--
--   and the **usual order function** is $|(A,B)|:=|A\cap B|$.
--
--   This is the separation system of the block application (Theorem 7.1).
--
--   **Formalization Note** The separation property is the published definition `RobertsonSeymour1986_GM5_IsSeparation`. The order is the paper's (footnote 24), the inverse of the order in [11]: an orientation $(A,B)$ points towards $B$.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §7, p.21 (PDF 32); footnote 24, p.22 (PDF 33)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_RobertsonSeymour1986_GM5_IsSeparation

namespace TangleStructTree

namespace Supplement

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The oriented **separations of a graph** `G`: pairs `(A, B)` of vertex sets with `A ∪ B = V` and no
edge between `A ∖ B` and `B ∖ A` ([11], adopted by von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §7, p.21 (PDF 32)).

**Formalization Note** `G` is a finite simple graph (`[Fintype V]`), the convention of [11] that
the paper adopts (§3, p.6). The separation property is the platform definition
`RobertsonSeymour1986.GM5.IsSeparation`. -/
def GraphSep (G : SimpleGraph V) : Type :=
  {p : Finset V × Finset V // RobertsonSeymour1986.GM5.IsSeparation G p.1 p.2}

/-- The partial order on separations of a graph (footnote 24, journal version p.22 (PDF 33)):
"`(A′, B′) ≤ (A, B)` if and only if `A′ ⊇ A` and `B′ ⊆ B`". This is the paper's order, the inverse
of that of [11] (footnote 5). -/
instance instPartialOrderGraphSep (G : SimpleGraph V) : PartialOrder (GraphSep G) where
  le a b := b.1.1 ⊆ a.1.1 ∧ a.1.2 ⊆ b.1.2
  le_refl a := ⟨subset_rfl, subset_rfl⟩
  le_trans a b c hab hbc := ⟨hbc.1.trans hab.1, hab.2.trans hbc.2⟩
  le_antisymm a b hab hba :=
    Subtype.ext (Prod.ext (Finset.Subset.antisymm hba.1 hab.1) (Finset.Subset.antisymm hab.2 hba.2))

/-- The involution `(A, B)∗ = (B, A)`. -/
instance instSepSystemGraphSep (G : SimpleGraph V) : SepSystem (GraphSep G) where
  rev a := ⟨(a.1.2, a.1.1), by
    obtain ⟨hU, hE⟩ := a.2
    refine ⟨by rw [Finset.union_comm]; exact hU, fun x hx y hy hxy => hE y hy x hx hxy.symm⟩⟩
  rev_rev a := rfl
  rev_le_rev a b h := ⟨h.2, h.1⟩

/-- The usual order function of [11]: `|(A, B)| := |A ∩ B|` (journal version, §7, p.21 (PDF 32)). -/
def sepOrder (G : SimpleGraph V) (a : GraphSep G) : ℝ :=
  ((a.1.1 ∩ a.1.2).card : ℝ)

end Supplement

end TangleStructTree


