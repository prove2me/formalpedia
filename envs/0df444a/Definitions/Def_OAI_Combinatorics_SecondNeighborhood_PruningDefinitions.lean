-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
-- name    : OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:44:57.55098+00:00
-- url     : https://prove2.me/theorems/1ef501a3-9697-4d39-a6d4-d6df037d27f4
-- title:
--   Conflicts, covers and the pruning statement for sets of vertex pairs
-- statement:
--   Let $r$ be a relation on a finite set $V$. Consider finite sets $R,C\subseteq V\times V$ of pairs. A pair $a\in R$ and a pair $b\in C$ conflict if $a_1\to b_1$ and $b_2\to a_2$. A pair $a\in R$ left-covers $z$ if $a_2=z_2$ and $a_1\to z_1$, and $b\in C$ right-covers $z$ if $b_1=z_1$ and $b_2\to z_2$. $Z(R,C)$ is the set of pairs $z$ that are both left-covered by some element of $R$ and right-covered by some element of $C$.
--
--   1. **Images.** The left image of $R$ is the set of pairs left-covered by some element of $R$. The right image of $C$ is the set of pairs right-covered by some element of $C$. A pair is covered by $(R,C)$ if it lies in either image.
--   2. **Doubly covered and hub pairs.** $Z(R,C)$ is as above. $H(R,C)$ is the set of pairs $h$ for which there are $i,j$ with $(h_1,j)\in R$, $(i,h_2)\in C$, $h_1\to i$ and $h_2\to j$.
--   3. **Conflict-free.** No element of $R$ conflicts with an element of $C$. The uncovered part of $Z(R,C)$ relative to $(R',C')$ consists of the $z\in Z(R,C)$ not covered by $(R',C')$.
--   4. **Pruning result.** $(R',C')$ is a pruning of $(R,C)$ if:
--      - $R'\subseteq R$ and $C'\subseteq C$, and $(R',C')$ is conflict-free;
--      - elements of $R$ or $C$ that conflict with nothing are kept;
--      - the deletions are bounded:
--   $$
--   |R\setminus R'|+|C\setminus C'|\le|H(R,C)|+|\{z\in Z(R,C):z\text{ not covered by }(R',C')\}| .
--   $$
--   5. **Pruning statement.** Every pair $(R,C)$ has a pruning.
--
--   Pruning removes all conflicts while deleting few pairs, with the cost charged to hub pairs and to doubly covered pairs that lose their cover. This combinatorial lemma is proved by matching and generic-rank arguments and is the engine of the reduction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/PruningDefinitions.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/PruningDefinitions.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SeymourSecondNeighborhood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

variable {V : Type*}

def Conflict (r : V → V → Prop) (a b : V × V) : Prop :=
  r a.1 b.1 ∧ r b.2 a.2

def LeftCovers (r : V → V → Prop) (a z : V × V) : Prop :=
  a.2 = z.2 ∧ r a.1 z.1

def RightCovers (r : V → V → Prop) (b z : V × V) : Prop :=
  b.1 = z.1 ∧ r b.2 z.2

variable [Fintype V] [DecidableEq V]

noncomputable section

def leftImage (r : V → V → Prop) (R : Finset (V × V)) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun z => ∃ p, (p, z.2) ∈ R ∧ r p z.1)

def rightImage (r : V → V → Prop) (C : Finset (V × V)) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun z => ∃ s, (z.1, s) ∈ C ∧ r s z.2)

def Covered (r : V → V → Prop) (R C : Finset (V × V)) (z : V × V) : Prop :=
  z ∈ leftImage r R ∨ z ∈ rightImage r C

def Z (r : V → V → Prop) (R C : Finset (V × V)) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun z =>
    ∃ p s, (p, z.2) ∈ R ∧ (z.1, s) ∈ C ∧ r p z.1 ∧ r s z.2)

def H (r : V → V → Prop) (R C : Finset (V × V)) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun h =>
    ∃ i j, (h.1, j) ∈ R ∧ (i, h.2) ∈ C ∧ r h.1 i ∧ r h.2 j)

def ConflictFree (r : V → V → Prop) (R C : Finset (V × V)) : Prop :=
  ∀ a ∈ R, ∀ b ∈ C, ¬ Conflict r a b

def uncoveredZ (r : V → V → Prop) (R C R' C' : Finset (V × V)) :
    Finset (V × V) := by
  classical
  exact (Z r R C).filter (fun z => ¬ Covered r R' C' z)

structure PruningResult (r : V → V → Prop) (R C R' C' : Finset (V × V)) : Prop where
  subset_left : R' ⊆ R
  subset_right : C' ⊆ C
  no_conflicts : ConflictFree r R' C'
  retain_left : ∀ a ∈ R, (∀ b ∈ C, ¬ Conflict r a b) → a ∈ R'
  retain_right : ∀ b ∈ C, (∀ a ∈ R, ¬ Conflict r a b) → b ∈ C'
  deletion_bound : (R \ R').card + (C \ C').card ≤
    (H r R C).card + (uncoveredZ r R C R' C').card

def PruningStatement (r : V → V → Prop) : Prop :=
  ∀ R C : Finset (V × V), ∃ R' C', PruningResult r R C R' C'

@[simp] theorem mem_leftImage {r : V → V → Prop} {R : Finset (V × V)}
    {z : V × V} : z ∈ leftImage r R ↔ ∃ p, (p, z.2) ∈ R ∧ r p z.1 := by
  classical
  simp [leftImage]

@[simp] theorem mem_rightImage {r : V → V → Prop} {C : Finset (V × V)}
    {z : V × V} : z ∈ rightImage r C ↔ ∃ s, (z.1, s) ∈ C ∧ r s z.2 := by
  classical
  simp [rightImage]

@[simp] theorem mem_Z {r : V → V → Prop} {R C : Finset (V × V)} {z : V × V} :
    z ∈ Z r R C ↔
      ∃ p s, (p, z.2) ∈ R ∧ (z.1, s) ∈ C ∧ r p z.1 ∧ r s z.2 := by
  classical
  simp [Z]

@[simp] theorem mem_H {r : V → V → Prop} {R C : Finset (V × V)} {h : V × V} :
    h ∈ H r R C ↔
      ∃ i j, (h.1, j) ∈ R ∧ (i, h.2) ∈ C ∧ r h.1 i ∧ r h.2 j := by
  classical
  simp [H]

@[simp] theorem mem_uncoveredZ {r : V → V → Prop}
    {R C R' C' : Finset (V × V)} {z : V × V} :
    z ∈ uncoveredZ r R C R' C' ↔ z ∈ Z r R C ∧ ¬ Covered r R' C' z := by
  classical
  simp only [uncoveredZ, Finset.mem_filter]

@[simp] theorem leftImage_empty (r : V → V → Prop) : leftImage r ∅ = ∅ := by
  classical
  ext z
  simp

@[simp] theorem rightImage_empty (r : V → V → Prop) : rightImage r ∅ = ∅ := by
  classical
  ext z
  simp

end
end SeymourSecondNeighborhood.Pruning

end OAI


