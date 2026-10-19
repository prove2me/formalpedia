-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalImages
-- name    : OAI_Combinatorics_SecondNeighborhood_ExtremalImages
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:01:16.861239+00:00
-- url     : https://prove2.me/theorems/2cc0604d-998c-4543-a76a-96941654400a
-- title:
--   The diagonal, rows and columns of a set of vertex pairs
-- statement:
--   Let $V$ be a finite set and $r$ a relation on $V$, with out-image $r(S)$ of a set $S$.
--
--   1. **Diagonal.** $\Delta=\{(v,v):v\in V\}$.
--   2. **Columns and rows.** For $P\subseteq V\times V$ and $j\in V$, the column is $P^{(j)}=\{p:(p,j)\in P\}$; for $Q$ and $i$, the row is $Q_{(i)}=\{s:(i,s)\in Q\}$.
--   3. **Images act on columns and rows.** The left image of $P$ (pairs $z$ with $(p,z_2)\in P$ and $p\to z_1$) has columns $r(P^{(j)})$, and the right image of $Q$ has rows $r(Q_{(i)})$:
--   $$
--   \bigl(\mathrm{left}(P)\bigr)^{(j)}=r\bigl(P^{(j)}\bigr),\qquad \bigl(\mathrm{right}(Q)\bigr)_{(i)}=r\bigl(Q_{(i)}\bigr).
--   $$
--
--   Viewing a pair set column by column reduces statements about left images to statements about out-images of vertex sets, where the second neighbourhood counting applies.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/ExtremalImages.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/ExtremalImages.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRank
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMaps
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelRestriction
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MaxSupportKernel
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelConflict
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankCoefficients
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMapsPolynomial
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankGlobalMinors
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelBasisLifts

namespace OAI

namespace SeymourSecondNeighborhood.Extremal

open Pruning
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

def diagonal : Finset (V × V) :=
  Finset.univ.filter (fun z => z.1 = z.2)

def column (P : Finset (V × V)) (j : V) : Finset V :=
  Finset.univ.filter (fun p => (p, j) ∈ P)

def row (Q : Finset (V × V)) (i : V) : Finset V :=
  Finset.univ.filter (fun s => (i, s) ∈ Q)

@[simp] theorem mem_diagonal {z : V × V} :
    z ∈ diagonal ↔ z.1 = z.2 := by
  simp [diagonal]

@[simp] theorem diagonal_mem (v : V) : (v, v) ∈ (diagonal : Finset (V × V)) := by
  exact mem_diagonal.mpr rfl

@[simp] theorem mem_column {P : Finset (V × V)} {j p : V} :
    p ∈ column P j ↔ (p, j) ∈ P := by
  simp [column]

@[simp] theorem mem_row {Q : Finset (V × V)} {i s : V} :
    s ∈ row Q i ↔ (i, s) ∈ Q := by
  simp [row]

@[simp] theorem column_leftImage (r : V → V → Prop) (P : Finset (V × V)) (j : V) :
    column (leftImage r P) j = image r (column P j) := by
  classical
  ext i
  simp

@[simp] theorem row_rightImage (r : V → V → Prop) (Q : Finset (V × V)) (i : V) :
    row (rightImage r Q) i = image r (row Q i) := by
  classical
  ext j
  simp

end
end SeymourSecondNeighborhood.Extremal

end OAI


