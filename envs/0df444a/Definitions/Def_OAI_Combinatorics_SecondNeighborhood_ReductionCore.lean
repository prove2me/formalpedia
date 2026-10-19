-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
-- name    : OAI_Combinatorics_SecondNeighborhood_ReductionCore
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:40:56.421075+00:00
-- url     : https://prove2.me/theorems/4d5f33aa-d6f3-49c9-9228-dd6ca136b7c6
-- title:
--   Counterexamples, arc-minimality and expansion properties for the second neighbourhood conjecture
-- statement:
--   Let $V$ be a finite set and $r$ a relation on $V$, read as a directed graph with an arc $x\to y$ when $r(x,y)$. It is oriented if it has no loops and no pair of opposite arcs. $N^+(v)=\{w:v\to w\}$ is the first (out-)neighbourhood, and $N^{++}(v)$ is the second neighbourhood: the vertices $w\ne v$ with $w\notin N^+(v)$ that are reached by a path $v\to u\to w$. $r(S)$ denotes the out-image of a vertex set $S$.
--
--   1. **Counterexample.** Every vertex satisfies $|N^{++}(v)|<|N^+(v)|$.
--   2. **Arc set and arc-minimality.** $\mathrm{arcs}(r)=\{(x,y):x\to y\}$. A relation $r$ is arc-minimal if every oriented counterexample $s$ on $V$ has at least as many arcs as $r$.
--   3. **Set expansion properties.** These quantify over nonempty proper subsets $S\subsetneq V$:
--      - *nonempty boundary*: $r(S)\setminus S\ne\emptyset$;
--      - *subset deficit*: $|r(r(S))\setminus r(S)|<|r(S)\setminus S|$;
--      - *strict subset growth*: $|S|+|r(r(S))|<2|r(S)|$.
--   4. **Positive in-degree.** Every vertex has an in-neighbour.
--
--   These are the structural properties that a minimal counterexample is shown to satisfy. Together they are contradictory, which proves the conjecture.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/ReductionCore.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/ReductionCore.lean by skeleton subtraction
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

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

def Counterexample (r : V → V → Prop) : Prop :=
  ∀ v, (secondNeighbors r v).card < (firstNeighbors r v).card

noncomputable def arcSet (r : V → V → Prop) : Finset (V × V) := by
  classical
  exact Finset.univ.filter fun p => r p.1 p.2

def ArcMinimal (r : V → V → Prop) : Prop :=
  ∀ s : V → V → Prop, IsOriented s → Counterexample s →
    (arcSet r).card ≤ (arcSet s).card

def NonemptyBoundary (r : V → V → Prop) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    (image r S \ S).Nonempty

def SubsetDeficit (r : V → V → Prop) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    (image r (image r S) \ image r S).card < (image r S \ S).card

def PositiveIndegree (r : V → V → Prop) : Prop :=
  ∀ v, ∃ u, r u v

def StrictSubsetGrowth (r : V → V → Prop) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    S.card + (image r (image r S)).card < 2 * (image r S).card

omit [DecidableEq V] in
@[simp] theorem mem_arcSet {r : V → V → Prop} {p : V × V} :
    p ∈ arcSet r ↔ r p.1 p.2 := by
  classical
  simp [arcSet]

end SeymourSecondNeighborhood

end OAI


