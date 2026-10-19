-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
-- name    : OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:42:04.258368+00:00
-- url     : https://prove2.me/theorems/276e20bd-648d-48d0-ad98-6e09f1e850bc
-- title:
--   Induced subgraphs and order-minimal counterexamples
-- statement:
--   Let $r$ be a relation on a finite set $V$.
--
--   1. **Induced subgraph.** For $S\subseteq V$, the restriction of $r$ to $S$.
--   2. **Order-minimal.** $r$ is order-minimal if $|V|\le n$ for every $n\ge1$ and every oriented counterexample $s$ on $\{0,\dots,n-1\}$. A counterexample is a digraph in which every vertex has strictly more first than second neighbours.
--
--   A smallest counterexample in terms of vertex count is the starting point of the proof by contradiction. Its induced proper subgraphs are no longer counterexamples.
--
--   **Formalization Note** `OrderMinimal` does not use the relation $r$ itself, only the cardinality of $V$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/MinimalCounterexample.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/MinimalCounterexample.lean by skeleton subtraction
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

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

def induced (r : V → V → Prop) (S : Finset V) : S → S → Prop :=
  fun x y => r x.val y.val

def OrderMinimal (_r : V → V → Prop) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ s : Fin n → Fin n → Prop,
    IsOriented s → Counterexample s → Fintype.card V ≤ n

end SeymourSecondNeighborhood

end OAI


