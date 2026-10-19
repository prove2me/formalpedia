-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
-- name    : OAI_Combinatorics_SecondNeighborhood_Deletion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:42:34.308484+00:00
-- url     : https://prove2.me/theorems/719bc8ea-49ba-4db9-8799-b54fd4dd1c53
-- title:
--   The deficit potential of a pair of vertex sets
-- statement:
--   Let $r$ be a relation on a finite set $V$, with out-image $r(\cdot)$. For $S,T\subseteq V$ define
--   $$
--   \Phi(S,T)=\Bigl|\,r(T)\setminus\bigl((r(S)\cap S)\cup T\bigr)\Bigr| .
--   $$
--   In particular $\Phi(S,\emptyset)=0$.
--
--   This potential counts out-neighbours of $T$ outside $T$ and outside the part of $S$ that $S$ reaches. It is used to track how deleting arcs or vertices affects second neighbourhoods in a minimal counterexample.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/Deletion.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/Deletion.lean by skeleton subtraction
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

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def deficitPotential (r : V → V → Prop) (S T : Finset V) : ℕ :=
  (image r T \ ((image r S ∩ S) ∪ T)).card

@[simp] theorem deficitPotential_empty (r : V → V → Prop) (S : Finset V) :
    deficitPotential r S ∅ = 0 := by
  classical
  simp [deficitPotential]

end SeymourSecondNeighborhood

end OAI


