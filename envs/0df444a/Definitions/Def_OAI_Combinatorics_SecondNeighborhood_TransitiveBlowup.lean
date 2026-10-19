-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
-- name    : OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:43:13.860524+00:00
-- url     : https://prove2.me/theorems/22435cc2-bc8a-49a2-8a8e-012c81daeff5
-- title:
--   The transitive blow-up of a digraph
-- statement:
--   Let $r$ be a relation on $V$ and $m\in\mathbb{N}$. The blow-up is the relation on $V\times\{0,\dots,m-1\}$ given by
--   $$
--   (x,i)\to(y,j)\iff r(x,y)\ \text{ or }\ \bigl(x=y\ \text{and}\ i<j\bigr).
--   $$
--   Each vertex is replaced by a transitive tournament on $m$ copies, and arcs of $r$ are copied between all copies.
--
--   Blow-ups multiply neighbourhood sizes in a controlled way. They are used to rescale counterexamples so that ratios of neighbourhood sizes can be compared with integers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/TransitiveBlowup.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/TransitiveBlowup.lean by skeleton subtraction
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

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*}

def blowup (r : V → V → Prop) (m : ℕ) : (V × Fin m) → (V × Fin m) → Prop :=
  fun p q => r p.1 q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

variable [Fintype V] [DecidableEq V]

end SeymourSecondNeighborhood

end OAI


