-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_EdgeRecovery
-- name    : OAI_Combinatorics_GotsmanLinial_EdgeRecovery
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:47:58.591859+00:00
-- url     : https://prove2.me/theorems/3c787e96-9683-444e-af2c-23664cd56cd6
-- title:
--   Distance shells: level sets of a natural-number-valued distance
-- statement:
--   Let $A$ be a finite set and $\rho:A\to\mathbb{N}$ any function, thought of as a distance attached to each element of $A$. For $k\in\mathbb{N}$, the distance shell of level $k$ is
--
--   $$
--   \mathrm{Sh}_k(\rho)=\{a\in A:\rho(a)=k\},
--   $$
--
--   so $a\in\mathrm{Sh}_k(\rho)$ exactly when $\rho(a)=k$, and $A$ is the disjoint union of the shells $\mathrm{Sh}_0(\rho),\mathrm{Sh}_1(\rho),\dots$
--
--   In the edge-recovery step of the Gotsman–Linial argument, $A$ is the set of ordered pairs $(x,y)$ of vertices of the Boolean cube and $\rho(x,y)$ is their Hamming distance: shell $0$ is the diagonal and shell $1$ is the set of ordered cube edges. Splitting a weighted sum over pairs, such as the squared entries of a matrix, by shells separates the diagonal mass and the edge mass from the contribution of more distant pairs.
--
--   **Formalization Note** The definition is `distanceShell d k`, a `Finset` obtained by filtering the finite type; `mem_distanceShell` is its membership rule.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/EdgeRecovery.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/EdgeRecovery.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GotsmanLinial mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_SignParity

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Recovering constant-sign edges from grading energy

The counting argument is separated from construction of the grading matrix.
Its hypotheses are explicit entrywise, total-energy, and distance-energy facts.
No edge-count or anticommutator conclusion is assumed.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- A finite distance layer, also useful for weights indexed by ordered pairs. -/
def distanceShell (d : α → ℕ) (k : ℕ) : Finset α :=
  Finset.univ.filter fun a => d a = k

@[simp] theorem mem_distanceShell (d : α → ℕ) (k : ℕ) (a : α) :
    a ∈ distanceShell d k ↔ d a = k := by
  simp [distanceShell]

end LeanBlast.GotsmanLinial

end OAI


