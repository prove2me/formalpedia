-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_GradingShift
-- name    : OAI_Combinatorics_GotsmanLinial_GradingShift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:00:30.208281+00:00
-- url     : https://prove2.me/theorems/7a72519d-abee-493d-b958-29981ec28b95
-- title:
--   Finite-dimensional inner product spaces as Hilbert spaces: setting for degree-shift tridiagonality
-- statement:
--   This definitions bundle introduces no new mathematical objects. It records a single standing convention: every finite-dimensional inner product space $E$ over $\mathbb{K}\in\{\mathbb{R},\mathbb{C}\}$ is complete, hence a Hilbert space, so that the orthogonal projection onto any subspace of $E$ is available. The convention is stated once for a general scalar field $\mathbb{K}$ and once for finite-dimensional complex spaces, where matrices are taken with respect to a finite orthonormal basis.
--
--   This is the setting of the module's results on degree shifts. If $(K_k)_{k\ge0}$ is an increasing flag of subspaces of $E$ and $Q_k$ denotes the orthogonal projection onto the layer $K_{k+1}\cap K_k^{\perp}$, an operator $Z$ with $Z(K_k)\subseteq K_{k+1}$ for all $k$ satisfies $Q_sZQ_r=0$ whenever $r+1<s$, and if $Z$ is also self-adjoint then
--   $$
--   Q_s\,Z\,Q_r=0\qquad\text{whenever } |r-s|\ge2,
--   $$
--   that is, $Z$ is block tridiagonal. On the Boolean cube this applies to multiplication by a coordinate $x_i$, which raises Fourier degree by at most one and commutes with the square-root weight operator, so it is block tridiagonal in the weighted degree grading.
--
--   **Formalization Note** The bundle consists only of local instances `CompleteSpace E` obtained from `FiniteDimensional.complete`, inside otherwise empty sections; the degree-shift lemmas themselves (such as `flagProjection_tridiagonal` and `weightedProjectionMatrix_tridiagonal`) belong to the module but are not part of this bundle.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/GradingShift.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/GradingShift.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_EdgeRecovery
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_WalshDimensions
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_WeightedGrading

namespace OAI

/-!
# A degree shift is tridiagonal in the associated orthogonal grading

These lemmas retain the degree-shift premise explicitly. The cube application
discharges it using coordinate multiplication and the weighted Fourier flag.
-/

noncomputable section

namespace LeanBlast.GotsmanLinial

section FiniteFlag

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

local instance instCompleteSpace_oAI_3 : CompleteSpace E := FiniteDimensional.complete 𝕜 E

end FiniteFlag

section MatrixFlag

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

local instance instCompleteSpace_oAI_4 : CompleteSpace E := FiniteDimensional.complete ℂ E

end MatrixFlag

section WeightedCube

variable {n : ℕ}

end WeightedCube

end LeanBlast.GotsmanLinial

end

end OAI


