-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
-- name    : OAI_GroupTheory_Kervaire_IncidenceTangent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:56:01.947879+00:00
-- url     : https://prove2.me/theorems/d123b424-1c51-4e2e-bc62-a3819fd9d360
-- title:
--   Horizontal differentials of the incidence map
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Horizontal input.** At a point $p$ of the algebra, the linear map $h\mapsto(0,\,p\cdot\mathrm{direction}(h))$ from the horizontal space to $\mathbb R\times$ algebra, the right-invariant directions at $p$.
--   2. **Horizontal differential.** The derivative of the incidence map at $(t,p)$ restricted to these directions.
--   3. **Skew blocks.** The diagonal blocks of a skew-Hermitian $(K\sqcup R)$-matrix.
--   4. **Degree derivative.** For $\varepsilon\in\mathbb R$, the linear map
--   $$
--   (A,B,Z)\mapsto\begin{pmatrix}\varepsilon A&2Z^*\\-2Z&-B\end{pmatrix}
--   $$
--   into skew-Hermitian matrices. It is a linear isomorphism for $\varepsilon\ne0$, with an explicit inverse.
--
--   It is the differential of the model incidence map in suitable coordinates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/IncidenceTangent.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/IncidenceTangent.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Kervaire mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder

namespace KervaireIncidenceCurrent

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
def horizontalInput (p : Alg K R) : Horizontal K R →ₗ[ℝ] (ℝ × Alg K R) where
  toFun h := (0,p*(direction h : Alg K R))
  map_add' h g := by
    change (0,p*(direction (h+g) : Alg K R)) = _
    rw [map_add]
    change ((0 : ℝ),p*((direction h : Alg K R)+(direction g : Alg K R))) =
      (0,p*(direction h : Alg K R))+(0,p*(direction g : Alg K R))
    rw [mul_add]
    exact Prod.ext (zero_add 0).symm rfl
  map_smul' c h := by
    change (0,p*(direction (c • h) : Alg K R)) = _
    rw [map_smul]
    change ((0 : ℝ),p*(c • (direction h : Alg K R))) = c • (0,p*(direction h : Alg K R))
    rw [mul_smul_comm]
    simp only [Prod.smul_mk,smul_zero]

def horizontalDifferential (f : ℝ × Mat K → Mat (K ⊕ R)) (t : ℝ) (p : Alg K R) :
    Horizontal K R →ₗ[ℝ] Mat (K ⊕ R) :=
  (fderiv ℝ (incidence f) (t,p)).toLinearMap.comp (horizontalInput p)

end
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))

end KervaireIncidenceCurrent

namespace KervaireFixedSpace
open Matrix
variable {K R : Type*}
abbrev Skew (K : Type*) := skewAdjoint (Matrix K K ℂ)

/-- Entrywise skew-Hermitian symmetry. -/
theorem skew_entry (T : Skew K) (i j : K) : star (T.val j i) = -T.val i j := by
  exact congrFun (congrFun T.property i) j

/-- The first diagonal block of a skew-Hermitian matrix. -/
def skewBlock11 (T : Skew (K ⊕ R)) : Skew K :=
  ⟨T.val.toBlocks₁₁, by
    ext i j
    exact skew_entry T (Sum.inl i) (Sum.inl j)⟩

/-- The second diagonal block of a skew-Hermitian matrix. -/
def skewBlock22 (T : Skew (K ⊕ R)) : Skew R :=
  ⟨T.val.toBlocks₂₂, by
    ext i j
    exact skew_entry T (Sum.inr i) (Sum.inr j)⟩

/-- The block formula for the incidence derivative. -/
def derivativeMatrix (ε : ℝ) (A : Skew K) (B : Skew R) (Z : Matrix R K ℂ) :
    Matrix (K ⊕ R) (K ⊕ R) ℂ :=
  fromBlocks (ε • A.val) ((2 : ℝ) • Zᴴ) ((-2 : ℝ) • Z) (-B.val)

theorem derivativeMatrix_skew (ε : ℝ) (A : Skew K) (B : Skew R) (Z : Matrix R K ℂ) :
    derivativeMatrix ε A B Z ∈ skewAdjoint (Matrix (K ⊕ R) (K ⊕ R) ℂ) := by
  change star (derivativeMatrix ε A B Z) = -derivativeMatrix ε A B Z
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [derivativeMatrix, Matrix.star_apply, Matrix.fromBlocks, skew_entry]
  · simp [derivativeMatrix, Matrix.star_apply, Matrix.fromBlocks]
  · simp [derivativeMatrix, Matrix.star_apply, Matrix.fromBlocks]
  · simp [derivativeMatrix, Matrix.star_apply, Matrix.fromBlocks, skew_entry]

def degreeDerivative (ε : ℝ) : (Skew K × Skew R × Matrix R K ℂ) →ₗ[ℝ] Skew (K ⊕ R) where
  toFun v := ⟨derivativeMatrix ε v.1 v.2.1 v.2.2,
    derivativeMatrix_skew ε v.1 v.2.1 v.2.2⟩
  map_add' v w := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [derivativeMatrix, Matrix.fromBlocks, smul_add]; abel
  map_smul' c v := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [derivativeMatrix, Matrix.fromBlocks, smul_comm ε c, smul_comm (2 : ℝ) c,
        smul_comm (-2 : ℝ) c]

/-- Explicit inverse coordinates of the differential; no finite-dimensional
or genericity assumption is needed for this algebraic step. -/
def inverseDerivative (ε : ℝ) (T : Skew (K ⊕ R)) : Skew K × Skew R × Matrix R K ℂ :=
  (ε⁻¹ • skewBlock11 T, -skewBlock22 T, (-((2 : ℝ)⁻¹)) • T.val.toBlocks₂₁)

theorem degreeDerivative_inverse (ε : ℝ) (hε : ε ≠ 0) (T : Skew (K ⊕ R)) :
    degreeDerivative ε (inverseDerivative ε T) = T := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [degreeDerivative, inverseDerivative, derivativeMatrix, skewBlock11,
      Matrix.fromBlocks, Matrix.toBlocks₁₁, smul_smul, hε]
  · simp [degreeDerivative, inverseDerivative, derivativeMatrix, Matrix.fromBlocks,
      Matrix.toBlocks₂₁, smul_smul, skew_entry]
  · simp [degreeDerivative, inverseDerivative, derivativeMatrix, Matrix.fromBlocks,
      Matrix.toBlocks₂₁, smul_smul]
  · simp [degreeDerivative, inverseDerivative, derivativeMatrix, skewBlock22,
      Matrix.fromBlocks, Matrix.toBlocks₂₂]

theorem inverse_degreeDerivative (ε : ℝ) (hε : ε ≠ 0) (v : Skew K × Skew R × Matrix R K ℂ) :
    inverseDerivative ε (degreeDerivative ε v) = v := by
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    simp [inverseDerivative, degreeDerivative, derivativeMatrix, skewBlock11,
      Matrix.toBlocks₁₁, Matrix.fromBlocks, hε]
  · apply Prod.ext
    · apply Subtype.ext
      ext i j
      simp [inverseDerivative, degreeDerivative, derivativeMatrix, skewBlock22,
        Matrix.toBlocks₂₂, Matrix.fromBlocks]
    · ext i j
      simp [inverseDerivative, degreeDerivative, derivativeMatrix, Matrix.toBlocks₂₁,
        Matrix.fromBlocks]

/-- The differential at the regular fiber is a real-linear isomorphism. -/
def degreeDerivativeEquiv (ε : ℝ) (hε : ε ≠ 0) :
    (Skew K × Skew R × Matrix R K ℂ) ≃ₗ[ℝ] Skew (K ⊕ R) :=
  { degreeDerivative ε with
    invFun := inverseDerivative ε
    left_inv := inverse_degreeDerivative ε hε
    right_inv := degreeDerivative_inverse ε hε }

end KervaireFixedSpace
namespace KervaireIncidenceCurrent
open MeasureTheory
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))
  [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))]
  {μ : Measure (unitary (Alg K R))} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

end KervaireIncidenceCurrent

end

end OAI


