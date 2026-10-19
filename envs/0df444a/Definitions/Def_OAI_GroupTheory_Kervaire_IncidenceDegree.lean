-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
-- name    : OAI_GroupTheory_Kervaire_IncidenceDegree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:59:56.578148+00:00
-- url     : https://prove2.me/theorems/b3c08c53-8d56-484a-897e-783a0c7341a9
-- title:
--   Volume forms and Jacobians of the incidence map
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Skew part.** $A\mapsto\frac12(A-A^*)$, the projection onto skew-Hermitian matrices.
--   2. **Tangent volume.** For a basis $b$ of the skew-Hermitian matrices, the top-degree form
--   $$
--   (v_j)_j\mapsto\det{}_b\bigl(\tfrac12(v_j-v_j^*)\bigr)_j .
--   $$
--   3. **Jacobian.** The tangent volume of the horizontal differential of the incidence map at a point, in given bases.
--   4. **Model volume basis.** The image of a horizontal basis under the model differential, a basis of skew matrices.
--
--   Its Jacobian is positive, so the model incidence map is a local diffeomorphism near its preimages of $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/IncidenceDegree.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/IncidenceDegree.lean by skeleton subtraction
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
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy

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
open scoped ContDiff

namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

/-- The ambient projection onto the skew-Hermitian tangent at the identity. -/
def skewPart {I : Type*} [Fintype I] [DecidableEq I] :
    Mat I →ₗ[ℝ] skewAdjoint.submodule ℝ (Mat I) where
  toFun A := ⟨(1/2 : ℝ) • (A-star A), by
    change star ((1/2 : ℝ) • (A-star A)) = -((1/2 : ℝ) • (A-star A))
    simp only [star_smul,star_sub,star_star,star_trivial]
    rw [← neg_sub A (star A),smul_neg]⟩
  map_add' A B := by
    apply Subtype.ext
    change (1/2 : ℝ) • ((A+B)-star (A+B)) =
      (1/2 : ℝ) • (A-star A)+(1/2 : ℝ) • (B-star B)
    rw [star_add]
    module
  map_smul' c A := by
    apply Subtype.ext
    change (1/2 : ℝ) • (c • A-star (c • A)) = c • ((1/2 : ℝ) • (A-star A))
    simp only [star_smul,star_trivial]
    module

@[simp] lemma skewPart_coe {I : Type*} [Fintype I] [DecidableEq I]
    (A : skewAdjoint.submodule ℝ (Mat I)) : skewPart (A : Mat I) = A := by
  apply Subtype.ext
  change (1/2 : ℝ) • ((A : Mat I)-star (A : Mat I)) = A
  rw [A.property]
  module

/-- A constant ambient form restricting to the determinant volume on the unitary tangent. -/
def tangentVolume {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (b : Basis J ℝ (skewAdjoint.submodule ℝ (Mat I))) : Mat I [⋀^J]→L[ℝ] ℝ where
  toAlternatingMap := b.det.compLinearMap skewPart
  cont := by
    change Continuous (fun v : J → Mat I ↦ b.det (fun j ↦ skewPart (v j)))
    simp only [Basis.det_apply]
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun v : J → Mat I ↦ (b.coord i) (skewPart (v j)))
    exact (b.coord i).continuous_of_finiteDimensional.comp
      (skewPart.continuous_of_finiteDimensional.comp (continuous_apply j))

end KervaireIncidenceCurrent

open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator

namespace KervaireUnitaryExponential
variable {A : Type*} [CStarAlgebra A]
local instance instNormedAlgebraRat_oAI : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A

end KervaireUnitaryExponential

namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {J : Type*} [Fintype J] [DecidableEq J]

def jacobian (b : Basis J ℝ (Horizontal K R))
    (c : Basis J ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))))
    (f : ℝ × Mat K → Mat (K ⊕ R)) (t : ℝ) (p : Alg K R) : ℝ :=
  tangentVolume c (fun j ↦ fderiv ℝ (incidence f) (t,p) (0,p*(direction (b j) : Alg K R)))

/-- The determinant volume is normalized by the base point's horizontal frame. -/
def modelVolumeBasis (b : Basis J ℝ (Horizontal K R)) :
    Basis J ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))) :=
  b.map (modelHorizontalEquiv 1 1)

end KervaireIncidenceCurrent

end

end OAI


