-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
-- name    : OAI_GroupTheory_Kervaire_UnitaryHomotopy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:57:44.355874+00:00
-- url     : https://prove2.me/theorems/c51abb75-4b95-4048-bcfc-ad767366df56
-- title:
--   Unitary maps, homotopies and currents
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Unitary maps.** Smooth maps between matrix algebras sending unitaries to unitaries.
--   2. **Homotopy.** Two such maps are elementarily homotopic if a smooth family through unitary maps joins them. Homotopy is the generated equivalence relation.
--   3. **Current.** For horizontal vectors $b_1,\dots,b_n$ and an $n$-form $\omega$, the Haar integral
--   $$
--   \int_{U}\omega\bigl(\mathrm{inc}_F(0,p)\bigr)\Bigl(d\,\mathrm{inc}_F\bigl(p\,\mathrm{dir}(b_1)\bigr),\dots,d\,\mathrm{inc}_F\bigl(p\,\mathrm{dir}(b_n)\bigr)\Bigr)\,dp
--   $$
--   over the unitary group $U$ of the algebra.
--   4. **Model and gauge.** The model $X\mapsto\mathrm{diag}(X,-1)$, conjugation of skew matrices by a unitary, and the gauge frame $\mathrm{diag}(U,V)$. The model's horizontal differential is identified with skew-Hermitian matrices.
--
--   Currents of homotopic maps agree, which is the homotopy invariance of degree.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/UnitaryHomotopy.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/UnitaryHomotopy.lean by skeleton subtraction
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

namespace KervaireUnitaryHomotopy
variable (B C : Type*) [CStarAlgebra B] [CStarAlgebra C]

/-- A smooth ambient representative of a smooth unitary-valued map. -/
structure UMap where
  toFun : B → C
  smooth : ContDiff ℝ ∞ toFun
  unitary : ∀ x : unitary B, toFun (x : B) ∈ unitary C

instance : CoeFun (UMap B C) (fun _ ↦ B → C) := ⟨UMap.toFun⟩

variable {B C}

/-- Elementary smooth homotopy; equalities only concern the unitary domain. -/
def Elementary (F G : UMap B C) : Prop :=
  ∃ H : ℝ × B → C, ContDiff ℝ ∞ H ∧
    (∀ t (x : unitary B), H (t,(x : B)) ∈ unitary C) ∧
    (∀ x : unitary B, H (0,(x : B)) = F x) ∧
    (∀ x : unitary B, H (1,(x : B)) = G x)

/-- Finite chains suffice, so no smooth concatenation theorem is assumed. -/
def Homotopic (F G : UMap B C) : Prop := Relation.EqvGen Elementary F G

section Differential
variable {E D : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]
  [StarRing E] [ContinuousStar E] [StarModule ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
local instance instNormedAlgebraRat_oAI : NormedAlgebra ℚ E := .restrictScalars ℚ ℝ E

end Differential

end KervaireUnitaryHomotopy

namespace KervaireIncidenceCurrent

section
open MeasureTheory KervaireUnitaryHomotopy
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))
  [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))]
  {μ : Measure (unitary (Alg K R))} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

/-- An ambient representative independent of the time coordinate. -/
def timeless (F : UMap (Mat K) (Mat (K ⊕ R))) : ℝ × Mat K → Mat (K ⊕ R) :=
  fun p ↦ F p.2

/-- The compact horizontal current evaluated on a smooth unitary map. -/
def current {n : ℕ} (b : Fin n → Horizontal K R)
    (form : Mat (K ⊕ R) → Mat (K ⊕ R) [⋀^Fin n]→L[ℝ] ℝ)
    (F : UMap (Mat K) (Mat (K ⊕ R))) : ℝ :=
  ∫ p : unitary (Alg K R), form (incidence (timeless F) (0,(p : Alg K R)))
    (fun i ↦ fderiv ℝ (incidence (timeless F)) (0,(p : Alg K R))
      (0,(p : Alg K R)*(direction (b i) : Alg K R))) ∂μ

end

variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

def model : ℝ × Mat K → Mat (K ⊕ R) := fun p ↦ diag p.2 (-1)

/-- Conjugation is a real linear automorphism of the skew-Hermitian space. -/
def skewConj (U : unitary (Mat K)) :
    skewAdjoint.submodule ℝ (Mat K) ≃ₗ[ℝ] skewAdjoint.submodule ℝ (Mat K) where
  toFun A := ⟨star (U : Mat K)*(A : Mat K)*U, by
    change star (star (U : Mat K)*(A : Mat K)*U) = -_
    rw [star_mul,star_mul,star_star,A.property]
    simp [mul_assoc]⟩
  invFun A := ⟨(U : Mat K)*(A : Mat K)*star (U : Mat K), by
    change star ((U : Mat K)*(A : Mat K)*star (U : Mat K)) = -_
    rw [star_mul,star_mul,star_star,A.property]
    simp [mul_assoc]⟩
  left_inv A := by
    apply Subtype.ext
    change (U : Mat K)*(star (U : Mat K)*(A : Mat K)*U)*star (U : Mat K) = A
    simp only [mul_assoc, U.property.2, mul_one]
    rw [← mul_assoc,U.property.2,one_mul]
  right_inv A := by
    apply Subtype.ext
    change star (U : Mat K)*((U : Mat K)*(A : Mat K)*star (U : Mat K))*U = A
    simp only [mul_assoc,U.property.1,mul_one]
    rw [← mul_assoc,U.property.1,one_mul]
  map_add' A B := by apply Subtype.ext; simp [mul_add,add_mul]
  map_smul' c A := by apply Subtype.ext; simp

def gaugeFrame (U : unitary (Mat K)) (V : unitary (Mat R)) : unitary (Mat (K ⊕ R)) :=
  ⟨diag (U : Mat K) (V : Mat R),diag_unitary U.property V.property⟩

def gaugePoint (U : unitary (Mat K)) (V : unitary (Mat R)) : unitary (Alg K R) :=
  ⟨(1,(gaugeFrame U V : Mat (K ⊕ R)),-1), by
    constructor <;> apply Prod.ext
    · simp
    · exact Prod.ext (gaugeFrame U V).property.1 (by simp)
    · simp
    · exact Prod.ext (gaugeFrame U V).property.2 (by simp)⟩

def modelHorizontalEquiv (U : unitary (Mat K)) (V : unitary (Mat R)) :
    Horizontal K R ≃ₗ[ℝ] skewAdjoint.submodule ℝ (Mat (K ⊕ R)) :=
  ((skewConj U).prodCongr (LinearEquiv.refl ℝ _)) |>.trans
    ((KervaireFixedSpace.degreeDerivativeEquiv (K := K) (R := R) 1 one_ne_zero).trans
      (skewConj (star (gaugeFrame U V))))

end KervaireIncidenceCurrent

end

end OAI


