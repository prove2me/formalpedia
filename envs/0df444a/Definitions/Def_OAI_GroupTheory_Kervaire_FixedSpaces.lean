-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
-- name    : OAI_GroupTheory_Kervaire_FixedSpaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:17:50.320991+00:00
-- url     : https://prove2.me/theorems/ce1b419a-9b57-4740-90d4-b11cf6d90673
-- title:
--   Fixed spaces of unitary matrices
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Fixed space and dimension.** For a square matrix $M$, the kernel of $M-1$ and its dimension $\dim\mathrm{Fix}(M)$.
--   2. **Reindexing.** A unitary matrix transported along a bijection of indices.
--   3. **Doubling.** For unitaries $D,P$, the linear map
--   $$
--   \mathrm{Fix}(DP)\times\mathrm{Fix}(DP)\to\mathrm{Fix}\Bigl(\begin{pmatrix}0&D\\D^*&0\end{pmatrix}\begin{pmatrix}0&P^*\\P&0\end{pmatrix}\Bigr),\qquad(v,w)\mapsto(v,D^*w).
--   $$
--   It doubles fixed dimensions.
--
--   Large fixed spaces of the mixed operator force its phase to be small, which feeds the boundary inequalities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/FixedSpaces.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/FixedSpaces.lean by skeleton subtraction
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
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence

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
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix

namespace KervaireFixed

section
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
def fixedDim (M : Matrix I I ℂ) := Module.finrank ℂ (LinearMap.ker (M.mulVecLin - LinearMap.id))
end

section
open Matrix
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
def reindexUnitary (e : I ≃ J) (P : unitary (Matrix I I ℂ)) : unitary (Matrix J J ℂ) :=
  ⟨Matrix.reindex e e (P : Matrix I I ℂ),by
    let f := Matrix.reindexAlgEquiv ℂ ℂ e
    have hs (M : Matrix I I ℂ) : star (f M) = f (star M) := by
      exact Matrix.conjTranspose_reindex e e M
    change star (f P) * f P = 1 ∧ f P * star (f P) = 1
    constructor
    · rw [hs,← map_mul,P.property.1,map_one]
    · rw [hs,← map_mul,P.property.2,map_one]⟩
end

section
open KervaireIncidenceCurrent KervaireSignPairing KervaireUnitaryHomotopy
open scoped Matrix.Norms.L2Operator
variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

end

open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]
abbrev fixedSpace (M : Matrix I I ℂ) := LinearMap.ker (M.mulVecLin - LinearMap.id)
omit [DecidableEq I] in
@[simp] lemma mem_fixedSpace (M : Matrix I I ℂ) (v : I → ℂ) :
    v ∈ fixedSpace M ↔ M.mulVec v = v := by
  simp [fixedSpace, LinearMap.mem_ker, sub_eq_zero]

lemma fixed_star {M : Matrix I I ℂ} (hM : M ∈ unitary (Matrix I I ℂ))
    {v : I → ℂ} (hv : M.mulVec v = v) : (star M).mulVec v = v := by
  calc
    (star M).mulVec v = (star M).mulVec (M.mulVec v) := congrArg _ hv.symm
    _ = v := by rw [mulVec_mulVec, hM.1, one_mulVec]

/-- Both traversal blocks have the same fixed space dimension, without a
spectral-theorem assumption or a nonzero complement assumption. -/
def doubleFixedMap (D P : unitary (Matrix I I ℂ)) :
    (fixedSpace ((D : Matrix I I ℂ) * (P : Matrix I I ℂ)) × fixedSpace ((D : Matrix I I ℂ) * (P : Matrix I I ℂ))) →ₗ[ℂ]
      fixedSpace ((fromBlocks 0 (D : Matrix I I ℂ) (star D : Matrix I I ℂ) 0) *
        (fromBlocks 0 (star P : Matrix I I ℂ) (P : Matrix I I ℂ) 0)) where
  toFun v := ⟨Sum.elim (v.1 : I → ℂ) ((star D : Matrix I I ℂ).mulVec v.2),by
    rw [mem_fixedSpace]
    have h1 := (mem_fixedSpace _ _).mp v.1.property
    have h2 := fixed_star (mul_mem D.property P.property) ((mem_fixedSpace _ _).mp v.2.property)
    simp only [star_mul] at h2
    rw [fromBlocks_multiply]
    simp only [zero_mul,mul_zero,zero_add,add_zero]
    rw [fromBlocks_mulVec]
    simp only [zero_mulVec,add_zero,zero_add]
    funext i
    cases i with
    | inl i => simpa using congrFun h1 i
    | inr i =>
      change ((star D : Matrix I I ℂ) * (star P : Matrix I I ℂ)).mulVec
        ((star D : Matrix I I ℂ).mulVec v.2) i = ((star D : Matrix I I ℂ).mulVec v.2) i
      have hh := congrArg ((star D : Matrix I I ℂ).mulVec) h2
      simpa only [mulVec_mulVec, mul_assoc] using congrFun hh i⟩
  map_add' v w := by
    apply Subtype.ext
    funext i
    cases i <;> simp [mulVec_add]
  map_smul' c v := by
    apply Subtype.ext
    funext i
    cases i <;> simp [mulVec_smul]

end KervaireFixed

namespace KervaireMatrix
open KervaireFixed KervaireSpectral KervaireRegular
open scoped Classical
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix

end

end OAI


