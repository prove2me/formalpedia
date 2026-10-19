-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
-- name    : OAI_GroupTheory_Kervaire_MixingOperators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:40:37.558505+00:00
-- url     : https://prove2.me/theorems/2e80ed20-79bf-4f58-97df-4f307e13d107
-- title:
--   Slots, the coefficient shift and the scalar mixer
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   Fix a cyclic order $\rho$ on the positions $I$ of the relator, coefficients $a:I\to A$, and a finite set $K$ of disks of each kind.
--
--   1. **Slots.** $(K\sqcup K)\times I$: a disk number, a kind (positive or negative), and a position.
--   2. **Successor.** $\rho$ on positive slots and $\rho^{-1}$ on negative slots.
--   3. **Labels.** $a_i^{-1}$ on positive slots and $a_{\rho^{-1}i}$ on negative slots.
--   4. **Mixing matrix and operators.** For $X\in U(K)$, the block involution $\begin{pmatrix}0&X^*\\X&0\end{pmatrix}$ at each position. The coefficient shift $S$ is the labelled shift of the successor, and $J$ is the scalar mixer:
--   $$
--   S=\mathrm{Shift}(\mathrm{succ},\mathrm{labels}),\qquad J=\mathrm{mix}(X)\otimes1,\qquad J^2=1 .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/MixingOperators.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/MixingOperators.lean by skeleton subtraction
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

namespace KervaireMixing

section
open Matrix KervaireMatrix KervaireRegular
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

/-- A slot is a disk number, a disk kind, and a position in the cyclic word. -/
abbrev Slot (I K : Type*) := (K ⊕ K) × I

/-- The opposite cyclic orders on positive and negative word disks. -/
def successor (ρ : Equiv.Perm I) : Equiv.Perm (Slot I K) where
  toFun p := match p with
    | (Sum.inl k, i) => (Sum.inl k, ρ i)
    | (Sum.inr k, i) => (Sum.inr k, ρ.symm i)
  invFun p := match p with
    | (Sum.inl k, i) => (Sum.inl k, ρ.symm i)
    | (Sum.inr k, i) => (Sum.inr k, ρ i)
  left_inv p := by rcases p with ⟨k|k,i⟩ <;> simp
  right_inv p := by rcases p with ⟨k|k,i⟩ <;> simp

/-- Coefficient inverses for the signed incidence operator. -/
def labels (ρ : Equiv.Perm I) (a : I → A) : Slot I K → A
  | (Sum.inl _, i) => (a i)⁻¹
  | (Sum.inr _, i) => a (ρ.symm i)

/-- The scalar mixing involution; no group coefficients occur in it. -/
def mixingMatrix (X : Matrix K K ℂ) : Matrix (Slot I K) (Slot I K) ℂ :=
  blockDiagonal fun _ : I => fromBlocks 0 Xᴴ X 0

omit [Fintype I] [Fintype K] in
@[simp] theorem mixingMatrix_star (X : Matrix K K ℂ) :
    star (mixingMatrix (I := I) X) = mixingMatrix X := by
  ext ⟨k,i⟩ ⟨l,j⟩
  rcases k with k | k <;> rcases l with l | l <;>
    by_cases h : i = j <;> simp [mixingMatrix, Matrix.star_apply, blockDiagonal_apply, fromBlocks, eq_comm, h]

@[simp] theorem mixingMatrix_sq (X : Matrix.unitaryGroup K ℂ) :
    mixingMatrix (I := I) (X : Matrix K K ℂ) * mixingMatrix (X : Matrix K K ℂ) = 1 := by
  simp only [mixingMatrix, ← blockDiagonal_mul, fromBlocks_multiply,
    zero_mul, mul_zero, add_zero, zero_add]
  rw [show (X : Matrix K K ℂ)ᴴ * (X : Matrix K K ℂ) = 1 from X.2.1,
    show (X : Matrix K K ℂ) * (X : Matrix K K ℂ)ᴴ = 1 from X.2.2]
  convert (blockDiagonal_one (m := K ⊕ K) (o := I) (α := ℂ)) using 1
  ext ⟨p,i⟩ ⟨q,j⟩
  simp [blockDiagonal_apply, fromBlocks_one, Matrix.one_apply]

/-- The coefficient shift S and scalar mixer J in the actual regular Hilbert space. -/
def S (ρ : Equiv.Perm I) (a : I → A) : Operator (Slot I K) A :=
  labelledShift (successor ρ) (labels ρ a)
def J (X : Matrix K K ℂ) : Operator (Slot I K) A := scalarTensor (mixingMatrix X)

omit [Fintype I] [Fintype K] in
theorem S_unitary (ρ : Equiv.Perm I) (a : I → A) :
    S (K := K) ρ a ∈ unitary (Operator (Slot I K) A) := labelledShift_unitary _ _
omit [Group A] in
theorem J_sq (X : Matrix.unitaryGroup K ℂ) :
    J (I := I) (A := A) (X : Matrix K K ℂ) * J (X : Matrix K K ℂ) = 1 := by
  rw [J, ← scalarTensor_mul, mixingMatrix_sq]
  ext f ⟨d,a⟩
  simp [Matrix.one_apply]

omit [Group A] in
theorem J_star (X : Matrix K K ℂ) :
    star (J (I := I) (A := A) X) = J X := by
  rw [J, scalarTensor_star, mixingMatrix_star]

omit [Group A] in
theorem J_unitary (X : Matrix.unitaryGroup K ℂ) :
    J (I := I) (A := A) (X : Matrix K K ℂ) ∈ unitary (Operator (Slot I K) A) := by
  rw [Unitary.mem_iff, J_star, J_sq]
  exact ⟨rfl,rfl⟩

omit [Group A] in
@[simp] theorem scalarTensor_delta (M : Matrix (Slot I K) (Slot I K) ℂ)
    (p q : Slot I K) (x y : A) :
    scalarTensor M (delta (p,x)) (q,y) = if x = y then M q p else 0 := by
  simp [scalarTensor_apply, delta, Pi.single_apply, Prod.mk.injEq, ite_and,
    mul_ite, eq_comm]

end
open Matrix KervaireMatrix KervaireRegular KervaireSpectral
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

end KervaireMixing
namespace KervaireCycle
variable {D E B : Type*} [Monoid B]
end KervaireCycle
namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireTraceCalculus KervaireCycle
open scoped Classical
variable {D E A : Type*} [Fintype D] [Fintype E] [Group A]
end KervaireMatrix

namespace KervaireRegular
open KervaireSpectral KervaireTraceCalculus MeasureTheory
variable {A : Type*} [Group A]

end KervaireRegular

namespace KervaireCycle
open KervaireSpectral
variable {D B : Type*} [CommMonoid B]
end KervaireCycle

namespace KervaireBoundary
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular
open scoped Classical
variable {D Z A : Type*} [Fintype D] [Fintype Z] [Group A]

end KervaireBoundary

end

end OAI


