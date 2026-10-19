-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
-- name    : OAI_GroupTheory_Kervaire_Traversal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:22:23.959+00:00
-- url     : https://prove2.me/theorems/09727be1-8d90-46f2-87b4-6181c93fd564
-- title:
--   Slot coordinates, mixers and monomial matrices
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   For relator positions $I$ with signs $s$ and disks $K$:
--
--   1. **Slots and sign coordinates.** Slots $(K\sqcup K)\times I$, and the bijection from two copies of $K\times I$ that places position $i$ in the positive or negative half according to $s_i$.
--   2. **Mixer and exchange.** For $X\in U(K)$, the block involution $\begin{pmatrix}0&X^*\\X&0\end{pmatrix}$ at each position, and for a matrix $P$ the exchange $\begin{pmatrix}0&P^*\\P&0\end{pmatrix}$.
--   3. **Monomial matrices.** For a permutation $\theta$ and weights $u$,
--   $$
--   M(\theta,u)_{ij}=\begin{cases}u_j,&i=\theta j,\\0,&\text{otherwise},\end{cases}
--   $$
--   multiplicative in the evident way.
--
--   Unimodularity of the relator yields a mixer $X$ with $\dim\mathrm{Fix}(\mathrm{mixer}(X)\,T)\ge2|K|$ for suitable Hermitian unitaries $T$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Traversal.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Traversal.lean by skeleton subtraction
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
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces

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

namespace KervaireTraversal

section
open Matrix KervaireFixed KervaireSignPairing
open scoped Classical
variable {I K : Type*} [Fintype I] [Fintype K]
abbrev Slots (I K : Type*) := (K ⊕ K) × I

def coordinates (s : I → ℤ) : ((K × I) ⊕ (K × I)) ≃ Slots I K where
  toFun p := match p with
    | .inl (k,i) => (if s i = 1 then Sum.inl k else Sum.inr k, i)
    | .inr (k,i) => (if s i = 1 then Sum.inr k else Sum.inl k, i)
  invFun p := match p with
    | (.inl k,i) => if s i = 1 then Sum.inl (k,i) else Sum.inr (k,i)
    | (.inr k,i) => if s i = 1 then Sum.inr (k,i) else Sum.inl (k,i)
  left_inv p := by rcases p with ⟨k,i⟩ | ⟨k,i⟩ <;> by_cases h : s i = 1 <;> simp [h]
  right_inv p := by rcases p with ⟨k|k,i⟩ <;> by_cases h : s i = 1 <;> simp [h]

def mixer (X : Matrix K K ℂ) : Matrix (Slots I K) (Slots I K) ℂ :=
  blockDiagonal fun _ : I => fromBlocks 0 (star X) X 0

def exchange (P : Matrix (K × I) (K × I) ℂ) :
    Matrix ((K × I) ⊕ (K × I)) ((K × I) ⊕ (K × I)) ℂ := fromBlocks 0 (star P) P 0

end

section
open Matrix KervaireFixed
open scoped Classical
variable {E : Type*} [Fintype E] [DecidableEq E]

end

open Matrix KervaireFixed
open scoped Classical
variable {I K : Type*} [Fintype I] [Fintype K] [Nonempty K]
local instance instDecidableEqSlots : DecidableEq (Slots I K) := Classical.decEq _

end KervaireTraversal

namespace KervaireMatrix
open Matrix KervaireRegular
open scoped Classical
variable {D : Type*} [Fintype D]

/-- The exact scalar weighted permutation attached to the oriented bands. -/
def monomial (θ : Equiv.Perm D) (u : D → ℂ) : Matrix D D ℂ :=
  fun i j ↦ if i = θ j then u j else 0

@[simp] lemma monomial_mul (θ τ : Equiv.Perm D) (u v : D → ℂ) :
    monomial θ u * monomial τ v = monomial (θ*τ) (fun j ↦ u (τ j)*v j) := by
  ext i j
  simp only [Matrix.mul_apply,monomial]
  rw [Finset.sum_eq_single (τ j)]
  · simp only
    change (if i = θ (τ j) then u (τ j) else 0) * v j =
      if i = θ (τ j) then u (τ j)*v j else 0
    split_ifs <;> simp
  · intro k _ hk
    simp [hk]
  · simp

omit [Fintype D] in
@[simp] lemma monomial_one [DecidableEq D] : monomial (Equiv.refl D) (fun _ ↦ 1) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [monomial,Matrix.one_apply,h]

variable {A : Type*} [Group A]
end KervaireMatrix

namespace KervaireMixing
open Matrix KervaireMatrix KervaireRegular KervaireFixed
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A] [Nonempty I] [Nonempty K]
local instance instDecidableEqSlot : DecidableEq (Slot I K) := Classical.decEq _

end KervaireMixing

end

end OAI


