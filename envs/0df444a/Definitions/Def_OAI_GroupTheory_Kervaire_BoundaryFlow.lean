-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow
-- name    : OAI_GroupTheory_Kervaire_BoundaryFlow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:27:58.247019+00:00
-- url     : https://prove2.me/theorems/071b3e19-4296-4c6a-8920-e562673164c2
-- title:
--   Antisymmetric flows on the dual graph
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   For an involution $\theta$ of darts $D$ and a map $b:D\to Z$ to faces:
--
--   1. **Antisymmetric functions.** The subspace of $\gamma:D\to\mathbb R$ with $\gamma(\theta d)=-\gamma(d)$, the flows along the edges $\{d,\theta d\}$.
--   2. **Divergence.** $(\operatorname{div}\gamma)(z)=\sum_{b(d)=z}\gamma(d)$.
--   3. **Edge flows.** $\mathbf 1_d-\mathbf 1_{\theta d}$.
--   4. **Dual adjacency.** $x\sim y$ if some dart $d$ has $b(d)=x$ and $b(\theta d)=y$.
--   5. **Traversal sign.** On slots, $s_i$ on positive disks and $-s_i$ on negative disks.
--
--   On a connected dual graph every divergence with total sum $0$ is attained by an antisymmetric flow, which is used to choose rotation angles.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/BoundaryFlow.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/BoundaryFlow.lean by skeleton subtraction
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
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

namespace KervaireFlow

section
open scoped Classical
variable {D Z : Type*} [Fintype D] [Fintype Z]

def antisymmetric (θ : Equiv.Perm D) : Submodule ℝ (D → ℝ) where
  carrier := {γ | ∀ d, γ (θ d) = -γ d}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy d
    change x (θ d) + y (θ d) = -(x d + y d)
    rw [hx d, hy d, neg_add]
  smul_mem' := by
    intro r x hx d
    change r • x (θ d) = -(r • x d)
    rw [hx d, smul_neg]

/-- Literal sum of corner phases on each boundary circle. -/
def divergence (b : D → Z) : (D → ℝ) →ₗ[ℝ] (Z → ℝ) where
  toFun γ z := ∑ d, if b d = z then γ d else 0
  map_add' γ δ := by
    ext z
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> simp
  map_smul' r γ := by
    ext z
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> simp

/-- Supported on the two ends of one band, including the harmless loop case. -/
def edgeFlow (θ : Equiv.Perm D) (d : D) : D → ℝ :=
  Pi.single d 1 - Pi.single (θ d) 1

/-- Adjacency in the graph dual to the band sides, with orientations retained. -/
def Adj (b : D → Z) (θ : Equiv.Perm D) (x y : Z) : Prop :=
  ∃ d, b d = x ∧ b (θ d) = y

end

variable {D Z : Type*}
end KervaireFlow
namespace KervaireBoundary

section
open Matrix KervaireMatrix KervaireRegular KervaireSpectral KervaireMixing KervaireTraversal
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]
local instance instDecidableEqSlot : DecidableEq (Slot I K) := Classical.decEq _

def traversalSign (s : I → ℤ) : Slot I K → ℤ
  | (.inl _,i) => s i
  | (.inr _,i) => -s i

end
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular KervaireMixing KervaireTraversal
open scoped Classical
variable {I K Z A : Type*} [Fintype I] [Fintype K] [Fintype Z] [Group A]
  [Nonempty I] [Nonempty K]
local instance instDecidableEqSlot_1 : DecidableEq (Slot I K) := Classical.decEq _

end KervaireBoundary

end

end OAI


