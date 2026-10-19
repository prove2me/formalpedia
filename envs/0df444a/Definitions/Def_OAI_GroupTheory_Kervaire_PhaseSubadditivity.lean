-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
-- name    : OAI_GroupTheory_Kervaire_PhaseSubadditivity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:17:09.500962+00:00
-- url     : https://prove2.me/theorems/e85f2be6-51bb-41c0-9f70-84d10ca50b3b
-- title:
--   Traced phases in a centralizer algebra
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   Let $S$ be a set of operators on a Hilbert space $H$ and $\xi_1,\dots,\xi_m$ vectors.
--
--   1. **Centralizer algebra.** The closed $*$-subalgebra of operators commuting with $S$, with its inclusion, square roots and order.
--   2. **Vector sum and summed phase.** The functional $T\mapsto\sum_j\langle\xi_j,T\xi_j\rangle$ and the phase
--   $$
--   \mathrm{Ph}(U)=\sum_j\mathrm{ph}_{\xi_j}(U).
--   $$
--   3. **Trace.** The vector sum restricted to the centralizer algebra.
--
--   When this restriction is tracial, the summed phase is subadditive on unitaries of the algebra: $\mathrm{Ph}(UV)\le\mathrm{Ph}(U)+\mathrm{Ph}(V)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseSubadditivity.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseSubadditivity.lean by skeleton subtraction
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

namespace KervaireCentralizer
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev Operator := H →L[ℂ] H

/-- The strongly closed algebra in which the phase comparison is performed. -/
def algebra (S : Set (Operator (H := H))) : StarSubalgebra ℂ (Operator (H := H)) :=
  StarSubalgebra.centralizer ℂ S

instance (S : Set (Operator (H := H))) : IsClosed (algebra S : Set (Operator (H := H))) :=
  Set.isClosed_centralizer _

/-- The inclusion is continuous for the inherited operator norm. -/
def inclusion (S : Set (Operator (H := H))) : algebra S →L[ℂ] Operator (H := H) :=
  (algebra S).toSubalgebra.toSubmodule.subtypeL

local instance instContinuousFunctionalCalculusRealOperatorIsSelfAdjoint : ContinuousFunctionalCalculus ℝ (Operator (H := H)) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The right-translation commutants are closed under continuous square roots. -/
theorem sqrt_mem (S : Set (Operator (H := H))) {X : Operator (H := H)}
    (hX : X ∈ algebra S) : CFC.sqrt X ∈ algebra S := by
  rw [algebra, StarSubalgebra.mem_centralizer_iff] at hX ⊢
  intro R hR
  obtain ⟨h₁, h₂⟩ := hX R hR
  exact ⟨((show Commute X R from h₁.symm).cfcₙ_nnreal NNReal.sqrt).eq.symm,
    ((show Commute X (star R) from h₂.symm).cfcₙ_nnreal NNReal.sqrt).eq.symm⟩

/-- The inherited positive-operator order, not a replacement order. -/
instance orderedRing (S : Set (Operator (H := H))) : StarOrderedRing (algebra S) := by
  apply StarOrderedRing.of_le_iff
  intro X Y
  constructor
  · intro h
    change (X : Operator (H := H)) ≤ (Y : Operator (H := H)) at h
    have hD : 0 ≤ ((Y : Operator (H := H)) - (X : Operator (H := H))) := sub_nonneg.mpr h
    let Q : algebra S := ⟨CFC.sqrt ((Y : Operator (H := H)) - (X : Operator (H := H))),
      sqrt_mem S ((algebra S).sub_mem Y.property X.property)⟩
    refine ⟨Q, ?_⟩
    apply Subtype.ext
    change (Y : Operator (H := H)) = (X : Operator (H := H)) +
      star (CFC.sqrt ((Y : Operator (H := H)) - (X : Operator (H := H)))) * CFC.sqrt ((Y : Operator (H := H)) - (X : Operator (H := H)))
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq,
      CFC.sqrt_mul_sqrt_self _ hD]
    abel
  · rintro ⟨Q, rfl⟩
    change (X : Operator (H := H)) ≤ (X : Operator (H := H)) + star (Q : Operator (H := H)) * (Q : Operator (H := H))
    exact le_add_of_nonneg_right (star_mul_self_nonneg _)

@[simp] theorem inclusion_apply (S : Set (Operator (H := H))) (X : algebra S) :
    inclusion S X = (X : Operator (H := H)) := rfl

/-- Unitarity is unchanged when an operator is viewed in its centralizer. -/
theorem unitary_iff (S : Set (Operator (H := H))) (X : algebra S) :
    X ∈ unitary (algebra S) ↔ (X : Operator (H := H)) ∈ unitary (Operator (H := H)) := by
  simp only [Unitary.mem_iff]
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨Subtype.ext h₁, Subtype.ext h₂⟩

end KervaireCentralizer

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- The unnormalized finite sum of vector functionals used for matrix traces. -/
def vectorSum (ξ : ι → H) : Operator H →L[ℂ] ℂ := ∑ j, vectorCLM (ξ j)

omit [CompleteSpace H] in
@[simp] theorem vectorSum_apply (ξ : ι → H) (T : Operator H) :
    vectorSum ξ T = ∑ j, vectorCLM (ξ j) T := by simp [vectorSum]

/-- The phase measured by a finite family of vectors. -/
def sumPhase (U : Operator H) [IsStarNormal U] (ξ : ι → H) : ℝ :=
  ∑ j, vectorPhase U (ξ j)

end KervaireSpectral

namespace KervaireCentralizer
open KervaireTraceCalculus KervaireSpectral KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- The vector sum restricted to the correct finite-trace algebra. -/
def trace (S : Set (Operator (H := H))) (ξ : ι → H) : algebra S →L[ℂ] ℂ :=
  (vectorSum ξ).comp (inclusion S)

@[simp] theorem trace_apply (S : Set (Operator (H := H))) (ξ : ι → H) (X : algebra S) :
    trace S ξ X = vectorSum ξ (X : Operator (H := H)) := rfl

end KervaireCentralizer

end

end OAI


