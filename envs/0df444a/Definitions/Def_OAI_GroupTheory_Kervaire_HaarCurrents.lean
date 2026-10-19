-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
-- name    : OAI_GroupTheory_Kervaire_HaarCurrents
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:43:54.868979+00:00
-- url     : https://prove2.me/theorems/2bd868a1-9dcd-4522-ac4b-e1488c49e366
-- title:
--   Exponential flows and lifted fields on unitary groups
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   Let $B$ be a finite-dimensional C*-algebra, whose unitary group is compact.
--
--   1. **Exponential flow.** For skew-adjoint $a$, the one-parameter subgroup
--   $$
--   t\mapsto e^{ta}\in U(B).
--   $$
--   2. **Lifted field.** The linear vector field $(s,x)\mapsto(0,xa)$ on $\mathbb R\times B$, the right-translation field lifted to the time cylinder.
--
--   Integrals over the Haar measure of $U(B)$ of derivatives along these fields vanish. This makes integrals of closed invariant forms, the currents, independent of homotopies.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/HaarCurrents.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/HaarCurrents.lean by skeleton subtraction
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

namespace KervaireHaarFlow

variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]

end KervaireHaarFlow

open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff

namespace KervaireClosedCurrent

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end KervaireClosedCurrent

namespace KervaireCurrentHomotopy
-- [generator] trimmed: open KervaireClosedCurrent KervaireHaarFlow VectorField ContinuousAlternatingMap
open KervaireHaarFlow VectorField ContinuousAlternatingMap
open scoped ContDiff

variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]

end KervaireCurrentHomotopy

namespace KervaireHaarFlow

open NormedSpace
open scoped ContDiff

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
  [StarRing B] [ContinuousStar B] [StarModule ℝ B]

local instance instNormedAlgebraRat_oAI : NormedAlgebra ℚ B := .restrictScalars ℚ ℝ B

/-- The genuine exponential flow in the unitary group. -/
def expFlow (a : skewAdjoint.submodule ℝ B) (t : ℝ) : unitary B :=
  ⟨exp (t • (a : B)), exp_mem_unitary_of_mem_skewAdjoint (by
    change star (t • (a : B)) = -(t • (a : B))
    rw [star_smul, star_trivial, a.property, smul_neg])⟩

variable [CompactSpace (unitary B)] [SecondCountableTopology (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

end KervaireHaarFlow

namespace KervaireUnitaryHaarCurrent
open MeasureTheory VectorField
open scoped ContDiff
variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

/-- The autonomous lift of a right-translation field to the time cylinder. -/
def liftField (a : B) : (ℝ × B) →L[ℝ] (ℝ × B) :=
  (ContinuousLinearMap.inr ℝ ℝ B).comp
    (((ContinuousLinearMap.mul ℝ B).flip a).comp (ContinuousLinearMap.snd ℝ ℝ B))

@[simp] lemma liftField_apply (a : B) (p : ℝ × B) : liftField a p = (0,p.2*a) := rfl

variable [CompleteSpace B] [StarRing B] [ContinuousStar B] [StarModule ℝ B]
  [CompactSpace (unitary B)] [SecondCountableTopology (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

end KervaireUnitaryHaarCurrent

namespace KervaireCompactUnitary
variable {B : Type*} [CStarAlgebra B] [FiniteDimensional ℂ B]

end KervaireCompactUnitary

end

end OAI


