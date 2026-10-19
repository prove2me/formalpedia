-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
-- name    : OAI_GroupTheory_Kervaire_CurrentPullback
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:46:57.899898+00:00
-- url     : https://prove2.me/theorems/1ad885e0-4de5-43c7-9ac6-c4f14ee2d481
-- title:
--   Tangent spaces of the unitary group
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Tangent space.** At a unitary $u$ of a finite-dimensional C*-algebra $B$, the real subspace
--   $$
--   T_uU(B)=\{ua:\ a^*=-a\}\subseteq B .
--   $$
--   Derivatives of smooth paths and maps into $U(B)$ lie in these tangent spaces, whose dimension is at most that of the skew-adjoint part.
--
--   This controls pullbacks of differential forms of top degree. They vanish on tuples of vectors lying in a proper subspace, which makes the pullback of an invariant current a constant.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/CurrentPullback.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/CurrentPullback.lean by skeleton subtraction
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

namespace KervaireCurrentPullback

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

end KervaireCurrentPullback

open MeasureTheory NormedSpace
open scoped ContDiff

namespace KervaireUnitaryTangent

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
  [StarRing B] [ContinuousStar B] [StarModule ℝ B]

/-- The real tangent subspace at a unitary, represented in the ambient algebra. -/
def tangent (u : unitary B) : Submodule ℝ B :=
  (skewAdjoint.submodule ℝ B).map (LinearMap.mulLeft ℝ (u : B))

end KervaireUnitaryTangent

open Module Set ContinuousAlternatingMap
namespace KervaireAlternatingSpan
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end KervaireAlternatingSpan

namespace KervaireHorizontalCurrent
open MeasureTheory ContinuousAlternatingMap VectorField
-- [generator] trimmed: open KervaireUnitaryHaarCurrent KervaireUnitaryTangent KervaireCurrentPullback
open KervaireUnitaryHaarCurrent KervaireUnitaryTangent
open scoped ContDiff
variable {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]
  [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [CompactSpace (unitary B)] [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

local instance instNormedAlgebraRat_oAI : NormedAlgebra ℚ B := .restrictScalars ℚ ℝ B

end KervaireHorizontalCurrent

end

end OAI


