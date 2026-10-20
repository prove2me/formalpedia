-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactHilbertWSC
-- name    : OAI_Analysis_LipschitzEquivalence_CompactHilbertWSC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:24:01.669989+00:00
-- url     : https://prove2.me/theorems/80f1e14c-7a8e-4fd1-a9b5-f0191e1e6965
-- title:
--   Normed structure for compactly supported free spaces of Hilbert spaces
-- statement:
--   For a real Hilbert space $H$, this records the normed-space structures used on the free space $\mathcal F(H)$, on the subspaces $\mathcal F_K(H)$ spanned by evaluations at points of $K\subseteq H$, and on their duals:
--   $$
--   \mathcal F_K(H)^*=\{\text{bounded linear functionals on }\mathcal F_K(H)\}.
--   $$
--
--   They fix the setting for proving that free spaces over compact subsets of Hilbert space are weakly sequentially complete.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/CompactHilbertWSC.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CompactHilbertWSC.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LipschitzEquivalence mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MolecularApproximation
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothCalculus
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_EnergyEstimates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BlockSelection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothMultiplier
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_DetectingSequence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WUCFunctions
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WUCDuals
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WUCOperator

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local instance instNormedAddCommGroupSpace_2 : NormedAddCommGroup (Space H) := inferInstance
local instance instNormedSpaceRealSpace_2 : NormedSpace ℝ (Space H) := inferInstance
local instance instNormedAddCommGroupSubtypeSpaceMemSubmoduleRealSupported_2 (K : Set H) : NormedAddCommGroup (supported K) := inferInstance
local instance instNormedSpaceRealSubtypeSpaceMemSubmoduleSupported_2 (K : Set H) : NormedSpace ℝ (supported K) := inferInstance
local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeSpaceMemSubmoduleSupported_1 (K : Set H) : NormedAddCommGroup ((supported K) →L[ℝ] ℝ) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeSpaceMemSubmoduleSupported_1 (K : Set H) : NormedSpace ℝ ((supported K) →L[ℝ] ℝ) := inferInstance

end LipschitzCounterexample.CompactWSC
end

end OAI


