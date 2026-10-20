-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
-- name    : OAI_Analysis_LipschitzEquivalence_CauchyReduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:52:48.928907+00:00
-- url     : https://prove2.me/theorems/7016c937-1ab8-483c-8c6a-dadb2bf8108c
-- title:
--   Localization states for weakly Cauchy sequences in free spaces
-- statement:
--   A Cauchy localization state at radius $R\ge0$ for the Lipschitz-free space $\mathcal F(M)$ records:
--   - a weakly Cauchy sequence $\mu_i$ in $\mathcal F(M)$;
--   - a closed set $S\subseteq M$ containing the base point and contained in $\bar B(0,R)$;
--   - the fact that every $\mu_i$ lies in the closed span of the evaluations on $S$:
--   $$
--   \mu_i\in\mathcal F_S(M)\quad\text{for all }i .
--   $$
--
--   It is the weakly Cauchy analogue of the localization state for weakly null sequences.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/CauchyReduction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CauchyReduction.lean by skeleton subtraction
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

namespace OAI

universe uM uE

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

structure CauchyLocalizationState (R : ℝ≥0) where
  seq : ℕ → Space M
  weak : WeakSequences.WeakCauchy seq
  set : Set M
  closed : IsClosed set
  zero_mem : (0 : M) ∈ set
  bounded : set ⊆ Metric.closedBall 0 (R : ℝ)
  support : ∀ i, seq i ∈ supported set

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.WeakSequences
open Filter Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

end LipschitzCounterexample.WeakSequences

namespace LipschitzCounterexample.FreeSpace
open Filter Topology
variable {M : Type uM} [MetricSpace M] [Zero M] [CompleteSpace M]

end LipschitzCounterexample.FreeSpace

end

end OAI


