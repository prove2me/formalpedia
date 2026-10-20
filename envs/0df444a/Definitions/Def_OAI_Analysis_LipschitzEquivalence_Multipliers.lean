-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
-- name    : OAI_Analysis_LipschitzEquivalence_Multipliers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:43:12.585722+00:00
-- url     : https://prove2.me/theorems/c3177541-ad2f-4004-af4a-829cf9eef378
-- title:
--   Multiplication operators and approximability on free spaces
-- statement:
--   Two notions on the Lipschitz-free space $\mathcal F(M)$ of a pointed metric space.
--
--   1. **Multipliers.** For a function $\varphi:M\to\mathbb R$, the multiplier is the linearization of $x\mapsto\varphi(x)\,\delta_x$:
--   $$
--   \varphi\cdot\delta_x=\varphi(x)\,\delta_x .
--   $$
--   It is a bounded operator on $\mathcal F(M)$ when $x\mapsto\varphi(x)\delta_x$ is Lipschitz.
--   2. **Approximability.** An element $\mu\in\mathcal F(M)$ is $\varepsilon$-approximable on $K\subseteq M$ if some $\nu$ in the closed span $\mathcal F_K(M)$ of $\{\delta_x:x\in K\}$ has $\|\mu-\nu\|<\varepsilon$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/Multipliers.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/Multipliers.lean by skeleton subtraction
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

def multiplier (φ : M → ℝ) : Space M →L[ℝ] Space M :=
  linearize (fun x => φ x • point x)

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

def Approximable (μ : Space M) (K : Set M) (ε : ℝ) : Prop :=
  ∃ ν : Space M, ν ∈ supported K ∧ ‖μ-ν‖ < ε

end LipschitzCounterexample.FreeSpace

end

end OAI


