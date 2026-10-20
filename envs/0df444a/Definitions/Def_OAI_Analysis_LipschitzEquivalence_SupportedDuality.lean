-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
-- name    : OAI_Analysis_LipschitzEquivalence_SupportedDuality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:30:41.55488+00:00
-- url     : https://prove2.me/theorems/84a4d037-373c-4853-9c97-5882183f3aeb
-- title:
--   Functionals on free spaces and set cutoffs
-- statement:
--   Duality and cutoff tools for the Lipschitz-free space $\mathcal F(M)$ of a pointed metric space.
--
--   1. **Dual elements are Lipschitz.** For a bounded functional $T$ on $\mathcal F(M)$, the function
--   $$
--   x\mapsto T(\delta_x)
--   $$
--   is $\|T\|$-Lipschitz on $M$, since $\|\delta_x-\delta_y\|=d(x,y)$.
--   2. **Set cutoffs.** For $K\subseteq M$ and a radius $r$, the set cutoff is $\psi_r(\mathrm{dist}(x,K))$, the one-dimensional cutoff applied to the distance to $K$. It equals $1$ within $r/2$ of $K$ and $0$ at distance $\ge r$ from $K$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SupportedDuality.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SupportedDuality.lean by skeleton subtraction
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

theorem dual_point_lipschitz (T : Space M →L[ℝ] ℝ) :
    LipschitzWith ‖T‖₊ (fun x => T (point x)) := by
  simpa only [mul_one,Function.comp_def] using T.lipschitz.comp isometry_point.lipschitz

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.LocalizedLinearization
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {E : Type uE} [MetricSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]

def setCutoff (K : Set M) (r : ℝ≥0) (x : M) : ℝ :=
  cutoff (0 : ℝ) r (Metric.infDist x K)

variable [Zero M]

end LipschitzCounterexample.LocalizedLinearization

end

end OAI


