-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert
-- name    : OAI_Analysis_LipschitzEquivalence_SmoothHilbert
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:56:46.705979+00:00
-- url     : https://prove2.me/theorems/a8a9c788-4276-404f-bfb4-fbace0146b8e
-- title:
--   Regularized norm and soft minimum on a Hilbert space
-- statement:
--   Smooth substitutes for the norm and the minimum on a real inner product space $H$, depending on a parameter $\varepsilon$.
--
--   1. **Regularized norm.** $\|x\|_\varepsilon=\sqrt{\|x\|^2+\varepsilon^2}$, which is smooth for $\varepsilon\ne0$ and differs from $\|x\|$ by at most $|\varepsilon|$.
--   2. **Soft minimum.** For real $a,b$,
--   $$
--   \min\nolimits_\varepsilon(a,b)=\frac{a+b-\sqrt{(a-b)^2+\varepsilon^2}}2 ,
--   $$
--   a smooth approximation of $\min(a,b)=\frac{a+b-|a-b|}2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SmoothHilbert.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SmoothHilbert.lean by skeleton subtraction
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

namespace OAI

universe uH uX

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open Filter Topology
open scoped NNReal ContDiff
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def regularNorm (ε : ℝ) (x : H) : ℝ := Real.sqrt (‖x‖^2+ε^2)

def softMin (ε a b : ℝ) : ℝ := (a+b-regularNorm ε (a-b))/2

end LipschitzCounterexample.CompactWSC
end

end OAI


