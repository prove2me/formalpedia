-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
-- name    : OAI_Analysis_LipschitzEquivalence_HilbertBlocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:55:40.040525+00:00
-- url     : https://prove2.me/theorems/8fc1dd3a-2817-4495-9911-bab5ecda3562
-- title:
--   Dyadic means of a sequence
-- statement:
--   For a sequence $u_k$ in a real vector space, the dyadic means are defined recursively by
--   $$
--   m_0(k)=u_k,\qquad m_{n+1}(k)=\tfrac12\bigl(m_n(k)+m_n(k+2^n)\bigr).
--   $$
--
--   So $m_n(k)$ is the average of the $2^n$ consecutive terms $u_k,\dots,u_{k+2^n-1}$. These averages are used to pass from weakly Cauchy sequences to norm-small differences.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/HilbertBlocks.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/HilbertBlocks.lean by skeleton subtraction
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

namespace OAI

universe uE uF uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped BigOperators

variable {E : Type uE} [AddCommGroup E] [Module ℝ E]

def dyadicMean (u : ℕ → E) : ℕ → ℕ → E
  | 0, k => u k
  | n+1, k => (1/2 : ℝ) • (dyadicMean u n k + dyadicMean u n (k+2^n))

@[simp] theorem dyadicMean_zero (u : ℕ → E) (k : ℕ) : dyadicMean u 0 k = u k := rfl

@[simp] theorem dyadicMean_succ (u : ℕ → E) (n k : ℕ) :
    dyadicMean u (n+1) k = (1/2 : ℝ) • (dyadicMean u n k + dyadicMean u n (k+2^n)) := rfl

variable {F : Type uF} [AddCommGroup F] [Module ℝ F]

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

end LipschitzCounterexample.CompactWSC
end

end OAI


