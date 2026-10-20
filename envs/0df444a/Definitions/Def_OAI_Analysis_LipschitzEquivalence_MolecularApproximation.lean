-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_MolecularApproximation
-- name    : OAI_Analysis_LipschitzEquivalence_MolecularApproximation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:58:49.384908+00:00
-- url     : https://prove2.me/theorems/65408efe-8061-433b-92e7-ca674ddfa60b
-- title:
--   Molecules and molecular representations in free spaces
-- statement:
--   Elementary molecules in the Lipschitz-free space $\mathcal F(M)$ and finite molecular data.
--
--   1. **Molecules.** For points $p\ne q$, the molecule
--   $$
--   m_{pq}=\frac{\delta_p-\delta_q}{d(p,q)}
--   $$
--   has norm $1$; for $p=q$ it is $0$.
--   2. **Molecular data.** Finite data consist of $n$ coefficients $c_i$ and pairs of points $(p_i,q_i)$. They represent the vector $\sum_ic_i(\delta_{p_i}-\delta_{q_i})$ with cost $\sum_i|c_i|\,d(p_i,q_i)$, which bounds the norm of the vector.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/MolecularApproximation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/MolecularApproximation.lean by skeleton subtraction
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

namespace OAI

universe uM

noncomputable section
namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology BigOperators
open Filter Set Metric LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

def molecule (p q : M) : Space M := (dist p q)⁻¹ • (point p-point q)

@[simp] theorem molecule_self (p : M) : molecule p p = 0 := by simp [molecule]

structure MolecularData (M : Type uM) where
  n : ℕ
  coeff : Fin n → ℝ
  p : Fin n → M
  q : Fin n → M

namespace MolecularData

def vector (a : MolecularData M) : Space M := ∑ i, a.coeff i • (point (a.p i)-point (a.q i))
def cost (a : MolecularData M) : ℝ := ∑ i, |a.coeff i| * dist (a.p i) (a.q i)

end MolecularData

end LipschitzCounterexample.FreeSpace
end

end OAI


