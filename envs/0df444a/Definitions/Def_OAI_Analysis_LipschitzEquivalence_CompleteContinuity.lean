-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
-- name    : OAI_Analysis_LipschitzEquivalence_CompleteContinuity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:25:48.960373+00:00
-- url     : https://prove2.me/theorems/285ad319-f93d-4faf-ba22-f9eb8203837c
-- title:
--   Unit normalization and scalar tests of Hilbert-valued Lipschitz maps
-- statement:
--   Two small tools used in the complete-continuity argument.
--
--   1. **Normalization.** For a sequence $u_i$ in a real normed space, its unit normalization is
--   $$
--   \hat u_i=\|u_i\|^{-1}u_i ,
--   $$
--   which has norm $1$ whenever $u_i\ne0$ (and is $0$ otherwise).
--   2. **Scalar tests.** If $D:M\to\mathcal H$ is an $L$-Lipschitz map into a Hilbert sum of Euclidean spaces and $\|b\|\le1$, then the scalar function $x\mapsto\langle D(x),b\rangle$ is $L$-Lipschitz on $M$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/CompleteContinuity.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CompleteContinuity.lean by skeleton subtraction
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

namespace OAI

universe uE uM uIndex

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.WeakSequences
open Filter Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
def unitNormalize (u : ℕ → E) (i : ℕ) : E := ‖u i‖⁻¹ • u i

end LipschitzCounterexample.WeakSequences

namespace LipschitzCounterexample.LocalizedLinearization
open Filter Set Topology LocalLipschitz CoordinateSpaces LocalGeometry
open scoped NNReal InnerProductSpace
variable {M : Type uM} [MetricSpace M] [Zero M]
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

omit [Zero M] in
theorem scalar_test_lipschitz (D : M → Hilbert (ι := ι)) {L : ℝ≥0}
    (hD : LipschitzWith L D) (b : Hilbert (ι := ι)) (hb : ‖b‖ ≤ 1) :
    LipschitzWith L (fun x => ⟪D x,b⟫_ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,← inner_sub_left]
  exact (abs_real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans (by simpa only [mul_one,← dist_eq_norm] using hD.dist_le_mul x y))

end LipschitzCounterexample.LocalizedLinearization

end

end OAI


