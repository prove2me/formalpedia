-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
-- name    : OAI_Analysis_LipschitzEquivalence_CompactLocalization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:23:53.889873+00:00
-- url     : https://prove2.me/theorems/3d7d91c0-2469-4f25-802f-2f96253b6d4f
-- title:
--   Removing a Lipschitz function near finitely many points
-- statement:
--   Localization of a Lipschitz function $d:M\to\mathbb R$ near finitely many points $z_j$ of a metric space, using the cutoffs $\psi_{z,r}$ (equal to $1$ on the ball of radius $r/2$ about $z$ and $0$ outside the ball of radius $r$).
--
--   1. **Supports.** A nonzero value $\psi_{z,r}(x)\ne0$ forces $d(x,z)<r$. If the balls $B(z_j,r)$ are pairwise disjoint, at most one $\psi_{z_j,r}$ is nonzero at each point.
--   2. **Removed part.** The removed part and the remainder are
--   $$
--   \mathrm{rem}(x)=\sum_j\bigl(d(x)-d(z_j)\bigr)\psi_{z_j,r}(x),\qquad d-\mathrm{rem}.
--   $$
--   The remainder is constant equal to $d(z_j)$ on $B(z_j,r/2)$.
--   3. **Lipschitz bound.** If $d$ is $L$-Lipschitz and the balls are disjoint, the removed part is $6L$-Lipschitz.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/CompactLocalization.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CompactLocalization.lean by skeleton subtraction
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

namespace OAI

universe uM uI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.LocalizedLinearization
open Filter Set Topology LocalLipschitz
open scoped NNReal ENNReal
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

theorem cutoff_nonzero_mem (z : M) {r : ℝ≥0} (hr : 0 < r) {x : M}
    (hx : cutoff z r x ≠ 0) : x ∈ Metric.ball z r := by
  by_contra hn
  apply hx
  exact cutoff_zero z hr (le_of_not_gt hn)

omit [Fintype I] in
theorem disjoint_cutoffs (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r))) :
    ∀ x j k, cutoff (z j) r x ≠ 0 → cutoff (z k) r x ≠ 0 → j = k := by
  intro x j k hj hk
  by_contra hn
  exact Set.disjoint_left.mp (hdis hn) (cutoff_nonzero_mem _ hr hj) (cutoff_nonzero_mem _ hr hk)

def removed (d : M → ℝ) (z : I → M) (r : ℝ≥0) (x : M) : ℝ :=
  ∑ j, (d x-d (z j))*cutoff (z j) r x

def remainder (d : M → ℝ) (z : I → M) (r : ℝ≥0) : M → ℝ :=
  weightedRemainder d z (fun j => cutoff (z j) r)

theorem removed_lipschitz (d : M → ℝ) {L : ℝ≥0} (hd : LipschitzWith L d)
    (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r))) :
    LipschitzWith (6*L) (removed d z r) := by
  have hpart (j : I) : LipschitzWith (3*L) (fun x => (d x-d (z j))*cutoff (z j) r x) :=
    cutoff_product_lipschitz _ hr _ (lipschitz_sub_const _ hd _) (sub_self _)
  have ht := disjoint_sum_lipschitz _ hpart (by
    intro x j k hj hk
    apply disjoint_cutoffs z hr hdis x j k
    · exact (mul_ne_zero_iff.mp hj).2
    · exact (mul_ne_zero_iff.mp hk).2)
  have he : 2*(3*L) = 6*L := by ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [he,removed] using ht.dist_le_mul x y

end LipschitzCounterexample.LocalizedLinearization

namespace LipschitzCounterexample.LocalizedLinearization
open Filter Set Topology LocalLipschitz
open scoped NNReal ENNReal
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Zero M] [Fintype I]

end LipschitzCounterexample.LocalizedLinearization

namespace LipschitzCounterexample.LocalizedLinearization
open Filter Set Topology LocalLipschitz
open scoped NNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

end LipschitzCounterexample.LocalizedLinearization

end

end OAI


