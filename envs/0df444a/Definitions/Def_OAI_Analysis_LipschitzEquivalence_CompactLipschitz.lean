-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
-- name    : OAI_Analysis_LipschitzEquivalence_CompactLipschitz
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:15:12.342724+00:00
-- url     : https://prove2.me/theorems/c71895c0-3e02-476e-8222-a6d09045d7bd
-- title:
--   Sums of disjointly supported Lipschitz functions
-- statement:
--   Two Lipschitz constructions on a metric space $M$ with finitely many indices $I$.
--
--   1. **Disjoint sums.** If each $f_i:M\to\mathbb R$ is $C$-Lipschitz and at every point at most one $f_i$ is nonzero, then
--   $$
--   x\mapsto\sum_{i\in I}f_i(x)\quad\text{is }2C\text{-Lipschitz}.
--   $$
--   2. **Weighted remainders.** For $d:M\to\mathbb R$, points $z_j$ and weights $\varphi_j$, the weighted remainder is
--   $$
--   d(x)-\sum_j\bigl(d(x)-d(z_j)\bigr)\varphi_j(x),
--   $$
--   which replaces $d$ near $z_j$ by its value $d(z_j)$ where $\varphi_j=1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/CompactLipschitz.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CompactLipschitz.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uM uI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

theorem disjoint_sum_lipschitz (f : I → M → ℝ) {C : ℝ≥0}
    (hf : ∀ i, LipschitzWith C (f i))
    (hdis : ∀ x i j, f i x ≠ 0 → f j x ≠ 0 → i = j) :
    LipschitzWith (2*C) (fun x => ∑ i, f i x) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hi =>
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Finset.sum_of_isEmpty,dist_self]
    positivity
  | inr hi =>
    have hex (x : M) : ∃ i : I, ∀ j : I, j ≠ i → f j x = 0 := by
      by_cases hx : ∃ i, f i x ≠ 0
      · obtain ⟨i,hi⟩ := hx
        refine ⟨i,fun j hji => ?_⟩
        by_contra hj
        exact hji (hdis x j i hj hi)
      · push Not at hx
        exact ⟨Classical.choice hi,fun j _ => hx j⟩
    choose a ha using hex
    have heval (x : M) : ∑ i, f i x = f (a x) x := by
      apply Finset.sum_eq_single (a x)
      · intro b hb hba
        exact ha x b hba
      · simp
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [heval,heval,Real.dist_eq]
    by_cases hxy : a x = a y
    · have h := (hf (a x)).dist_le_mul x y
      rw [Real.dist_eq,hxy] at h
      rw [hxy]
      calc
        _ ≤ (C : ℝ) * dist x y := h
        _ ≤ (2*C : ℝ≥0) * dist x y := by
          simp only [NNReal.coe_mul, NNReal.coe_ofNat]
          nlinarith [C.coe_nonneg, dist_nonneg (x := x) (y := y)]
    · have hx := (hf (a x)).dist_le_mul x y
      have hy := (hf (a y)).dist_le_mul x y
      rw [ha y (a x) hxy,Real.dist_eq,sub_zero] at hx
      rw [ha x (a y) (Ne.symm hxy),Real.dist_eq,zero_sub,abs_neg] at hy
      calc
        _ ≤ |f (a x) x|+|f (a y) y| := abs_sub _ _
        _ ≤ (2*C : ℝ≥0) * dist x y := by
          simp only [NNReal.coe_mul,NNReal.coe_ofNat]
          linarith

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

def weightedRemainder (d : M → ℝ) (z : I → M) (φ : I → M → ℝ) (x : M) : ℝ :=
  d x - ∑ j, (d x-d (z j))*φ j x

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalGeometry
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

end LipschitzCounterexample.LocalGeometry

end

end OAI


