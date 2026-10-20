-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
-- name    : OAI_Analysis_LipschitzEquivalence_GraphObstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:12:48.857491+00:00
-- url     : https://prove2.me/theorems/9f3e2542-c5da-47aa-9cb2-a5409d3d6c0e
-- title:
--   Diagonal embeddings of scalar null sequences into Hilbert-valued null sequences
-- statement:
--   Auxiliary isometries used to locate copies of $c_0$ inside $c_0(\ell^2)$.
--
--   1. **Unit vectors.** $e_i\in\ell^2$ is the $i$-th standard unit vector, with $\|e_i\|=1$.
--   2. **Single entries.** For each $n$, $x\mapsto\mathrm{single}_n(x)$ is a linear isometry $\ell^2\to c_0(\ell^2)$.
--   3. **Diagonal embedding.** For unit vectors $t_n\in\ell^2$, the map
--   $$
--   a\mapsto(a_n\,t_n)_{n\in\mathbb N}
--   $$
--   is a linear isometry from scalar $c_0$ into $c_0(\ell^2)$.
--   4. **First component.** For $Q:A\to H$ between Banach spaces, the projection of the weighted graph space $\mathcal G(Q)$ to its $\ell^1(A)$ component is a bounded operator.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/GraphObstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/GraphObstruction.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uH uA uB

noncomputable section
namespace LipschitzCounterexample

namespace GraphObstruction
open Filter Topology
open WeakSequences
open scoped ENNReal NNReal
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]
abbrev unitVector (i : ℕ) : RealL2 := lp.single 2 i 1

@[simp] theorem unitVector_coord (i j : ℕ) : unitVector i j = if j = i then 1 else 0 := by
  simp [unitVector, lp.single_apply, Pi.single_apply]

@[simp] theorem norm_unitVector (i : ℕ) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

open NullSequences

variable {A : Type uA} {B : Type uB} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def c0singleLI (n : ℕ) : RealL2 →ₗᵢ[ℝ] C0 (H := RealL2) where
  toFun := NullSequences.single n
  map_add' := by
    intro x y
    ext i
    by_cases hi : i = n <;> simp [hi]
  map_smul' := by
    intro c x
    ext i
    by_cases hi : i = n <;> simp [hi]
  norm_map' := NullSequences.norm_single n

def diagonalFun (t : ℕ → RealL2) (ht : ∀ n, ‖t n‖ = 1) (a : ScalarC0) : C0 (H := RealL2) :=
  ofTendsto (fun n => a n • t n) (by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    simpa only [norm_smul, ht, mul_one, norm_zero] using (NullSequences.tendsto_zero a).norm)

def diagonal (t : ℕ → RealL2) (ht : ∀ n, ‖t n‖ = 1) : ScalarC0 →ₗᵢ[ℝ] C0 (H := RealL2) where
  toFun := diagonalFun t ht
  map_add' := by
    intro a b
    apply ZeroAtInftyContinuousMap.ext
    intro n
    exact add_smul (a n) (b n) (t n)
  map_smul' := by
    intro c a
    apply ZeroAtInftyContinuousMap.ext
    intro n
    exact mul_smul c (a n) (t n)
  norm_map' := by
    intro a
    apply le_antisymm
    · apply (NullSequences.norm_le (norm_nonneg a)).2
      intro n
      change ‖a n • t n‖ ≤ ‖a‖
      rw [norm_smul, ht, mul_one]
      exact norm_apply_le a n
    · apply (NullSequences.norm_le (norm_nonneg _)).2
      intro n
      calc
        ‖a n‖ = ‖a n • t n‖ := by rw [norm_smul, ht, mul_one]
        _ ≤ _ := norm_apply_le (diagonalFun t ht a) n

@[simp] theorem diagonal_apply (t : ℕ → RealL2) (ht : ∀ n, ‖t n‖ = 1) (a : ScalarC0) (n : ℕ) :
    diagonal t ht a n = a n • t n := rfl

variable [CompleteSpace A] [CompleteSpace H]

def first (Q : A →L[ℝ] H) : WeightedGraph.Space Q →L[ℝ] WeightedGraph.L1 A :=
  (ContinuousLinearMap.fst ℝ (WeightedGraph.L1 A) (WeightedGraph.C0 H)).comp
    (WeightedGraph.inclusion Q).toContinuousLinearMap

end GraphObstruction

end LipschitzCounterexample
end

end OAI


