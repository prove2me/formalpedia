-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
-- name    : OAI_Analysis_LipschitzEquivalence_GraphEmbedding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:28:14.205673+00:00
-- url     : https://prove2.me/theorems/d5c07528-0047-4568-a4ee-47c392c76487
-- title:
--   Bi-Lipschitz equivalence of weighted graph spaces and an isometric copy of c₀
-- statement:
--   Consequences of the free-space criterion for weighted graph spaces, for real normed spaces $U,V$ and $W=U\oplus_2V$.
--
--   1. **Setting.** Let $q:\mathcal F(W)\to U$ be bounded and $h:W\to U$ a bijection with $h(0)=0$ and $q(\delta_x)=h(x)-x_U$. Assume $h$ is $b$-Lipschitz and $h^{-1}$ is $a$-Lipschitz. Let $Q_1:\mathcal F(W)\oplus_1V\to W$, $(\mu,v)\mapsto(q\mu,v)$, and let $B,B^{-1}$ be the associated bi-Lipschitz maps.
--   2. **Graph equivalence.** Lifting $B$ (with $h$) and $B^{-1}$ (with $h^{-1}$) coordinatewise gives mutually inverse Lipschitz bijections
--   $$
--   \mathcal G(Q_1)\ \leftrightarrow\ \mathcal G(q)
--   $$
--   between the weighted graph spaces.
--   3. **Copy of $c_0(V)$.** The map sending a null sequence $(v_i)$ in $V$ to the element of $\mathcal G(Q_1)$ with coordinates $(0,v_i)$ is a linear isometry $c_0(V)\to\mathcal G(Q_1)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/GraphEmbedding.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/GraphEmbedding.lean by skeleton subtraction
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

namespace OAI

universe uU uV

noncomputable section
namespace LipschitzCounterexample

namespace Criterion
open scoped NNReal ENNReal Topology
open Filter
variable {U : Type uU} {V : Type uV} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (q : Free U V →L[ℝ] U) (h : Domain U V ≃ U)
  (hlin : ∀ x : Domain U V, q (FreeSpace.point x) = h x - x.fst)
  (h0 : h 0 = 0) {a b : ℝ≥0} (hh : LipschitzWith b h) (hi : LipschitzWith a h.symm)

omit [NormedSpace ℝ U] [NormedSpace ℝ V] in
include h0 in
@[simp] theorem symm_zero : h.symm 0 = 0 := by
  apply h.injective
  simpa using h0.symm

omit [NormedSpace ℝ V] in
include h0 in
@[simp] theorem Binv_zero : Binv q h 0 = 0 := by
  simp [Binv, symm_zero h h0]

def graphEquiv : WeightedGraph.Space (Q1 q) ≃ WeightedGraph.Space q where
  toFun := WeightedGraph.lift (Q1 q) q (B q) h (lipschitz_B q) hh
    (B_zero q) h0 (diagram q h hlin)
  invFun := WeightedGraph.lift q (Q1 q) (Binv q h) h.symm (lipschitz_Binv q h hi) hi
    (Binv_zero q h h0) (symm_zero h h0) (Q1_Binv q h hlin)
  left_inv := by
    intro s
    apply WeightedGraph.ext
    intro i
    simp only [WeightedGraph.coord_lift, Binv_B q h hlin]
  right_inv := by
    intro s
    apply WeightedGraph.ext
    intro i
    simp only [WeightedGraph.coord_lift, B_Binv q h hlin]

omit hlin h0 hh hi in

def c0EmbedFun (v : NullSequences.C0 (H := V)) : WeightedGraph.Space (Q1 q) :=
  WeightedGraph.ofSequence (Q1 q) (fun i => WithLp.toLp 1 (0, v i)) (by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (WeightedGraph.weight_nonneg i) (norm_nonneg _))
      (fun i => ?_) ((WeightedGraph.hasSum_weight.summable).mul_right ‖v‖)
    rw [WithLp.prod_norm_eq_of_L1]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_zero, zero_add]
    exact mul_le_mul_of_nonneg_left (NullSequences.norm_apply_le v i) (WeightedGraph.weight_nonneg i)) (by
    have heq : (fun i => Q1 q (WithLp.toLp 1 (0, v i))) =
        (fun i => WithLp.toLp 2 ((0 : U), v i)) := by
      funext i
      apply (WithLp.equiv 2 (U × V)).injective
      simp [Q1]
    rw [heq]
    have ht : Tendsto (fun i => ((0 : U), v i)) atTop (𝓝 ((0 : U), (0 : V))) :=
      tendsto_const_nhds.prodMk_nhds (NullSequences.tendsto_zero v)
    convert ((WithLp.prodContinuousLinearEquiv 2 ℝ U V).symm.continuous.tendsto (0, 0)).comp ht using 1
    · rfl
    · congr 1)

omit hlin h0 hh hi in
@[simp] theorem c0EmbedFun_coord (v : NullSequences.C0 (H := V)) (i : ℕ) :
    WeightedGraph.coord (Q1 q) (c0EmbedFun q v) i = WithLp.toLp 1 (0, v i) :=
  WeightedGraph.coord_ofSequence ..

omit hlin h0 hh hi in
theorem norm_c0EmbedFun (v : NullSequences.C0 (H := V)) : ‖c0EmbedFun q v‖ = ‖v‖ := by
  have hn (i : ℕ) : ‖WeightedGraph.coord (Q1 q) (c0EmbedFun q v) i‖ = ‖v i‖ := by
    simp
  have hq (i : ℕ) : ‖WeightedGraph.output (Q1 q) (c0EmbedFun q v) i‖ = ‖v i‖ := by
    rw [← WeightedGraph.map_coord, c0EmbedFun_coord]
    have ht := WithLp.prod_norm_sq_eq_of_L2 (Q1 q (WithLp.toLp 1 (0, v i)))
    simp only [Q1_fst, Q1_snd, WithLp.toLp_fst, WithLp.toLp_snd, map_zero,
      norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at ht
    nlinarith [norm_nonneg (Q1 q (WithLp.toLp 1 (0, v i))), norm_nonneg (v i)]
  apply le_antisymm
  · rw [WeightedGraph.norm_eq]
    apply max_le
    · simp_rw [hn]
      calc
        _ ≤ ∑' i, WeightedGraph.weight i * ‖v‖ := by
          apply Summable.tsum_le_tsum
          · intro i
            exact mul_le_mul_of_nonneg_left (NullSequences.norm_apply_le v i) (WeightedGraph.weight_nonneg i)
          · simpa only [hn] using WeightedGraph.summable_weighted_norm (Q1 q) (c0EmbedFun q v)
          · exact WeightedGraph.hasSum_weight.summable.mul_right ‖v‖
        _ = ‖v‖ := by rw [tsum_mul_right, WeightedGraph.hasSum_weight.tsum_eq, one_mul]
    · apply (NullSequences.norm_le (norm_nonneg v)).2
      intro i
      rw [hq]
      exact NullSequences.norm_apply_le v i
  · apply (NullSequences.norm_le (norm_nonneg _)).2
    intro i
    rw [← hq]
    exact (NullSequences.norm_apply_le _ i).trans (WeightedGraph.norm_output_le _ _)

omit hlin h0 hh hi in
def c0Embed : NullSequences.C0 (H := V) →ₗᵢ[ℝ] WeightedGraph.Space (Q1 q) where
  toFun := c0EmbedFun q
  map_add' := by
    intro x y
    apply WeightedGraph.ext
    intro i
    change _ = WeightedGraph.coordCLM _ i _
    rw [map_add]
    change _ = WeightedGraph.coord (Q1 q) (c0EmbedFun q x) i +
      WeightedGraph.coord (Q1 q) (c0EmbedFun q y) i
    simp only [c0EmbedFun_coord]
    apply (WithLp.equiv 1 (Free U V × V)).injective
    simp
  map_smul' := by
    intro c x
    apply WeightedGraph.ext
    intro i
    change _ = WeightedGraph.coordCLM _ i _
    rw [map_smul]
    change _ = c • WeightedGraph.coord (Q1 q) (c0EmbedFun q x) i
    simp only [c0EmbedFun_coord]
    apply (WithLp.equiv 1 (Free U V × V)).injective
    simp
  norm_map' := norm_c0EmbedFun q

end Criterion

end LipschitzCounterexample
end

end OAI


