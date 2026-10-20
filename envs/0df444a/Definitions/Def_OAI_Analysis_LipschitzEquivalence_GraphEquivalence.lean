-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
-- name    : OAI_Analysis_LipschitzEquivalence_GraphEquivalence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:16:56.151848+00:00
-- url     : https://prove2.me/theorems/ab218492-5592-4be5-ab5d-ce2b806bd3cd
-- title:
--   A Lipschitz criterion relating free spaces and ℓ¹-sums
-- statement:
--   For real normed spaces $U,V$, let $W=U\oplus_2V$ and let $\mathcal F(W)$ be its Lipschitz-free space.
--
--   1. **Spaces and maps.** Given a bounded operator $q:\mathcal F(W)\to U$, put $S=\mathcal F(W)\oplus_1V$ and $Q_1(\mu,v)=(q\mu,v)\in W$; then $\|Q_1\|\le\max(\|q\|,1)$. Define the Lipschitz map
--   $$
--   B(\mu,v)=\mu+\delta_{Q_1(\mu,v)}\in\mathcal F(W),
--   $$
--   with $B(0)=0$ and Lipschitz constant $1+\max(\|q\|,1)$.
--   2. **Inverse.** Suppose $h:W\to U$ is a bijection with $q(\delta_x)=h(x)-x_U$ for all $x\in W$, where $x_U$ is the $U$-component of $x$. Then $q\circ B=h\circ Q_1$. The map
--   $$
--   B^{-1}(z)=\bigl(z-\delta_{h^{-1}(qz)},\ (h^{-1}(qz))_V\bigr)
--   $$
--   is a two-sided inverse of $B$, and it is $(1+2\|q\|A)$-Lipschitz when $h^{-1}$ is $A$-Lipschitz.
--
--   So $B$ is a bi-Lipschitz bijection between $S$ and $\mathcal F(W)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/GraphEquivalence.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/GraphEquivalence.lean by skeleton subtraction
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

namespace OAI

universe uU uV

noncomputable section
namespace LipschitzCounterexample

namespace Criterion
open scoped NNReal ENNReal Topology
open Filter
variable {U : Type uU} {V : Type uV} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

abbrev Domain (U : Type uU) (V : Type uV) := WithLp 2 (U × V)
abbrev Free (U : Type uU) (V : Type uV) [NormedAddCommGroup U] [NormedAddCommGroup V] :=
  FreeSpace.Space (Domain U V)
abbrev Sum (U : Type uU) (V : Type uV) [NormedAddCommGroup U] [NormedAddCommGroup V] :=
  WithLp 1 (Free U V × V)

variable (q : Free U V →L[ℝ] U)

def Q1 : Sum U V →L[ℝ] Domain U V :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ U V).symm.toContinuousLinearMap.comp
    ((q.comp (WithLp.fstL 1 ℝ (Free U V) V)).prod (WithLp.sndL 1 ℝ (Free U V) V))

@[simp] theorem Q1_fst (x : Sum U V) : (Q1 q x).fst = q x.fst := rfl
@[simp] theorem Q1_snd (x : Sum U V) : (Q1 q x).snd = x.snd := rfl

theorem norm_Q1_le (x : Sum U V) : ‖Q1 q x‖ ≤ max ‖q‖ 1 * ‖x‖ := by
  have he := q.le_opNorm x.fst
  have hq : ‖q‖ ≤ max ‖q‖ 1 := le_max_left _ _
  have h1 : (1 : ℝ) ≤ max ‖q‖ 1 := le_max_right _ _
  have hn : ‖Q1 q x‖ ≤ ‖q x.fst‖ + ‖x.snd‖ := by
    have ht := WithLp.prod_norm_sq_eq_of_L2 (Q1 q x)
    simp only [Q1_fst, Q1_snd] at ht
    nlinarith [norm_nonneg (Q1 q x), norm_nonneg (q x.fst), norm_nonneg x.snd]
  rw [WithLp.prod_norm_eq_of_L1]
  calc
    _ ≤ ‖q x.fst‖ + ‖x.snd‖ := hn
    _ ≤ (max ‖q‖ 1) * ‖x.fst‖ + (max ‖q‖ 1) * ‖x.snd‖ := by
      apply add_le_add
      · exact he.trans (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
      · nlinarith [norm_nonneg x.snd]
    _ = _ := by ring

theorem lipschitz_Q1 : LipschitzWith (max ‖q‖₊ 1) (Q1 q) := by
  apply lipschitzWith_iff_norm_sub_le.2
  intro x y
  rw [← map_sub]
  exact norm_Q1_le q (x-y)

def B (x : Sum U V) : Free U V := x.fst + FreeSpace.point (Q1 q x)

@[simp] theorem B_zero : B q 0 = 0 := by simp [B]

theorem lipschitz_B : LipschitzWith (1 + max ‖q‖₊ 1) (B q) := by
  apply lipschitzWith_iff_norm_sub_le.2
  intro x y
  have he : ‖x.fst - y.fst‖ ≤ ‖x-y‖ := WithLp.norm_fst_le (Free U V) (x-y)
  have hd : ‖FreeSpace.point (Q1 q x) - FreeSpace.point (Q1 q y)‖ ≤
      (max ‖q‖ 1) * ‖x-y‖ := by
    rw [← dist_eq_norm, FreeSpace.isometry_point.dist_eq, dist_eq_norm]
    exact (lipschitz_Q1 q).norm_sub_le x y
  calc
    ‖B q x - B q y‖ = ‖(x.fst-y.fst) + (FreeSpace.point (Q1 q x)-FreeSpace.point (Q1 q y))‖ := by
      congr 1
      simp only [B]
      abel
    _ ≤ ‖x.fst-y.fst‖ + ‖FreeSpace.point (Q1 q x)-FreeSpace.point (Q1 q y)‖ := norm_add_le _ _
    _ ≤ (1 + max ‖q‖₊ 1 : ℝ≥0) * ‖x-y‖ := by
      simp only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_max, coe_nnnorm]
      linarith

variable (h : Domain U V ≃ U)
  (hlin : ∀ x : Domain U V, q (FreeSpace.point x) = h x - x.fst)

include hlin in
theorem diagram (x : Sum U V) : q (B q x) = h (Q1 q x) := by
  rw [B, map_add, hlin, Q1_fst]
  abel

def Binv (z : Free U V) : Sum U V :=
  WithLp.toLp 1 (z - FreeSpace.point (h.symm (q z)), (h.symm (q z)).snd)

include hlin in
theorem Q1_Binv (z : Free U V) : Q1 q (Binv q h z) = h.symm (q z) := by
  apply (WithLp.equiv 2 (U × V)).injective
  apply Prod.ext
  · change q (z - FreeSpace.point (h.symm (q z))) = (h.symm (q z)).fst
    rw [map_sub, hlin, h.apply_symm_apply]
    abel
  · rfl

include hlin in
theorem B_Binv (z : Free U V) : B q (Binv q h z) = z := by
  rw [B, Q1_Binv q h hlin]
  change z - FreeSpace.point (h.symm (q z)) + FreeSpace.point (h.symm (q z)) = z
  abel

include hlin in
theorem Binv_B (x : Sum U V) : Binv q h (B q x) = x := by
  apply (WithLp.equiv 1 (Free U V × V)).injective
  apply Prod.ext
  · change B q x - FreeSpace.point (h.symm (q (B q x))) = x.fst
    rw [diagram q h hlin, h.symm_apply_apply, B]
    abel
  · change (h.symm (q (B q x))).snd = x.snd
    rw [diagram q h hlin, h.symm_apply_apply, Q1_snd]

omit hlin [NormedSpace ℝ V] in
theorem lipschitz_Binv {A : ℝ≥0} (hh : LipschitzWith A h.symm) :
    LipschitzWith (1 + 2 * ‖q‖₊ * A) (Binv q h) := by
  apply lipschitzWith_iff_norm_sub_le.2
  intro z t
  have hx : ‖h.symm (q z) - h.symm (q t)‖ ≤ (‖q‖ * A) * ‖z-t‖ := by
    calc
      _ ≤ A * ‖q z - q t‖ := hh.norm_sub_le _ _
      _ ≤ A * (‖q‖ * ‖z-t‖) := mul_le_mul_of_nonneg_left (q.lipschitz.norm_sub_le z t) A.coe_nonneg
      _ = _ := by ring
  have hp : ‖FreeSpace.point (h.symm (q z)) - FreeSpace.point (h.symm (q t))‖ =
      ‖h.symm (q z) - h.symm (q t)‖ := by
    simpa only [dist_eq_norm] using FreeSpace.isometry_point.dist_eq (h.symm (q z)) (h.symm (q t))
  have hs : ‖(h.symm (q z)).snd-(h.symm (q t)).snd‖ ≤ ‖h.symm (q z)-h.symm (q t)‖ :=
    WithLp.norm_snd_le U (h.symm (q z) - h.symm (q t))
  rw [WithLp.prod_norm_eq_of_L1]
  change ‖(z-FreeSpace.point (h.symm (q z)))-(t-FreeSpace.point (h.symm (q t)))‖ +
    ‖(h.symm (q z)).snd-(h.symm (q t)).snd‖ ≤ _
  have he : ‖(z-FreeSpace.point (h.symm (q z)))-(t-FreeSpace.point (h.symm (q t)))‖ ≤
      ‖z-t‖ + ‖h.symm (q z)-h.symm (q t)‖ := by
    rw [show (z-FreeSpace.point (h.symm (q z)))-(t-FreeSpace.point (h.symm (q t))) =
      (z-t)-(FreeSpace.point (h.symm (q z))-FreeSpace.point (h.symm (q t))) by abel]
    exact (norm_sub_le _ _).trans (by rw [hp])
  simp only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_ofNat, coe_nnnorm]
  nlinarith

end Criterion

end LipschitzCounterexample
end

end OAI


