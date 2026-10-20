-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
-- name    : OAI_Analysis_LipschitzEquivalence_SlotRadii
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:24:59.718142+00:00
-- url     : https://prove2.me/theorems/293b0e59-0829-467c-8bac-18827c56872e
-- title:
--   Tail radii of points in the slot domain
-- statement:
--   Radius functions on the slot domain $\mathcal D=\mathcal H\oplus_2\ell^2$, where $\mathcal H=\bigl(\bigoplus_nE_n\bigr)_{\ell^2}$.
--
--   1. **Local energy.** For $x=(u,v)\in\mathcal D$ and $n\in\mathbb N$, let
--   $$
--   a_n(x)^2=\|u_n\|^2+\|u_{\lfloor n/2\rfloor}\|^2+|v_{\lfloor n/2\rfloor}|^2 ,
--   $$
--   the energy of slot $n$ and its parent slot. Then $\sum_na_n(x)^2=3\|u\|^2+2\|v\|^2$, since each parent index is used twice.
--   2. **Radius map.** The blocks $(u_n,u_{\lfloor n/2\rfloor},v_{\lfloor n/2\rfloor})$ form an element of a Hilbert sum of norm at most $\sqrt3\,\|x\|$, linearly in $x$.
--   3. **Radii.** The $N$-th radius $\rho_N(x)$ is the norm of the tail from index $N$ of this element, so
--   $$
--   \rho_N(x)^2-\rho_{N+1}(x)^2=a_N(x)^2 .
--   $$
--   The radii are antitone in $N$ and each $\rho_N$ is $\sqrt3$-Lipschitz.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SlotRadii.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SlotRadii.lean by skeleton subtraction
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

namespace OAI

universe uE

noncomputable section
namespace LipschitzCounterexample

namespace HilbertSlots
open scoped ENNReal NNReal
open Filter Topology
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

theorem hasSum_parent {b : ℕ → ℝ} {B : ℝ} (hb : HasSum b B) :
    HasSum (fun n => b (n / 2)) (2 * B) := by
  rw [two_mul]
  apply Equiv.natSumNatEquivNat.hasSum_iff.1
  apply HasSum.sum
  · simpa [Function.comp_def, Nat.mul_add_div] using hb
  · simpa [Function.comp_def, Nat.mul_add_div] using hb

abbrev SlotDomain (E : ℕ → Type uE) [∀ i, NormedAddCommGroup (E i)] :=
  WithLp 2 (HilbertSum E × RealL2)
abbrev RadiusBlock (E : ℕ → Type uE) [∀ i, NormedAddCommGroup (E i)] (n : ℕ) :=
  WithLp 2 (E n × WithLp 2 (E (n/2) × ℝ))

def aSq (x : SlotDomain E) (n : ℕ) : ℝ :=
  ‖x.fst n‖^2 + ‖x.fst (n/2)‖^2 + ‖x.snd (n/2)‖^2

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem aSq_nonneg (x : SlotDomain E) (n : ℕ) : 0 ≤ aSq x n := by
  unfold aSq
  positivity

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem hasSum_aSq (x : SlotDomain E) :
    HasSum (aSq x) (3 * ‖x.fst‖^2 + 2 * ‖x.snd‖^2) := by
  have hu : HasSum (fun n => ‖x.fst n‖^2) (‖x.fst‖^2) := by
    simpa using lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x.fst
  have hv : HasSum (fun n => ‖x.snd n‖^2) (‖x.snd‖^2) := by
    simpa using lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x.snd
  convert (hu.add (hasSum_parent hu)).add (hasSum_parent hv) using 1
  · rfl
  · ring

def radiusBlock (x : SlotDomain E) (n : ℕ) : RadiusBlock E n :=
  WithLp.toLp 2 (x.fst n, WithLp.toLp 2 (x.fst (n/2), x.snd (n/2)))

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem radiusBlock_norm_sq (x : SlotDomain E) (n : ℕ) :
    ‖radiusBlock x n‖^2 = aSq x n := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  simp only [radiusBlock, WithLp.toLp_fst, WithLp.toLp_snd, aSq]
  ring

def radiusSeq (x : SlotDomain E) : HilbertSum (RadiusBlock E) :=
  ⟨radiusBlock x, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, radiusBlock_norm_sq] using
      (hasSum_aSq x).summable)⟩

omit [∀ i, InnerProductSpace ℝ (E i)] in
@[simp] theorem radiusSeq_apply (x : SlotDomain E) (n : ℕ) : radiusSeq x n = radiusBlock x n := rfl

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem radiusSeq_norm_sq (x : SlotDomain E) :
    ‖radiusSeq x‖^2 = 3 * ‖x.fst‖^2 + 2 * ‖x.snd‖^2 := by
  rw [norm_sq_tsum]
  simp only [radiusSeq_apply, radiusBlock_norm_sq]
  exact (hasSum_aSq x).tsum_eq

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem radiusSeq_norm_le (x : SlotDomain E) : ‖radiusSeq x‖ ≤ Real.sqrt 3 * ‖x‖ := by
  have h := radiusSeq_norm_sq x
  have hx := WithLp.prod_norm_sq_eq_of_L2 x
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).1
  rw [mul_pow, hs]
  nlinarith [sq_nonneg ‖x.snd‖]

def radiusCLM : SlotDomain E →L[ℝ] HilbertSum (RadiusBlock E) :=
  ({ toFun := radiusSeq
     map_add' := by
       intro x y
       apply lp.ext
       funext n
       apply (WithLp.equiv 2 (E n × WithLp 2 (E (n/2) × ℝ))).injective
       simp [radiusSeq, radiusBlock]
       rfl
     map_smul' := by
       intro c x
       apply lp.ext
       funext n
       apply (WithLp.equiv 2 (E n × WithLp 2 (E (n/2) × ℝ))).injective
       simp [radiusSeq, radiusBlock]
       rfl } : SlotDomain E →ₗ[ℝ] HilbertSum (RadiusBlock E)).mkContinuous
    (Real.sqrt 3) radiusSeq_norm_le

def tailCLM (N : ℕ) : HilbertSum E →L[ℝ] HilbertSum E :=
  ContinuousLinearMap.id ℝ (HilbertSum E) -
    ∑ i ∈ Finset.range N, (lp.singleContinuousLinearMap ℝ E 2 i).comp (lp.evalCLM ℝ E 2 i)

@[simp] theorem tailCLM_apply (N : ℕ) (x : HilbertSum E) : tailCLM N x = x - cutHead N x := by
  simp only [tailCLM, sub_apply, ContinuousLinearMap.id_apply,
    sum_apply, ContinuousLinearMap.comp_apply, cutHead,
    lp.singleContinuousLinearMap_apply]
  rfl

theorem tail_norm_le (N : ℕ) (x : HilbertSum E) : ‖tailCLM N x‖ ≤ ‖x‖ := by
  have hh := norm_sub_prefix_sq x N
  have hn : 0 ≤ ∑ i ∈ Finset.range N, ‖x i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [tailCLM_apply]
  nlinarith [norm_nonneg (x-cutHead N x), norm_nonneg x]

def radius (N : ℕ) (x : SlotDomain E) : ℝ := ‖tailCLM N (radiusCLM x)‖

theorem radius_nonneg (N : ℕ) (x : SlotDomain E) : 0 ≤ radius N x := norm_nonneg _

theorem radius_sq (N : ℕ) (x : SlotDomain E) :
    radius N x ^ 2 = ‖radiusSeq x‖^2 - ∑ i ∈ Finset.range N, aSq x i := by
  simpa [radius, radiusCLM, radiusSeq_apply, radiusBlock_norm_sq] using norm_sub_prefix_sq (radiusSeq x) N

theorem radius_step (N : ℕ) (x : SlotDomain E) :
    aSq x N = radius N x ^ 2 - radius (N+1) x ^ 2 := by
  rw [radius_sq, radius_sq, Finset.sum_range_succ]
  ring

theorem radius_antitone (x : SlotDomain E) : Antitone (fun N => radius N x) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := radius_step n x
  nlinarith [aSq_nonneg x n, radius_nonneg n x, radius_nonneg (n+1) x]

theorem radius_lipschitz (N : ℕ) : LipschitzWith ⟨Real.sqrt 3, Real.sqrt_nonneg _⟩ (radius (E := E) N) := by
  apply lipschitzWith_iff_norm_sub_le.2
  intro x y
  change ‖‖tailCLM N (radiusCLM x)‖ - ‖tailCLM N (radiusCLM y)‖‖ ≤ _
  rw [Real.norm_eq_abs]
  apply (abs_norm_sub_norm_le _ _).trans
  rw [← map_sub, ← map_sub]
  exact (tail_norm_le N _).trans (radiusSeq_norm_le (x-y))

end HilbertSlots

end LipschitzCounterexample
end

end OAI


