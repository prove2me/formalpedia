-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
-- name    : OAI_Analysis_LipschitzEquivalence_FreeSpace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:06:03.189887+00:00
-- url     : https://prove2.me/theorems/134b4b5e-91bb-47e9-a808-68d7d4cb4518
-- title:
--   The Lipschitz-free space of a pointed metric space
-- statement:
--   For a metric space $M$ with base point $0$, the Lipschitz-free (Arens–Eells) space $\mathcal F(M)$ and its linearization property.
--
--   1. **Lipschitz functions.** $\mathrm{Lip}_0(M)$ is the real vector space of Lipschitz functions $f:M\to\mathbb R$ with $f(0)=0$, normed by the best Lipschitz constant
--   $$
--   \|f\|=\sup_{x\ne y}\frac{|f(x)-f(y)|}{d(x,y)},
--   $$
--   realized through the slope map into $\ell^\infty(M\times M)$. Then $|f(x)-f(y)|\le\|f\|\,d(x,y)$ and $|f(x)|\le d(x,0)\|f\|$.
--   2. **Evaluations.** For $x\in M$ the evaluation $\delta_x(f)=f(x)$ is a bounded functional on $\mathrm{Lip}_0(M)$ with $\delta_0=0$ and $\|\delta_x-\delta_y\|=d(x,y)$, the lower bound coming from the test function $x\mapsto d(x,y)-d(0,y)$.
--   3. **The free space.** $\mathcal F(M)$ is the closed linear span of the $\delta_x$ in the dual of $\mathrm{Lip}_0(M)$. It is a Banach space, separable when $M$ is, and $x\mapsto\delta_x$ is an isometric embedding of $M$ whose finite linear combinations are dense.
--   4. **Linearization.** If $D:M\to F$ is $K$-Lipschitz into a Banach space with $D(0)=0$, then $\|\sum a_xD(x)\|\le K\|\sum a_x\delta_x\|$, and $D$ extends to a bounded linear map $\hat D:\mathcal F(M)\to F$ with $\hat D(\delta_x)=D(x)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/FreeSpace.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/FreeSpace.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LipschitzEquivalence mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LipschitzEquivalence

namespace OAI

universe uM uF

noncomputable section
namespace LipschitzCounterexample

namespace FreeSpace

open scoped NNReal ENNReal

variable (M : Type uM) [MetricSpace M] [Zero M]

def lipZeroSubmodule : Submodule ℝ (M → ℝ) where
  carrier := { f | f 0 = 0 ∧ ∃ K : ℝ≥0, LipschitzWith K f }
  zero_mem' := ⟨rfl, 0, LipschitzWith.const 0⟩
  add_mem' := by
    rintro f g ⟨hf0, K, hf⟩ ⟨hg0, L, hg⟩
    exact ⟨by simp [hf0, hg0], K + L, hf.add hg⟩
  smul_mem' := by
    rintro c f ⟨hf0, K, hf⟩
    exact ⟨by simp [hf0], _, (lipschitzWith_smul c).comp hf⟩

def LipZero : Type _ := lipZeroSubmodule M

instance : AddCommGroup (LipZero M) := inferInstanceAs (AddCommGroup (lipZeroSubmodule M))
instance : Module ℝ (LipZero M) := inferInstanceAs (Module ℝ (lipZeroSubmodule M))

variable {M}

def slopes (f : LipZero M) : lp (fun _ : M × M => ℝ) ∞ :=
  ⟨fun p => (f.1 p.1 - f.1 p.2) / dist p.1 p.2, by
    obtain ⟨K, hK⟩ := f.2.2
    apply memℓp_infty
    refine ⟨(K : ℝ), ?_⟩
    rintro _ ⟨⟨x, y⟩, rfl⟩
    change ‖(f.1 x - f.1 y) / dist x y‖ ≤ (K : ℝ)
    by_cases h : x = y
    · simp [h]
    · rw [norm_div, Real.norm_of_nonneg dist_nonneg]
      apply (div_le_iff₀ (dist_pos.mpr h)).2
      simpa only [Real.norm_eq_abs, Real.dist_eq] using hK.dist_le_mul x y⟩

def slopesLinear : LipZero M →ₗ[ℝ] lp (fun _ : M × M => ℝ) ∞ where
  toFun := slopes
  map_add' := by
    intro f g
    apply Subtype.ext
    funext p
    change ((f.1 p.1 + g.1 p.1) - (f.1 p.2 + g.1 p.2)) / dist p.1 p.2 =
      (f.1 p.1 - f.1 p.2) / dist p.1 p.2 + (g.1 p.1 - g.1 p.2) / dist p.1 p.2
    ring
  map_smul' := by
    intro c f
    apply Subtype.ext
    funext p
    change (c * f.1 p.1 - c * f.1 p.2) / dist p.1 p.2 =
      c * ((f.1 p.1 - f.1 p.2) / dist p.1 p.2)
    ring

theorem slopes_injective : Function.Injective (slopesLinear (M := M)) := by
  intro f g h
  apply Subtype.ext
  funext x
  by_cases hx : x = 0
  · simpa [hx] using f.2.1.trans g.2.1.symm
  · have hx' := congrArg (fun a : lp (fun _ : M × M => ℝ) ∞ => a.1 (x, 0)) h
    change (f.1 x - f.1 0) / dist x 0 = (g.1 x - g.1 0) / dist x 0 at hx'
    simpa [f.2.1, g.2.1] using (div_left_inj' (dist_ne_zero.mpr hx)).mp hx'

instance : NormedAddCommGroup (LipZero M) :=
  NormedAddCommGroup.induced _ _ slopesLinear slopes_injective

instance : NormedSpace ℝ (LipZero M) :=
  NormedSpace.induced ℝ _ _ slopesLinear

theorem norm_le_of_lipschitz (f : LipZero M) {K : ℝ≥0}
    (h : LipschitzWith K f.1) : ‖f‖ ≤ (K : ℝ) := by
  change ‖slopes f‖ ≤ (K : ℝ)
  apply lp.norm_le_of_forall_le K.coe_nonneg
  rintro ⟨x,y⟩
  change ‖(f.1 x - f.1 y) / dist x y‖ ≤ (K : ℝ)
  by_cases hxy : x = y
  · simp [hxy]
  · rw [norm_div, Real.norm_of_nonneg dist_nonneg]
    apply (div_le_iff₀ (dist_pos.mpr hxy)).2
    simpa only [Real.norm_eq_abs, Real.dist_eq] using h.dist_le_mul x y

theorem norm_sub_le (f : LipZero M) (x y : M) :
    ‖f.1 x - f.1 y‖ ≤ ‖f‖ * dist x y := by
  by_cases h : x = y
  · simp [h]
  · have hs := lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) (slopes f) (x,y)
    change ‖(f.1 x - f.1 y) / dist x y‖ ≤ ‖f‖ at hs
    rw [norm_div, Real.norm_of_nonneg dist_nonneg] at hs
    exact (div_le_iff₀ (dist_pos.mpr h)).mp hs

theorem norm_apply_le (f : LipZero M) (x : M) : ‖f.1 x‖ ≤ dist x 0 * ‖f‖ := by
  simpa [f.2.1, mul_comm] using norm_sub_le f x 0

def delta (x : M) : StrongDual ℝ (LipZero M) :=
  ({ toFun := fun f => f.1 x
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : LipZero M →ₗ[ℝ] ℝ).mkContinuous
       (dist x 0) (fun f => norm_apply_le f x)

@[simp] theorem delta_apply (x : M) (f : LipZero M) : delta x f = f.1 x := rfl

@[simp] theorem delta_zero : delta (0 : M) = 0 := by
  ext f
  exact f.2.1

theorem norm_delta_sub_le (x y : M) : ‖delta x - delta y‖ ≤ dist x y := by
  apply ContinuousLinearMap.opNorm_le_bound _ dist_nonneg
  intro f
  simpa only [sub_apply, delta_apply, mul_comm] using norm_sub_le f x y

def distanceTest (y : M) : LipZero M :=
  ⟨fun x => dist x y - dist 0 y, by
    refine ⟨by simp, 1, ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x z
    simpa only [one_mul, NNReal.coe_one, Real.dist_eq, sub_sub_sub_cancel_right]
      using abs_dist_sub_le x z y⟩

theorem norm_distanceTest_le (y : M) : ‖distanceTest y‖ ≤ 1 := by
  apply norm_le_of_lipschitz (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simpa only [distanceTest, one_mul, NNReal.coe_one, Real.dist_eq, sub_sub_sub_cancel_right]
    using abs_dist_sub_le x z y

theorem norm_delta_sub (x y : M) : ‖delta x - delta y‖ = dist x y := by
  apply le_antisymm (norm_delta_sub_le x y)
  have h := (delta x - delta y).le_opNorm (distanceTest y)
  have heq : (delta x - delta y) (distanceTest y) = dist x y := by
    rw [sub_apply, delta_apply, delta_apply]
    simp [distanceTest]
  rw [heq, Real.norm_of_nonneg dist_nonneg] at h
  exact h.trans (mul_le_of_le_one_right (norm_nonneg _) (norm_distanceTest_le _))

def freeSubmodule : Submodule ℝ (StrongDual ℝ (LipZero M)) :=
  (Submodule.span ℝ (Set.range (delta (M := M)))).topologicalClosure

def Space (M : Type uM) [MetricSpace M] [Zero M] : Type _ := freeSubmodule (M := M)

instance : NormedAddCommGroup (Space M) :=
  inferInstanceAs (NormedAddCommGroup (freeSubmodule (M := M)))

instance : NormedSpace ℝ (Space M) :=
  inferInstanceAs (NormedSpace ℝ (freeSubmodule (M := M)))

instance : CompleteSpace (Space M) := by
  have : IsClosed (freeSubmodule (M := M) : Set (StrongDual ℝ (LipZero M))) :=
    Submodule.isClosed_topologicalClosure _
  exact inferInstanceAs (CompleteSpace (freeSubmodule (M := M)))

def point (x : M) : Space M :=
  ⟨delta x, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x, rfl⟩)⟩

@[simp] theorem point_zero : point (0 : M) = 0 := by
  apply Subtype.ext
  exact delta_zero

theorem isometry_point : Isometry (point (M := M)) := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (delta x) (delta y) = dist x y
  rw [dist_eq_norm, norm_delta_sub]

def inclusion : Space M →ₗᵢ[ℝ] StrongDual ℝ (LipZero M) where
  toFun := fun x => x.1
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  norm_map' := fun _ => rfl

theorem dense_combinations :
    DenseRange (Finsupp.linearCombination ℝ (point (M := M))) := by
  intro x
  rw [inclusion.isometry.isEmbedding.closure_eq_preimage_closure_image]
  change x.1 ∈ closure (inclusion '' Set.range (Finsupp.linearCombination ℝ point))
  have hi : inclusion '' Set.range (Finsupp.linearCombination ℝ (point (M := M))) =
      (Submodule.span ℝ (Set.range (delta (M := M))) : Set (StrongDual ℝ (LipZero M))) := by
    rw [← Finsupp.range_linearCombination]
    ext y
    constructor
    · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, (Finsupp.apply_linearCombination ℝ inclusion.toLinearMap point a).symm⟩
    · rintro ⟨a, rfl⟩
      refine ⟨Finsupp.linearCombination ℝ point a, ⟨a, rfl⟩, ?_⟩
      exact Finsupp.apply_linearCombination ℝ inclusion.toLinearMap point a
  rw [hi]
  exact x.2

instance [TopologicalSpace.SeparableSpace M] : TopologicalSpace.SeparableSpace (Space M) := by
  have hc : Continuous (delta (M := M)) :=
    continuous_subtype_val.comp isometry_point.continuous
  have hs := TopologicalSpace.isSeparable_range hc
  exact hs.span.closure.separableSpace

section Linearization
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (D : M → F) {K : ℝ≥0} (hD : LipschitzWith K D) (h0 : D 0 = 0)

def pullback (g : StrongDual ℝ F) : LipZero M :=
  ⟨fun x => g (D x), by
    refine ⟨by simp [h0], _, g.lipschitz.comp hD⟩⟩

theorem norm_pullback_le (g : StrongDual ℝ F) :
    ‖pullback D hD h0 g‖ ≤ ‖g‖ * K :=
  by simpa using norm_le_of_lipschitz (pullback D hD h0 g) (g.lipschitz.comp hD)

include hD h0

theorem combination_pairing (g : StrongDual ℝ F) (a : M →₀ ℝ) :
    g (Finsupp.linearCombination ℝ D a) =
      (Finsupp.linearCombination ℝ point a).1 (pullback D hD h0 g) := by
  classical
  change g (Finsupp.linearCombination ℝ D a) =
    inclusion (Finsupp.linearCombination ℝ point a) (pullback D hD h0 g)
  change g (Finsupp.linearCombination ℝ D a) =
    (inclusion.toLinearMap (Finsupp.linearCombination ℝ point a)) (pullback D hD h0 g)
  rw [Finsupp.apply_linearCombination ℝ inclusion.toLinearMap]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    sum_apply, smul_apply]
  rfl

theorem norm_combination_le (a : M →₀ ℝ) :
    ‖Finsupp.linearCombination ℝ D a‖ ≤ K * ‖Finsupp.linearCombination ℝ point a‖ := by
  apply NormedSpace.norm_le_dual_bound ℝ _ (mul_nonneg K.coe_nonneg (norm_nonneg _))
  intro g
  rw [combination_pairing D hD h0]
  have h := (Finsupp.linearCombination ℝ point a).1.le_opNorm (pullback D hD h0 g)
  calc
    _ ≤ ‖(Finsupp.linearCombination ℝ point a).1‖ * ‖pullback D hD h0 g‖ := h
    _ ≤ ‖Finsupp.linearCombination ℝ point a‖ * (‖g‖ * K) := by
      change ‖Finsupp.linearCombination ℝ point a‖ * ‖pullback D hD h0 g‖ ≤ _
      exact mul_le_mul_of_nonneg_left (norm_pullback_le D hD h0 g) (norm_nonneg _)
    _ = K * ‖Finsupp.linearCombination ℝ point a‖ * ‖g‖ := by ring

variable [CompleteSpace F]

omit hD h0 in

def linearize : Space M →L[ℝ] F :=
  (Finsupp.linearCombination ℝ D).extendOfNorm (Finsupp.linearCombination ℝ point)

@[simp] theorem linearize_point (x : M) : linearize D (point x) = D x := by
  have h := LinearMap.extendOfNorm_eq (f := Finsupp.linearCombination ℝ D)
    dense_combinations ⟨K, norm_combination_le D hD h0⟩ (Finsupp.single x 1)
  simpa [linearize] using h

end Linearization

end FreeSpace

end LipschitzCounterexample
end

end OAI


