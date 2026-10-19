-- Prove2me | Definitions.Def_OAIQWSP000
-- name    : OAIQWSP000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:29:24.148554+00:00
-- url     : https://prove2.me/theorems/9fc73334-8ac8-4ba5-80c8-3b59c3267e38
-- title:
--   OpenAI symmetric polar products split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of `OAI.SymmetricPolar.symmetric_polar_main`: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Geometry/PolarProducts` (OpenAI, *Symplectic Balls in Symmetric Polar Products*, OpenAI Math Release, September 22, 2026, result family 087, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It also contains the lemmas those definitions use in their bodies, and the lemmas those lemmas need. Several definitions are built from proofs: for example the ODE flow `SmoothODE.trajectory` and the time-step homeomorphism `SmoothODE.stepHomeomorph` use lemmas of the development in their bodies. It also contains OpenAI's `@[simp]` lemmas about these definitions, and OpenAI's `local instance` lines.
--
--   The definitions of the published statement (`Position`, `Phase`, `IsSymmetricConvexBody`, `polar`, `polarProduct`, `capacityBall`, `omega0`, `HasSymplecticEmbedding`, `gromovWidth`) are not repeated: the bundle imports them from the published bundle `Def_SymmetricPolar`. It imports no other bundle.
--
--   Modules: `CanonicalCoordinates.lean`, `CanonicalCylinder.lean`, `CompleteFlow.lean`, `Contraction.lean`, `EmbeddingInverse.lean`, `ExteriorHamiltonian.lean`, `FiniteDescent.lean`, `FourierIntegrals.lean`, `FourierPaths.lean`, `GalerkinBounds.lean`, `GradientLinking.lean`, `HamiltonianGrowth.lean`, `HolomorphicBalls.lean`, `HorizontalIntegrals.lean`, `LensArea.lean`, `LensBounds.lean`, `LensEstimates.lean`, `LensMap.lean`, `LocalODE.lean`, `LogProfile.lean`, `MomentumBounds.lean`, `MoserField.lean`, `MoserFlow.lean`, `Nonsqueezing.lean`, `PeriodicFourier.lean`, `PeriodicSolutions.lean`, `PlanarSquare.lean`, `PotentialDeformation.lean`, `PotentialForms.lean`, `QuadraticAction.lean`, `RadialMap.lean`, `RegularizedMaximum.lean`, `SmoothPaths.lean`, `SmoothProfiles.lean`, `StripEmbedding.lean`, `StripMaps.lean`, `TensorCalculus.lean`, `TipEstimates.lean`.
--
--   The theorems of the development that the definitions do not need are proved in the solutions of this split. Three of them, including the two classical results Gromov's non-squeezing theorem (`CylinderNonsqueezing.radius_le_of_map`) and Moser's deformation lemma (`Moser.compactlySupported_deformation`), are published as statements, each with its own proof. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Symplectic Balls in Symmetric Polar Products, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 087; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Balls-in-Symmetric-Polar-Products-September-22-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/PolarProducts at commit adc7f12

import Mathlib
import Definitions.Def_SymmetricPolar

section
-- module Solutions.OAIQW_SymmetricPolar.Contraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

section LowerBoundInline

open Set Filter Function
open scoped Topology ContDiff NNReal

namespace SmoothContraction

variable {E : Type u1} {F : Type u2} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

noncomputable section

def fixedPoint {f : E × F → F} {L : ℝ≥0}
    (hL : L < 1) (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) (x : E) : F :=
  ContractingWith.fixedPoint (fun y => f (x, y)) ⟨hL, hLip x⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedSpace ℝ F] in
theorem fixedPoint_eq {f : E × F → F} {L : ℝ≥0}
    (hL : L < 1) (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) (x : E) :
    f (x, fixedPoint hL hLip x) = fixedPoint hL hLip x :=
  (show ContractingWith L (fun y => f (x, y)) from ⟨hL, hLip x⟩).fixedPoint_isFixedPt

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedSpace ℝ F] in
theorem eq_fixedPoint {f : E × F → F} {L : ℝ≥0}
    (hL : L < 1) (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) (x : E) {y : F}
    (hy : f (x, y) = y) : y = fixedPoint hL hLip x :=
  (show ContractingWith L (fun y => f (x, y)) from ⟨hL, hLip x⟩).fixedPoint_unique hy

omit [CompleteSpace E] in

theorem partial_isInvertible {f : E × F → F} {L : ℝ≥0}
    (hf : Differentiable ℝ f) (hL : L < 1)
    (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) (u : E × F) :
    ((fderiv ℝ (fun p : E × F => p.2 - f p) u).comp
      (ContinuousLinearMap.inr ℝ E F)).IsInvertible := by
  let A := (fderiv ℝ f u).comp (ContinuousLinearMap.inr ℝ E F)
  have hA : HasFDerivAt (fun y => f (u.1, y)) A u.2 :=
    (hf u).hasFDerivAt.comp u.2 (hasFDerivAt_prodMk_right u.1 u.2)
  have hnorm : ‖A‖ < 1 := by
    rw [← hA.fderiv]
    exact (norm_fderiv_le_of_lipschitz ℝ (hLip u.1)).trans_lt (by exact_mod_cast hL)
  have heq : (fderiv ℝ (fun p : E × F => p.2 - f p) u).comp
      (ContinuousLinearMap.inr ℝ E F) = 1 - A := by
    change (fderiv ℝ (Prod.snd - f) u).comp _ = _
    rw [(hasFDerivAt_snd.sub (hf u).hasFDerivAt).fderiv]
    ext y
    simp [A]
  rw [heq]
  obtain ⟨v, hv⟩ := isUnit_one_sub_of_norm_lt_one hnorm
  exact ⟨ContinuousLinearEquiv.ofUnit v, hv⟩

theorem contDiff_fixedPoint {f : E × F → F} {L : ℝ≥0}
    (hf : ContDiff ℝ ∞ f) (hL : L < 1)
    (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) :
    ContDiff ℝ ∞ (fixedPoint hL hLip) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  let y := fixedPoint hL hLip x
  let g : E × F → F := fun p => p.2 - f p
  have hg : ContDiffAt ℝ ∞ g (x, y) := (contDiff_snd.sub hf).contDiffAt
  have hi := partial_isInvertible (hf.differentiable (by simp)) hL hLip (x, y)
  let ψ := hg.implicitFunction (by simp) hi
  have hψ : ContDiffAt ℝ ∞ ψ x := hg.contDiffAt_implicitFunction (by simp) hi
  have hzero : g (x, y) = 0 := sub_eq_zero.mpr (fixedPoint_eq hL hLip x).symm
  have hnear : ψ =ᶠ[𝓝 x] fixedPoint hL hLip := by
    filter_upwards [hg.eventually_apply_implicitFunction (by simp) hi] with x' hx'
    apply eq_fixedPoint hL hLip x'
    have : g (x', ψ x') = 0 := hx'.trans hzero
    exact (sub_eq_zero.mp this).symm
  exact hψ.congr_of_eventuallyEq hnear.symm

end
end SmoothContraction

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.SmoothPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal

open Set Filter Metric
open scoped Topology ContDiff

namespace SmoothPaths

universe u v

variable {X : Type v} {E F : Type u} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable section

def applyField (A : C(X, E →L[ℝ] F)) : C(X, E) →L[ℝ] C(X, F) := by
  let L : C(X, E) →ₗ[ℝ] C(X, F) :=
    { toFun := fun u => ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  apply L.mkContinuous ‖A‖
  intro u
  apply (ContinuousMap.norm_le (L u) (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
  intro t
  exact ((A t).le_opNorm (u t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
      (norm_nonneg _) (norm_nonneg _))

@[simp] theorem applyField_apply (A : C(X, E →L[ℝ] F)) (u : C(X, E)) (t : X) :
    applyField A u t = A t (u t) := rfl

def applyFieldCLM : C(X, E →L[ℝ] F) →L[ℝ] C(X, E) →L[ℝ] C(X, F) := by
  let L : C(X, E →L[ℝ] F) →ₗ[ℝ] (C(X, E) →L[ℝ] C(X, F)) :=
    { toFun := fun A => applyField A
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hL : ∀ A : C(X, E →L[ℝ] F), ‖L A‖ ≤ 1 * ‖A‖ := by
    intro A
    rw [one_mul]
    apply (applyField A).opNorm_le_bound (norm_nonneg A)
    intro u
    apply (ContinuousMap.norm_le (applyField A u)
      (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
    intro t
    exact ((A t).le_opNorm (u t)).trans
      (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
        (norm_nonneg _) (norm_nonneg _))
  exact LinearMap.mkContinuous (σ := RingHom.id ℝ)
    (E := C(X, E →L[ℝ] F)) (F := C(X, E) →L[ℝ] C(X, F)) L 1 hL

@[simp] theorem applyFieldCLM_apply (A : C(X, E →L[ℝ] F)) :
    applyFieldCLM A = applyField A := rfl

def superpose {f : E → F} (hf : Continuous f) (u : C(X, E)) : C(X, F) :=
  ⟨fun t => f (u t), hf.comp u.continuous⟩

omit [CompactSpace X] [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem superpose_apply {f : E → F} (hf : Continuous f)
    (u : C(X, E)) (t : X) : superpose hf u t = f (u t) := rfl

omit [CompactSpace X] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem continuous_superpose {f : E → F} (hf : Continuous f) :
    Continuous (superpose (X := X) hf) :=
  ContinuousMap.continuous_postcomp ⟨f, hf⟩

theorem hasFDerivAt_superpose [ProperSpace E] {f : E → F}
    (hf : Differentiable ℝ f) (hf' : Continuous (fderiv ℝ f)) (u : C(X, E)) :
    HasFDerivAt (superpose hf.continuous)
      (applyField (superpose hf' u)) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have huc : UniformContinuousOn (fderiv ℝ f) (closedBall (0 : E) (‖u‖ + 2)) :=
    (isCompact_closedBall (0 : E) (‖u‖ + 2)).uniformContinuousOn_of_continuous hf'.continuousOn
  obtain ⟨δ, hδ, hbound⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : C(X, E)) (lt_min hδ zero_lt_one)] with h hh
  have hhδ : ‖h‖ < δ := (mem_ball_zero_iff.mp hh).trans_le (min_le_left _ _)
  have hh1 : ‖h‖ < 1 := (mem_ball_zero_iff.mp hh).trans_le (min_le_right _ _)
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro t
  have hu : ‖u t‖ ≤ ‖u‖ := u.norm_coe_le_norm t
  have hsmall : ‖h t‖ < δ := (h.norm_coe_le_norm t).trans_lt hhδ
  have hsmall1 : ‖h t‖ < 1 := (h.norm_coe_le_norm t).trans_lt hh1
  have hut : u t ∈ closedBall (0 : E) (‖u‖ + 2) := by
    rw [mem_closedBall_zero_iff]; linarith
  have hall : ∀ y ∈ ball (u t) (min δ 1),
      ‖fderiv ℝ f y - fderiv ℝ f (u t)‖ ≤ ε := by
    intro y hy
    have hdist : dist y (u t) < δ := hy.trans_le (min_le_left _ _)
    have hdist1 : dist y (u t) < 1 := hy.trans_le (min_le_right _ _)
    have hyball : y ∈ closedBall (0 : E) (‖u‖ + 2) := by
      rw [mem_closedBall_zero_iff]
      have hn := norm_le_norm_sub_add y (u t)
      rw [← dist_eq_norm] at hn
      linarith
    exact le_of_lt (by simpa only [dist_eq_norm] using hbound y hyball (u t) hut hdist)
  have hu0 : u t ∈ ball (u t) (min δ 1) := mem_ball_self (lt_min hδ zero_lt_one)
  have huh : u t + h t ∈ ball (u t) (min δ 1) := by
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact lt_min hsmall hsmall1
  have he := (convex_ball (u t) (min δ 1)).norm_image_sub_le_of_norm_fderiv_le'
    (fun _ _ => hf _) hall hu0 huh
  simp only [add_sub_cancel_left] at he
  exact he.trans (mul_le_mul_of_nonneg_left (h.norm_coe_le_norm t) hε.le)

theorem contDiff_superpose_nat [ProperSpace E] (n : ℕ) {f : E → F}
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (superpose (X := X) hf.continuous) := by
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr (continuous_superpose hf.continuous)
  | succ n ih =>
    have hn : (↑(n + 1) : WithTop ℕ∞) ≠ 0 := by simp
    have hd : Differentiable ℝ f := hf.differentiable hn
    have hcd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hc : ContDiff ℝ n (fun u : C(X, E) => applyField (superpose hcd.continuous u)) :=
      by simpa only [Function.comp_def, applyFieldCLM_apply] using
        (applyFieldCLM (X := X) (E := E) (F := F)).contDiff.comp (ih hcd)
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨_, hc, hasFDerivAt_superpose hd hcd.continuous⟩

theorem contDiff_superpose [ProperSpace E] {f : E → F}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (superpose (X := X) hf.continuous) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_superpose_nat n (contDiff_infty.mp hf n)

end
end SmoothPaths

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.LocalODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u3 u4 u5 u6

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace SmoothODE

abbrev Time := Icc (0 : ℝ) 1

variable {E : Type u3} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

def extend (u : C(Time, E)) : ℝ → E := fun t => u (projIcc 0 1 zero_le_one t)

omit [NormedSpace ℝ E] in
theorem continuous_extend (u : C(Time, E)) : Continuous (extend u) :=
  u.continuous.comp continuous_projIcc

omit [NormedSpace ℝ E] in
@[simp] theorem extend_coe (u : C(Time, E)) (t : Time) : extend u t = u t := by
  simp [extend]

def primitive (u : C(Time, E)) : C(Time, E) :=
  ⟨fun t => ∫ s in 0..(t : ℝ), extend u s,
    (intervalIntegral.continuous_primitive
      (fun a b => (continuous_extend u).intervalIntegrable a b) 0).comp continuous_subtype_val⟩

@[simp] theorem primitive_apply (u : C(Time, E)) (t : Time) :
    primitive u t = ∫ s in 0..(t : ℝ), extend u s := rfl

theorem norm_primitive_le (u : C(Time, E)) : ‖primitive u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (t : ℝ)) (C := ‖u‖)
    (fun s _ => u.norm_coe_le_norm (projIcc 0 1 zero_le_one s))
  change ‖∫ s in 0..(t : ℝ), extend u s‖ ≤ ‖u‖
  refine h.trans ?_
  rw [sub_zero, abs_of_nonneg t.2.1]
  exact mul_le_of_le_one_right (norm_nonneg _) t.2.2

def primitiveCLM : C(Time, E) →L[ℝ] C(Time, E) := by
  let L : C(Time, E) →ₗ[ℝ] C(Time, E) :=
    { toFun := primitive
      map_add' := by
        intro u v
        ext t
        change (∫ s in 0..(t : ℝ), extend u s + extend v s) = _
        exact intervalIntegral.integral_add
          ((continuous_extend u).intervalIntegrable _ _)
          ((continuous_extend v).intervalIntegrable _ _)
      map_smul' := by
        intro c u
        ext t
        exact intervalIntegral.integral_smul c (extend u) }
  exact L.mkContinuous 1 (by
    intro u
    change ‖primitive u‖ ≤ 1 * ‖u‖
    simpa using norm_primitive_le u)

@[simp] theorem primitiveCLM_apply (u : C(Time, E)) : primitiveCLM u = primitive u := rfl

theorem primitiveCLM_norm_le : ‖primitiveCLM (E := E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using norm_primitive_le u

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u4} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

noncomputable section

def picard {V : E → E} (hV : Continuous V) (h : ℝ) (x : E)
    (u : C(Time, E)) : C(Time, E) :=
  ContinuousMap.const Time x + h • primitive (SmoothPaths.superpose hV u)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem lipschitz_superpose {V : E → E} {K : ℝ≥0}
    (hV : LipschitzWith K V) :
    LipschitzWith K (SmoothPaths.superpose (X := Time) hV.continuous) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  apply (ContinuousMap.dist_le (mul_nonneg K.coe_nonneg dist_nonneg)).mpr
  intro t
  exact (hV.dist_le_mul (u t) (v t)).trans
    (mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist (f := u) (g := v) t) K.coe_nonneg)

omit [CompleteSpace E] in
theorem lipschitz_picard {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (x : E) : LipschitzWith (‖h‖₊ * K) (picard hV.continuous h x) := by
  have hp : LipschitzWith 1 (primitive (E := E)) := by
    change LipschitzWith 1 (primitiveCLM (E := E))
    exact ContinuousLinearMap.opNorm_le_iff_lipschitz.mp primitiveCLM_norm_le
  have hi := (lipschitzWith_smul h).comp (hp.comp (lipschitz_superpose hV))
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simpa [picard] using hi.dist_le_mul u v

omit [CompleteSpace E] in

theorem contDiff_picard [ProperSpace E] {V : E → E} (hV : ContDiff ℝ ∞ V) (h : ℝ) :
    ContDiff ℝ ∞ (fun p : E × C(Time, E) => picard hV.continuous h p.1 p.2) := by
  have hc : ContDiff ℝ ∞ (fun p : E × C(Time, E) => ContinuousMap.const Time p.1) :=
    (ContinuousLinearMap.const ℝ Time : E →L[ℝ] C(Time, E)).contDiff.comp contDiff_fst
  have hp : ContDiff ℝ ∞ (fun p : E × C(Time, E) =>
      primitive (SmoothPaths.superpose hV.continuous p.2)) :=
    primitiveCLM.contDiff.comp ((SmoothPaths.contDiff_superpose hV).comp contDiff_snd)
  exact hc.add (hp.const_smul h)

def trajectory {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : C(Time, E) :=
  SmoothContraction.fixedPoint (f := fun p : E × C(Time, E) => picard hV.continuous h p.1 p.2) hh (lipschitz_picard hV h) x

theorem trajectory_eq {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) :
    picard hV.continuous h x (trajectory hV h hh x) = trajectory hV h hh x :=
  SmoothContraction.fixedPoint_eq (f := fun p : E × C(Time, E) => picard hV.continuous h p.1 p.2) hh (lipschitz_picard hV h) x

theorem contDiff_trajectory [ProperSpace E] {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) :
    ContDiff ℝ ∞ (trajectory hV h hh) :=
  SmoothContraction.contDiff_fixedPoint (f := fun p : E × C(Time, E) => picard hV.continuous h p.1 p.2) (contDiff_picard hVs h) hh (lipschitz_picard hV h)

def curve {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (t : ℝ) : E :=
  x + h • ∫ s in 0..t, V (extend (trajectory hV h hh x) s)

@[simp] theorem curve_coe {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (t : Time) :
    curve hV h hh x t = trajectory hV h hh x t :=
  congrArg (fun u : C(Time, E) => u t) (trajectory_eq hV h hh x)

@[simp] theorem curve_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : curve hV h hh x 0 = x := by
  simp [curve]

theorem continuous_curve {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : Continuous (curve hV h hh x) := by
  have hc := hV.continuous.comp (continuous_extend (trajectory hV h hh x))
  exact continuous_const.add
    ((intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0).const_smul h)

theorem hasDerivAt_curve {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (t : Time) :
    HasDerivAt (curve hV h hh x) (h • V (curve hV h hh x t)) (t : ℝ) := by
  have hc := hV.continuous.comp (continuous_extend (trajectory hV h hh x))
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) (hc.stronglyMeasurableAtFilter volume (𝓝 (t : ℝ)))
      hc.continuousAt
  rw [curve_coe]
  change HasDerivAt (fun s : ℝ =>
    x + h • ∫ r in 0..s, V (extend (trajectory hV h hh x) r)) _ (t : ℝ)
  simpa only [Pi.smul_apply, Function.comp_apply, extend_coe] using
    (hd.const_smul h).const_add x

def step {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : E :=
  trajectory hV h hh x ⟨1, by constructor <;> norm_num⟩

theorem contDiff_step [ProperSpace E] {V : E → E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) : ContDiff ℝ ∞ (step hV h hh) :=
  (ContinuousMap.evalCLM ℝ (M := E) (⟨1, by constructor <;> norm_num⟩ : Time)).contDiff.comp
    (contDiff_trajectory hV hVs h hh)

@[simp] theorem curve_one {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : curve hV h hh x 1 = step hV h hh x :=
  curve_coe hV h hh x ⟨1, by constructor <;> norm_num⟩

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u5} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

noncomputable section

theorem curve_unique {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) {f : ℝ → E}
    (hf : ContinuousOn f (Icc 0 1))
    (hf' : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt f (h • V (f t)) (Ici t) t)
    (h0 : f 0 = x) : EqOn f (curve hV h hh x) (Icc 0 1) := by
  apply ODE_solution_unique_of_mem_Icc_right
    (v := fun _ y => h • V y) (s := fun _ => univ)
    (K := ‖h‖₊ * K)
  · intro _ _
    exact ((lipschitzWith_smul h).comp hV).lipschitzOnWith
  · exact hf
  · exact hf'
  · intro _ _; trivial
  · exact (continuous_curve hV h hh x).continuousOn
  · intro t ht
    exact (hasDerivAt_curve hV h hh x ⟨t, ht.1, ht.2.le⟩).hasDerivWithinAt
  · intro _ _; trivial
  · simpa using h0

theorem curve_reverse {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) :
    EqOn (fun t => curve hV h hh x (1 - t))
      (curve hV (-h) (by simpa using hh) (step hV h hh x)) (Icc 0 1) := by
  apply curve_unique hV (-h) (by simpa using hh) (step hV h hh x)
  · exact ((continuous_curve hV h hh x).comp (continuous_const.sub continuous_id)).continuousOn
  · intro t ht
    have hr : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hd := (hasDerivAt_curve hV h hh x ⟨1 - t, hr⟩).scomp t
      ((hasDerivAt_id t).const_sub 1)
    have he : HasDerivAt (fun t => curve hV h hh x (1 - t))
        ((-h) • V (curve hV h hh x (1 - t))) t := by
      simpa only [Function.comp_def, id_eq, neg_smul, one_smul] using hd
    exact he.hasDerivWithinAt
  · simp

theorem step_neg_step {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) :
    step hV (-h) (by simpa using hh) (step hV h hh x) = x := by
  have he := curve_reverse hV h hh x (show 1 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa using he.symm

def stepHomeomorph [ProperSpace E] {V : E → E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) : E ≃ₜ E where
  toFun := step hV h hh
  invFun := step hV (-h) (by simpa using hh)
  left_inv := step_neg_step hV h hh
  right_inv x := by
    simpa only [neg_neg] using step_neg_step hV (-h) (by simpa using hh) x
  continuous_toFun := (contDiff_step hV hVs h hh).continuous
  continuous_invFun := (contDiff_step hV hVs (-h) (by simpa using hh)).continuous

@[simp] theorem stepHomeomorph_apply [ProperSpace E] {V : E → E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) :
    stepHomeomorph hV hVs h hh x = step hV h hh x := rfl

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u6} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

def tangentPath {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) : C(Time, E) :=
  fderiv ℝ (trajectory hV h hh) x v

end
end SmoothODE

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.CompleteFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u7 u8 u9 u10 u11 u12 u13

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u7} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

def variation {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) (t : ℝ) : E :=
  v + h • ∫ s in 0..t,
    fderiv ℝ V (extend (trajectory hV h hh x) s) (extend (tangentPath hV h hh x v) s)

omit [ProperSpace E] in
@[simp] theorem variation_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) : variation hV h hh x v 0 = v := by
  simp [variation]

end
end SmoothODE

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.TensorCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u17 u18 u19 u20 u21 u22

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

open Set Filter Function
open scoped Topology ContDiff

namespace TensorCalculus

variable {E : Type u17} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance oneTensorGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance oneTensorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance twoTensorGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance twoTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

abbrev TwoTensor (E : Type u18) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ

def alt : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ) -
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap

@[simp] theorem alt_apply (B : TwoTensor E) (a b : E) :
    alt B a b = B a b - B b a := rfl

def exteriorD (γ : E → E →L[ℝ] ℝ) (x : E) : TwoTensor E :=
  alt (fderiv ℝ γ x)

@[simp] theorem exteriorD_apply (γ : E → E →L[ℝ] ℝ) (x a b : E) :
    exteriorD γ x a b = fderiv ℝ γ x a b - fderiv ℝ γ x b a := rfl

end
end TensorCalculus

namespace TensorCalculus

open Set Filter Function
open scoped Topology ContDiff

variable {E : Type u20} {F : Type u21} {D : Type u22} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

noncomputable section

def pullLinear (L : F →L[ℝ] E) (B : TwoTensor E) : TwoTensor F :=
  B.bilinearComp L L

@[simp] theorem pullLinear_apply (L : F →L[ℝ] E) (B : TwoTensor E) (a b : F) :
    pullLinear L B a b = B (L a) (L b) := rfl

end
end TensorCalculus

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.MoserField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u23 u24

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff

open Set Filter Function
open scoped Topology ContDiff NNReal

namespace Moser

variable {E : Type u23} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable section

def spatialField (A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ)
    (γ : E → E →L[ℝ] ℝ) (ρ : ℝ → ℝ) (z : ℝ × E) : E :=
  -(ρ z.1) • (A z).inverse (γ z.2)

end
end Moser

namespace Moser

open Set Filter Function TensorCalculus
open scoped Topology ContDiff

variable {E : Type u24} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance oneTensorGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance oneTensorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance twoTensorGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance twoTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def extendedOneForm (γ : E → E →L[ℝ] ℝ) (β : ℝ → ℝ) (z : ℝ × E) :
    (ℝ × E) →L[ℝ] ℝ :=
  β z.1 • (γ z.2).comp (ContinuousLinearMap.snd ℝ ℝ E)

@[simp] theorem extendedOneForm_apply (γ : E → E →L[ℝ] ℝ) (β : ℝ → ℝ)
    (z a : ℝ × E) : extendedOneForm γ β z a = β z.1 * γ z.2 a.2 := rfl

def spatialTensor (W : E → TwoTensor E) (γ : E → E →L[ℝ] ℝ)
    (β : ℝ → ℝ) (z : ℝ × E) : TwoTensor E :=
  W z.2 + β z.1 • exteriorD γ z.2

def spaceTimeTensor (W : E → TwoTensor E) (γ : E → E →L[ℝ] ℝ)
    (β : ℝ → ℝ) (z : ℝ × E) : TwoTensor (ℝ × E) :=
  pullLinear (ContinuousLinearMap.snd ℝ ℝ E) (W z.2) +
    exteriorD (extendedOneForm γ β) z

end
end Moser

open Set Filter
open scoped Topology ContDiff

namespace Moser

noncomputable section

def timeCutoff : ℝ → ℝ := Real.smoothTransition

@[simp] theorem timeCutoff_zero : timeCutoff 0 = 0 := Real.smoothTransition.zero

@[simp] theorem timeCutoff_one : timeCutoff 1 = 1 := Real.smoothTransition.one

end
end Moser

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.MoserFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u25 u26

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff

open Set Filter Function
open scoped Topology ContDiff

namespace SmoothODE

variable {E : Type u25} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

def fiberHomeomorph (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ) : E ≃ₜ E where
  toFun x := (f (t, x)).2
  invFun y := (f.symm (t + T, y)).2
  left_inv x := by
    have he : (t + T, (f (t, x)).2) = f (t, x) := by
      ext
      · exact (hTime (t, x)).symm
      · rfl
    change (f.symm (t + T, (f (t, x)).2)).2 = x
    rw [he, f.symm_apply_apply]
  right_inv y := by
    have he : (f.symm (t + T, y)).1 = t := by
      have h := hTime (f.symm (t + T, y))
      rw [f.apply_symm_apply] at h
      dsimp at h
      linarith
    have he' : (t, (f.symm (t + T, y)).2) = f.symm (t + T, y) := by
      ext
      · exact he.symm
      · rfl
    change (f (t, (f.symm (t + T, y)).2)).2 = y
    rw [he', f.apply_symm_apply]
  continuous_toFun := continuous_snd.comp (f.continuous.comp (continuous_const.prodMk continuous_id))
  continuous_invFun := continuous_snd.comp
    (f.symm.continuous.comp (continuous_const.prodMk continuous_id))

omit [NormedSpace ℝ E] in
@[simp] theorem fiberHomeomorph_apply (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ) (x : E) :
    fiberHomeomorph f T hTime t x = (f (t, x)).2 := rfl

omit [NormedSpace ℝ E] in
@[simp] theorem fiberHomeomorph_symm_apply (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ) (x : E) :
    (fiberHomeomorph f T hTime t).symm x = (f.symm (t + T, x)).2 := rfl

end
end SmoothODE

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PotentialForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u27 u28 u29

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff

namespace ComplexPotential

open TensorCalculus Set Filter
open scoped Topology ContDiff

variable {E : Type u27} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance oneTensorGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance oneTensorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance twoTensorGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance twoTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def dcOp (J : E →L[ℝ] E) : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
  (-1 / 4 : ℝ) • (ContinuousLinearMap.compL ℝ E E ℝ).flip J

def dc (J : E →L[ℝ] E) (φ : E → ℝ) (x : E) : E →L[ℝ] ℝ :=
  dcOp J (fderiv ℝ φ x)

def ddc (J : E →L[ℝ] E) (φ : E → ℝ) : E → TwoTensor E := exteriorD (dc J φ)

@[simp] theorem dcOp_apply (J : E →L[ℝ] E) (L : E →L[ℝ] ℝ) (a : E) :
    dcOp J L a = -(L (J a)) / 4 := by
  simp only [dcOp, smul_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

@[simp] theorem dc_apply (J : E →L[ℝ] E) (φ : E → ℝ) (x a : E) :
    dc J φ x a = -(fderiv ℝ φ x (J a)) / 4 := dcOp_apply J _ a

theorem contDiffAt_dc (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) : ContDiffAt ℝ ∞ (dc J φ) x := by
  change ContDiffAt ℝ ∞ (dcOp J ∘ fderiv ℝ φ) x
  exact (dcOp J).contDiff.contDiffAt.comp x (hφ.fderiv_right (m := ∞) (by simp))

def IsPSHAt (J : E →L[ℝ] E) (φ : E → ℝ) (x : E) : Prop :=
  ContDiffAt ℝ ∞ φ x ∧ ∀ a, 0 ≤ ddc J φ x a (J a)

theorem dc_add (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    dc J (fun y => φ y + ψ y) x = dc J φ x + dc J ψ x := by
  simp only [dc, fderiv_fun_add hφ hψ, map_add]

theorem ddc_add (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (hψ : ContDiffAt ℝ ∞ ψ x) :
    ddc J (fun y => φ y + ψ y) x = ddc J φ x + ddc J ψ x := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : dc J (fun y => φ y + ψ y) =ᶠ[𝓝 x] fun y => dc J φ y + dc J ψ y := by
    filter_upwards [(hφ.of_le h1).eventually (by simp),
      (hψ.of_le h1).eventually (by simp)] with y hy hz
    exact dc_add J (hy.differentiableAt (by simp)) (hz.differentiableAt (by simp))
  unfold ddc exteriorD
  rw [he.fderiv_eq, fderiv_fun_add
    ((contDiffAt_dc J hφ).differentiableAt (by simp))
    ((contDiffAt_dc J hψ).differentiableAt (by simp)), map_add]

end
end ComplexPotential

namespace ComplexPotential

open TensorCalculus
open scoped ContDiff Topology

variable {E : Type u28} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

def standardTensor (J : E →L[ℝ] E) : TwoTensor E := (innerSL ℝ).comp J

@[simp] theorem standardTensor_apply (J : E →L[ℝ] E) (a b : E) :
    standardTensor J a b = inner (𝕜 := ℝ) (J a) b := rfl

end
end ComplexPotential

namespace ComplexPotential

open TensorCalculus Set Filter
open scoped ContDiff Topology

variable {E : Type u29} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance linearOneGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance linearOneSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance linearTwoGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

local instance linearTwoSpace_rf9e987_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
@[simp] theorem dc_const (J : E →L[ℝ] E) (c : ℝ) (x : E) :
    dc J (fun _ => c) x = 0 := by
  simp [dc]

@[simp] theorem ddc_const (J : E →L[ℝ] E) (c : ℝ) (x : E) :
    ddc J (fun _ => c) x = 0 := by
  simp [ddc, exteriorD, show dc J (fun _ : E => c) = fun _ => 0 by funext y; simp]

theorem dc_const_smul (J : E →L[ℝ] E) (c : ℝ) {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) :
    dc J (fun y => c * φ y) x = c • dc J φ x := by
  ext a
  rw [dc_apply, fderiv_const_mul hφ]
  simp only [smul_apply, smul_eq_mul, dc_apply]
  ring

theorem ddc_const_smul (J : E →L[ℝ] E) (c : ℝ) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) :
    ddc J (fun y => c * φ y) x = c • ddc J φ x := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : dc J (fun y => c * φ y) =ᶠ[𝓝 x] fun y => c • dc J φ y := by
    filter_upwards [(hφ.of_le h1).eventually (by simp)] with y hy
    exact dc_const_smul J c (hy.differentiableAt one_ne_zero)
  unfold ddc exteriorD
  rw [he.fderiv_eq]
  have hd : fderiv ℝ (fun y => c • dc J φ y) x = c • fderiv ℝ (dc J φ) x :=
    (((contDiffAt_dc J hφ).differentiableAt (by simp)).hasFDerivAt.const_smul c).fderiv
  rw [hd, map_smul]

theorem IsPSHAt.add {J : E →L[ℝ] E} {φ ψ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) (hψ : IsPSHAt J ψ x) :
    IsPSHAt J (fun y => φ y + ψ y) x := by
  refine ⟨hφ.1.add hψ.1, fun a => ?_⟩
  rw [ddc_add J hφ.1 hψ.1, add_apply, add_apply]
  exact add_nonneg (hφ.2 a) (hψ.2 a)

theorem IsPSHAt.const_smul {J : E →L[ℝ] E} {φ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) {c : ℝ} (hc : 0 ≤ c) :
    IsPSHAt J (fun y => c * φ y) x := by
  refine ⟨contDiffAt_const.mul hφ.1, fun a => ?_⟩
  rw [ddc_const_smul J c hφ.1]
  simpa only [smul_apply, smul_eq_mul] using mul_nonneg hc (hφ.2 a)

end
end ComplexPotential

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PotentialDeformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u30 u31 u32 u33 u34 u35

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff

open Set Filter Function
open scoped ContDiff Topology

namespace CompactExtension
noncomputable section

variable {E : Type u30} {F : Type u31} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def extend (U : Set E) (f : E → F) : E → F := by
  classical
  exact U.indicator f

end
end CompactExtension

namespace ComplexPotential

open TensorCalculus Set Filter Function
open scoped ContDiff Topology

noncomputable section

variable {E : Type u32} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance moserOneGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance moserOneSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance moserTwoGroup : NormedAddCommGroup (TwoTensor E) := inferInstance
local instance moserTwoSpace : NormedSpace ℝ (TwoTensor E) := inferInstance

end
end ComplexPotential

namespace ComplexPotential

open Set Filter
open scoped ContDiff Topology

noncomputable section

@[simp] theorem deriv_log_add (δ t : ℝ) :
    deriv (fun s => Real.log (s + δ)) t = (t + δ)⁻¹ := by
  rw [deriv_comp_add_const, Real.deriv_log]

variable {E : Type u35} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def logNormSq (δ : ℝ) (x : E) : ℝ := Real.log (‖x‖^2 + δ)

end
end ComplexPotential

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.RegularizedMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u36 u37

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace SmoothPositivePart

noncomputable section

def primitive (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, Real.smoothTransition s

def shift : ℝ := primitive 1 - 1

def positivePart (t : ℝ) : ℝ := primitive (t - shift)

def smoothMax (h p : ℝ) : ℝ := p + positivePart (h - p)

end
end SmoothPositivePart

namespace ComplexPotential

open SmoothPositivePart Set Filter
open scoped ContDiff Topology

variable {E : Type u37} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

omit [NormedSpace ℝ E] in

def gluedPotential (R : ℝ) (H P : E → ℝ) (x : E) : ℝ := by
  classical
  exact if ‖x‖ < R then if x = 0 then P x else smoothMax (H x) (P x) else H x

end
end ComplexPotential

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.RadialMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u38 u39 u40

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace RadialSymplectic

open Set Filter Function TensorCalculus
open scoped Topology ContDiff

variable {E : Type u38} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance oneTensorGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance oneTensorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

local instance twoTensorGroup_rf9e987_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance twoTensorSpace_rf9e987_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
def radialMap (α : E → ℝ) (x : E) : E := α x • x

def radialPrimitive (B : TwoTensor E) (α : E → ℝ) (x : E) : E →L[ℝ] ℝ :=
  (α x ^ 2 / 2) • B x

end
end RadialSymplectic

open Set
open scoped Topology ContDiff

namespace RadialSymplectic

noncomputable section

def radiusSq (μ δ s : ℝ) : ℝ := s + μ * (s / (s + δ))

def inverseScaleSq (μ δ t : ℝ) : ℝ :=
  2 * δ / (μ + δ - t + Real.sqrt ((μ + δ - t) ^ 2 + 4 * δ * t))

theorem radiusSq_strictMonoOn {μ δ : ℝ} (hμ : 0 ≤ μ) (hδ : 0 < δ) :
    StrictMonoOn (radiusSq μ δ) (Ici 0) := by
  intro s hs t ht hst
  have hsδ : 0 < s + δ := add_pos_of_nonneg_of_pos hs hδ
  have htδ : 0 < t + δ := add_pos_of_nonneg_of_pos ht hδ
  have hf : s / (s + δ) ≤ t / (t + δ) := by
    apply (div_le_div_iff₀ hsδ htδ).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hf hμ
  dsimp only [radiusSq]
  linarith

theorem radial_discriminant_pos {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (t : ℝ) :
    0 < (μ + δ - t) ^ 2 + 4 * δ * t := by
  nlinarith [sq_nonneg (t + δ - μ), mul_pos hμ hδ]

theorem inverseScaleSq_den_pos {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (_ht : 0 ≤ t) : 0 < μ + δ - t + Real.sqrt ((μ + δ - t) ^ 2 + 4 * δ * t) := by
  have hsq := Real.sq_sqrt (radial_discriminant_pos hμ hδ t).le
  have hr := Real.sqrt_nonneg ((μ + δ - t) ^ 2 + 4 * δ * t)
  by_contra hc
  have hc' : Real.sqrt ((μ + δ - t) ^ 2 + 4 * δ * t) ≤ -(μ + δ - t) := by
    linarith
  have htt : 0 < t := by linarith
  have hmul := mul_self_le_mul_self hr hc'
  nlinarith [mul_pos hδ htt]

theorem inverseScaleSq_pos {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    0 < inverseScaleSq μ δ t :=
  div_pos (mul_pos (by norm_num) hδ) (inverseScaleSq_den_pos hμ hδ ht)

theorem inverseScaleSq_quadratic {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (ht : 0 ≤ t) :
    t * (inverseScaleSq μ δ t) ^ 2 + (μ + δ - t) * inverseScaleSq μ δ t - δ = 0 := by
  have hD := (inverseScaleSq_den_pos hμ hδ ht).ne'
  have hsq := Real.sq_sqrt (radial_discriminant_pos hμ hδ t).le
  unfold inverseScaleSq
  generalize Real.sqrt ((μ + δ - t) ^ 2 + 4 * δ * t) = R at hD hsq ⊢
  field_simp [hD]
  nlinarith

theorem inverseScaleSq_factor {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    (1 + μ / (inverseScaleSq μ δ t * t + δ)) * inverseScaleSq μ δ t = 1 := by
  have hq := inverseScaleSq_pos hμ hδ ht
  have hquad := inverseScaleSq_quadratic hμ hδ ht
  have hd : 0 < inverseScaleSq μ δ t * t + δ :=
    add_pos_of_nonneg_of_pos (mul_nonneg hq.le ht) hδ
  field_simp [hd.ne']
  nlinarith

theorem contDiffAt_inverseScaleSq {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    ContDiffAt ℝ ∞ (inverseScaleSq μ δ) t := by
  have hs : ContDiffAt ℝ ∞ (fun y => Real.sqrt ((μ + δ - y) ^ 2 + 4 * δ * y)) t :=
    (Real.contDiffAt_sqrt (radial_discriminant_pos hμ hδ t).ne').comp t
      (((contDiffAt_const.sub contDiffAt_id).pow 2).add (contDiffAt_const.mul contDiffAt_id))
  exact contDiffAt_const.div ((contDiffAt_const.sub contDiffAt_id).add hs)
    (inverseScaleSq_den_pos hμ hδ ht).ne'

end
end RadialSymplectic

namespace RadialSymplectic

open Set
open scoped Topology ContDiff

variable {E : Type u39} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

def expansionScale (μ δ : ℝ) (x : E) : ℝ := Real.sqrt (1 + μ / (‖x‖ ^ 2 + δ))
def radialExpansion (μ δ : ℝ) : E → E := radialMap (expansionScale μ δ)
def contractionScale (μ δ : ℝ) (x : E) : ℝ :=
  Real.sqrt (inverseScaleSq μ δ (‖x‖ ^ 2))
def radialContraction (μ δ : ℝ) : E → E := radialMap (contractionScale μ δ)

omit [InnerProductSpace ℝ E] in
theorem expansionScale_pos {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    0 < expansionScale μ δ x := by
  unfold expansionScale
  apply Real.sqrt_pos.mpr
  have hd : 0 < ‖x‖ ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  positivity

omit [InnerProductSpace ℝ E] in
theorem expansionScale_sq {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    expansionScale μ δ x ^ 2 = 1 + μ / (‖x‖ ^ 2 + δ) := by
  unfold expansionScale
  apply Real.sq_sqrt
  have hd : 0 < ‖x‖ ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  positivity

theorem norm_sq_radialExpansion {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    ‖radialExpansion μ δ x‖ ^ 2 = radiusSq μ δ (‖x‖ ^ 2) := by
  simp only [radialExpansion, radialMap, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [expansionScale_sq hμ hδ]
  unfold radiusSq
  ring

theorem radialExpansion_injective {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    Function.Injective (radialExpansion μ δ : E → E) := by
  intro x y h
  have hh := congrArg (fun z : E => ‖z‖ ^ 2) h
  rw [norm_sq_radialExpansion hμ hδ, norm_sq_radialExpansion hμ hδ] at hh
  have hnorm := (radiusSq_strictMonoOn hμ.le hδ).injOn (sq_nonneg ‖x‖) (sq_nonneg ‖y‖) hh
  have hscale : expansionScale μ δ x = expansionScale μ δ y := by
    unfold expansionScale
    rw [hnorm]
  dsimp only [radialExpansion, radialMap] at h
  rw [hscale] at h
  exact (smul_right_injective E (expansionScale_pos hμ hδ y).ne') h

omit [InnerProductSpace ℝ E] in
theorem contractionScale_pos {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    0 < contractionScale μ δ x :=
  Real.sqrt_pos.mpr (inverseScaleSq_pos hμ hδ (sq_nonneg _))

theorem norm_sq_radialContraction {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    ‖radialContraction μ δ x‖ ^ 2 = inverseScaleSq μ δ (‖x‖ ^ 2) * ‖x‖ ^ 2 := by
  simp only [radialContraction, radialMap, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [contractionScale, Real.sq_sqrt (inverseScaleSq_pos hμ hδ (sq_nonneg _)).le]

theorem expansionScale_mul_contractionScale {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (x : E) : expansionScale μ δ (radialContraction μ δ x) * contractionScale μ δ x = 1 := by
  have hp := expansionScale_pos hμ hδ (radialContraction μ δ x)
  have hq := contractionScale_pos hμ hδ x
  have hsq : (expansionScale μ δ (radialContraction μ δ x) * contractionScale μ δ x)^2 = 1 := by
    rw [mul_pow, expansionScale_sq hμ hδ, contractionScale,
      Real.sq_sqrt (inverseScaleSq_pos hμ hδ (sq_nonneg _)).le,
      norm_sq_radialContraction hμ hδ]
    exact inverseScaleSq_factor hμ hδ (sq_nonneg _)
  nlinarith [mul_pos hp hq]

theorem radialExpansion_radialContraction {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (x : E) : radialExpansion μ δ (radialContraction μ δ x) = x := by
  change expansionScale μ δ (radialContraction μ δ x) • (contractionScale μ δ x • x) = x
  rw [smul_smul, expansionScale_mul_contractionScale hμ hδ, one_smul]

theorem radialContraction_radialExpansion {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (x : E) : radialContraction μ δ (radialExpansion μ δ x) = x :=
  radialExpansion_injective hμ hδ (radialExpansion_radialContraction hμ hδ _)

theorem contDiff_expansionScale {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (expansionScale μ δ : E → ℝ) := by
  have hn : ContDiff ℝ ∞ (fun x : E => ‖x‖^2 + δ) := (contDiff_norm_sq ℝ).add contDiff_const
  have hd (x : E) : ‖x‖ ^ 2 + δ ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ).ne'
  have hp (x : E) : 1 + μ / (‖x‖ ^ 2 + δ) ≠ 0 := by
    have hpp : 0 < ‖x‖ ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
    positivity
  exact (contDiff_const.add (contDiff_const.div hn hd)).sqrt hp

theorem contDiff_contractionScale {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (contractionScale μ δ : E → ℝ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hi : ContDiffAt ℝ ∞ (fun z : E => inverseScaleSq μ δ (‖z‖ ^ 2)) x :=
    (contDiffAt_inverseScaleSq hμ hδ (sq_nonneg ‖x‖)).comp (f := fun z : E => ‖z‖^2) x
      (contDiff_norm_sq ℝ).contDiffAt
  exact (Real.contDiffAt_sqrt (inverseScaleSq_pos hμ hδ (sq_nonneg ‖x‖)).ne').comp
    (f := fun z : E => inverseScaleSq μ δ (‖z‖ ^ 2)) x hi

theorem contDiff_radialExpansion {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (radialExpansion μ δ : E → E) :=
  (contDiff_expansionScale hμ hδ).smul contDiff_id

theorem contDiff_radialContraction {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (radialContraction μ δ : E → E) :=
  (contDiff_contractionScale hμ hδ).smul contDiff_id

def radialHomeomorph {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) : E ≃ₜ E where
  toFun := radialExpansion μ δ
  invFun := radialContraction μ δ
  left_inv := radialContraction_radialExpansion hμ hδ
  right_inv := radialExpansion_radialContraction hμ hδ
  continuous_toFun := (contDiff_radialExpansion hμ hδ).continuous
  continuous_invFun := (contDiff_radialContraction hμ hδ).continuous

end
end RadialSymplectic

namespace RadialSymplectic

open ComplexPotential TensorCalculus
open scoped ContDiff

noncomputable section

variable {E : Type u40} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def modelPotential (μ δ : ℝ) (x : E) : ℝ := ‖x‖^2 + μ * Real.log (‖x‖^2 + δ)

end
end RadialSymplectic

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.HolomorphicBalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u41 u42 u43 u44 u45 u46 u47 u48 u49

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff

open Set

namespace TensorCalculus

open Set Filter
open scoped Topology ContDiff

variable {E : Type u42} {F : Type u43} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable section

local instance pullbackOneTensorGroup : NormedAddCommGroup (F →L[ℝ] ℝ) := inferInstance
local instance pullbackOneTensorSpace : NormedSpace ℝ (F →L[ℝ] ℝ) := inferInstance

local instance pullbackTwoTensorGroup_rf9e987_1 : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
local instance pullbackTwoTensorSpace_rf9e987_1 : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
def pullbackOneForm (f : E → F) (γ : F → F →L[ℝ] ℝ) (x : E) : E →L[ℝ] ℝ :=
  (γ (f x)).comp (fderiv ℝ f x)

@[simp] theorem pullbackOneForm_apply (f : E → F) (γ : F → F →L[ℝ] ℝ) (x a : E) :
    pullbackOneForm f γ x a = γ (f x) (fderiv ℝ f x a) := rfl

end
end TensorCalculus

namespace ComplexPotential

open Set Filter TensorCalculus
open scoped ContDiff Topology

noncomputable section

variable {E : Type u46} {F : Type u47} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def complexStructure (E : Type u48) [NormedAddCommGroup E] [NormedSpace ℂ E] : E →L[ℝ] E :=
  (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ

@[simp] theorem complexStructure_apply (a : E) : complexStructure E a = Complex.I • a := rfl

end
end ComplexPotential

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.LogProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u50 u51

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace SmoothLogProfile
noncomputable section

variable (b l u : ℝ)

def cutoff (t : ℝ) : ℝ := Real.smoothTransition ((t - l) / (u - l))

def slope (t : ℝ) : ℝ := b + cutoff l u t * (Real.exp t - b)

def profile (t : ℝ) : ℝ := Real.exp u + ∫ s in u..t, slope b l u s

end
end SmoothLogProfile

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.LensMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology

open Set Filter Complex
open scoped Topology ContDiff

namespace PlanarLens
noncomputable section

def term (n : ℕ) (w : ℂ) : ℂ := (-1)^n * w^(2*n+1) / (2*n+1)^2

def termDeriv (n : ℕ) (w : ℂ) : ℂ := (-1)^n * w^(2*n) / (2*n+1)

def F (w : ℂ) : ℂ := (8 / (Real.pi^2) : ℝ) * ∑' n : ℕ, term n w

@[simp] theorem term_zero (n : ℕ) : term n 0 = 0 := by simp [term]

@[simp] theorem F_zero : F 0 = 0 := by simp [F]

@[simp] theorem F_neg (w : ℂ) : F (-w) = -F w := by
  have he : (fun n : ℕ => term n (-w)) = fun n : ℕ => -term n w := by
    funext n
    simp only [term]
    rw [(show Odd (2*n+1) by exact ⟨n, by omega⟩).neg_pow]
    ring
  simp only [F, he, tsum_neg, mul_neg]

@[simp] theorem F_conj (w : ℂ) : F ((starRingEnd ℂ) w) = (starRingEnd ℂ) (F w) := by
  have he : (fun n : ℕ => term n ((starRingEnd ℂ) w)) = fun n : ℕ => conjCLE (term n w) := by
    funext n
    simp [term, map_ofNat]
  simp only [F, he, ← conjCLE.map_tsum]
  simp [map_ofNat]

def cayley (w : ℂ) : ℂ := (1 + w*I)/(1-w*I)

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.LensArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

def D : Set ℂ := F '' Metric.ball 0 1

def g : ℂ → ℂ := Function.invFunOn F (Metric.ball 0 1)

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

def T (r : ℝ) : ℝ := (F ((r : ℂ)*I)).im

@[simp] theorem T_zero : T 0 = 0 := by simp [T]

@[simp] theorem T_neg (r : ℝ) : T (-r) = -T r := by simp [T]

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

def A (w : ℂ) : ℝ := (w * deriv F w).re

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.LensEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

namespace PlanarLens
open Set Filter Complex MeasureTheory intervalIntegral
open scoped Topology ContDiff
noncomputable section

def circleTop (r s : ℝ) : ℂ := (r : ℂ) * ((Real.sin s : ℂ)+(Real.cos s : ℂ)*I)

@[simp] theorem circleTop_re (r s : ℝ) : (circleTop r s).re = r * Real.sin s := by
  simp only [circleTop, mul_re, add_re, ofReal_re, ofReal_im, I_im, I_re,
    mul_zero, mul_one, sub_zero, zero_mul, add_zero]

@[simp] theorem circleTop_im (r s : ℝ) : (circleTop r s).im = r * Real.cos s := by
  simp only [circleTop, mul_im, add_re, add_im, ofReal_re, ofReal_im, mul_re, I_im, I_re,
    mul_zero, mul_one, zero_add, zero_mul, add_zero]

@[simp] theorem circleTop_zero (r : ℝ) : circleTop r 0 = (r : ℂ)*I := by
  simp [circleTop]

@[simp] theorem circleTop_pi_half (r : ℝ) : circleTop r (Real.pi/2) = (r : ℂ) := by
  simp [circleTop]

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.HorizontalIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u52 u53 u54

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

namespace SmoothPaths
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section

universe u
variable {E F : Type u} {H : Type u52} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def integralPath : C(SmoothODE.Time, F) →L[ℝ] F :=
  (ContinuousMap.evalCLM ℝ ⟨1, by norm_num⟩).comp SmoothODE.primitiveCLM

@[simp] theorem integralPath_apply (u : C(SmoothODE.Time, F)) :
    integralPath u = ∫ t in (0 : ℝ)..1, SmoothODE.extend u t := rfl

end
end SmoothPaths

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

def density (k : ℕ) (z : ℂ) : ℝ := ‖g z‖^(2*k-2) * ‖deriv g z‖^2

def J (k : ℕ) (v t : ℝ) : ℝ := (k : ℝ)^2 * ∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I)

@[simp] theorem J_zero (k : ℕ) (t : ℝ) : J k 0 t = 0 := by simp [J]

def horizontalPath : ℂ →L[ℝ] C(SmoothODE.Time, ℂ) := by
  let L : ℂ →ₗ[ℝ] C(SmoothODE.Time, ℂ) :=
    { toFun := fun z => ⟨fun a => ((a : ℝ)*z.re : ℝ) + (z.im : ℂ)*I, by fun_prop⟩
      map_add' := by intro z w; ext a; simp; ring
      map_smul' := by intro c z; ext a; simp; ring }
  apply L.mkContinuous 2
  intro z
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro a
  change ‖(((a : ℝ)*z.re : ℝ) : ℂ)+(z.im : ℂ)*I‖ ≤ _
  calc
    _ ≤ ‖(((a : ℝ)*z.re : ℝ) : ℂ)‖ + ‖(z.im : ℂ)*I‖ := norm_add_le _ _
    _ = |(a : ℝ)| * |z.re| + |z.im| := by simp
    _ ≤ |z.re| + |z.im| := by
      rw [abs_of_nonneg a.2.1]
      nlinarith [a.2.2, abs_nonneg z.re]
    _ ≤ 2*‖z‖ := by linarith [abs_re_le_norm z, abs_im_le_norm z]

@[simp] theorem horizontalPath_apply (z : ℂ) (a : SmoothODE.Time) :
    horizontalPath z a = (((a : ℝ)*z.re : ℝ) : ℂ)+(z.im : ℂ)*I := rfl

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

def rho (t h : ℝ) : ℝ := ‖g ((h : ℂ)+(t : ℂ)*I)‖
def rhoD (t h : ℝ) : ℝ := A (g ((h : ℂ)+(t : ℂ)*I)) /
  (rho t h * ‖deriv F (g ((h : ℂ)+(t : ℂ)*I))‖^2)

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.TipEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

open MeasureTheory intervalIntegral Set
open scoped Real

namespace SymmetricPolar
noncomputable section

def endpointKernel (H y : ℝ) : ℝ := Real.sqrt (y / (H - y))

def movingEndpointIntegral (k : ℕ) (a : ℝ) : ℝ :=
  (k : ℝ) * ∫ r in a..1,
    r ^ (2 * k - 1) * Real.sqrt ((1 - r) / (r - a))

end
end SymmetricPolar

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

def tailSlope (a : ℝ) : ℝ := 8/Real.pi^2 * Real.artanh a

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.LensBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

def excess (k : ℕ) (z : ℂ) : ℝ := |J k z.re z.im|/(k : ℝ) - Real.pi/4*‖g z‖^(2*k)

def epsilon (k : ℕ) : ℝ := max 0 (sSup (excess k '' D))

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.StripMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u55 u56 u57 u58 u59 u60

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PolarStrips
open Set Filter Asymptotics
open scoped Topology ContDiff
noncomputable section

variable {E : Type u55} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {ι : Type u56} [Fintype ι]

def domain (ℓ : ι → E →L[ℂ] ℂ) : Set E := {z | ∀ j, ℓ j z ∈ PlanarLens.D}

def tuple (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) (z : E) : EuclideanSpace ℂ ι :=
  (EuclideanSpace.equiv ι ℂ).symm (fun j => PlanarLens.g (ℓ j z)^k)

omit [Fintype ι] in
@[simp] theorem tuple_apply (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) (z : E) (j : ι) :
    tuple ℓ k z j = PlanarLens.g (ℓ j z)^k := rfl

end
end PolarStrips

namespace ComplexCoordinates
open scoped ComplexConjugate ContDiff
noncomputable section
variable {ι : Type u57} [Fintype ι]
abbrev R (ι : Type u58) := EuclideanSpace ℝ ι
abbrev C (ι : Type u59) := EuclideanSpace ℂ ι

def re : C ι →L[ℝ] R ι :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => (EuclideanSpace.equiv ι ℝ).symm (fun i => (z i).re)
    map_add' := by intro x y; ext i; simp
    map_smul' := by intro a x; ext i; simp }

def im : C ι →L[ℝ] R ι :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => (EuclideanSpace.equiv ι ℝ).symm (fun i => (z i).im)
    map_add' := by intro x y; ext i; simp
    map_smul' := by intro a x; ext i; simp }

@[simp] theorem re_apply (z : C ι) (i : ι) : re z i = (z i).re := rfl
@[simp] theorem im_apply (z : C ι) (i : ι) : im z i = (z i).im := rfl

def parts : C ι ≃L[ℝ] R ι × R ι :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun z => (re z, im z)
    invFun := fun p => (EuclideanSpace.equiv ι ℂ).symm (fun i => (p.1 i : ℂ)+(p.2 i : ℂ)*Complex.I)
    left_inv := by intro z; ext i; simp [Complex.re_add_im]
    right_inv := by intro p; ext i <;> simp
    map_add' := by intros; simp
    map_smul' := by intros; simp }

@[simp] theorem parts_apply (z : C ι) : parts z = (re z, im z) := rfl
@[simp] theorem parts_symm_apply (x y : R ι) (i : ι) :
    parts.symm (x,y) i = (x i : ℂ)+(y i : ℂ)*Complex.I := rfl

def functional (b : R ι) : C ι →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => ∑ i, (b i : ℂ)*z i
    map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
    map_smul' := by intro a x; simp [mul_left_comm, Finset.mul_sum] }

@[simp] theorem functional_apply (b : R ι) (z : C ι) : functional b z = ∑ i, (b i : ℂ)*z i := rfl

@[simp] theorem re_I_smul (z : C ι) : re (Complex.I • z) = -im z := by
  ext i; simp [Complex.mul_re]
@[simp] theorem im_I_smul (z : C ι) : im (Complex.I • z) = re z := by
  ext i; simp [Complex.mul_im]

end
end ComplexCoordinates

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

def primitive (k : ℕ) (z : ℂ) : ℝ := J k z.re z.im

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.StripEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u61 u62 u63 u64 u65 u66 u67 u68 u69

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PolarStrips
open Set ComplexCoordinates
open scoped ContDiff
noncomputable section
variable {ι : Type u61} {κ : Type u62} [Fintype ι] [Fintype κ]

def phase (b : κ → R ι) (k : ℕ) (z : C ι) : R ι × R ι :=
  (im z, -re z - ∑ j, PlanarLens.primitive k (functional (b j) z) • b j)

end
end PolarStrips

namespace ComplexPotential
open ComplexCoordinates Set Filter
open scoped Topology ContDiff
noncomputable section

variable {E : Type u63} {F : Type u64} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {ι : Type u65} [Fintype ι]

def phaseForm (v w : R ι × R ι) : ℝ :=
  inner (𝕜 := ℝ) v.1 w.2-inner (𝕜 := ℝ) w.1 v.2

end
end ComplexPotential

namespace ConvexPolar
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type u68} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def polar (K : Set E) : Set E := {p | ∀ q ∈ K, inner (𝕜 := ℝ) q p ≤ 1}

variable {κ : Type u69}

def stripBody (b : κ → E) : Set E := {x | ∀ j, |inner (𝕜 := ℝ) (b j) x| ≤ 1}

end
end ConvexPolar

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.MomentumBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u70 u71 u72 u73

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

open Set
open scoped ContDiff ENNReal

namespace LocalEmbedding
open Set Filter
open scoped Topology ContDiff
noncomputable section
variable {E : Type u72} {F : Type u73} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem open_image {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  have hs := hf.contDiffAt (hU.mem_nhds hx)
  obtain ⟨e, heq⟩ := hD x hx
  have he : HasFDerivAt f e.toContinuousLinearMap x := by
    rw [heq]
    exact (hs.differentiableAt (by simp)).hasFDerivAt
  rw [← (hs.hasStrictFDerivAt' he (by simp)).map_nhds_eq_of_equiv]
  change f ⁻¹' (f '' U) ∈ 𝓝 x
  exact mem_of_superset (hU.mem_nhds hx) (fun y hy => mem_image_of_mem f hy)

theorem isOpenEmbedding {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hi : InjOn f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) :
    Topology.IsOpenEmbedding (fun x : U => f x) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hf.continuousOn.domRestrict
  · intro x y h; exact Subtype.ext (hi x.2 y.2 h)
  · intro V hV
    have hUV : Subtype.val '' V ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.2
    have huV : IsOpen (Subtype.val '' V) := hU.isOpenMap_subtype_val _ hV
    have ho := open_image huV (hf.mono hUV) (fun x hx => hD x (hUV hx))
    change IsOpen ((fun x : U => f x) '' V)
    rw [image_image] at ho
    exact ho

end
end LocalEmbedding

namespace SymmetricPolar
open Set Filter
open scoped ContDiff Topology
noncomputable section
variable {n : ℕ}

def diagScale (a b : ℝ) : Phase n →L[ℝ] Phase n :=
  (a • ContinuousLinearMap.fst ℝ (Position n) (Position n)).prod
    (b • ContinuousLinearMap.snd ℝ (Position n) (Position n))

@[simp] theorem diagScale_apply (a b : ℝ) (z : Phase n) : diagScale a b z = (a • z.1, b • z.2) := rfl

end
end SymmetricPolar

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FiniteDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u80 u81 u82 u83

section NonsqueezingInline
section
open Set Filter Function MeasureTheory
open scoped Topology ContDiff

namespace SmoothLinking
noncomputable section
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type u80} {F : Type u81} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def degreeMap (η : E × F → E × F) (e : F) (ρ : ℝ) (z : E × ℝ) : E × ℝ :=
  if 0 < z.2+ρ then
    ((η (z.1, (z.2+ρ) • e)).1, (‖(η (z.1, (z.2+ρ) • e)).2‖^2-ρ^2)/(z.2+2*ρ))
  else z

end
end SmoothLinking

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

end
end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.GradientLinking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u84 u85 u86 u87 u88

section NonsqueezingInline
section
open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace GradientDescent
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff
variable {E : Type u84} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

 def field (Φ σ : E → ℝ) (ε : ℝ) (x : E) : E :=
   (-(2*σ x/(‖gradient Φ x‖^2+ε^2))) • gradient Φ x

end
end GradientDescent

namespace GradientDescent
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {E : Type u85} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

 def energyCutoff (Φ : E → ℝ) (a : ℝ) (x : E) : ℝ :=
   Real.smoothTransition ((2*Φ x-a)/a)

end
end GradientDescent

end

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FourierIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u89 u90 u91 u92 u93 u94 u95 u96 u97 u98 u99

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate

local instance instFactLtRealOfNat_solutions : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
abbrev Time := AddCircle (1 : ℝ)
abbrev μ : Measure Time := AddCircle.haarAddCircle

def eval {ι : Type u89} [Fintype ι] (k : ι → ℤ) (a : ι → ℂ) (t : Time) : ℂ :=
  ∑ i, a i * fourier (k i) t

 theorem integrable_continuous {G : Type u91} [NormedAddCommGroup G]
    {f : Time → G} (hf : Continuous f) : Integrable f μ := by
  simpa only [integrableOn_univ] using hf.continuousOn.integrableOn_compact isCompact_univ

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FourierPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u100 u101 u102 u103 u104 u105 u106 u107 u108 u109 u110 u111

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff

local instance instFactLtRealOfNat_solutions_2_rf9e987_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι : Type u101} {κ : Type u102} [Fintype ι] [Fintype κ]

abbrev Vector (κ : Type u103) := EuclideanSpace ℂ κ
abbrev Coeff (ι : Type u104) (κ : Type u105) := EuclideanSpace ℂ (ι × κ)

def mode (a : Coeff ι κ) (i : ι) : Vector κ :=
  (EuclideanSpace.equiv κ ℂ).symm (fun j => a (i,j))

omit [Fintype ι] [Fintype κ] in
@[simp] theorem mode_apply (a : Coeff ι κ) (i : ι) (j : κ) : mode a i j = a (i,j) := rfl

def loop (k : ι → ℤ) (a : Coeff ι κ) : C(Time, Vector κ) where
  toFun t := ∑ i, fourier (k i) t • mode a i
  continuous_toFun := continuous_finsetSum _ (fun i _ =>
    (fourier (k i)).continuous.smul continuous_const)

@[simp] theorem loop_apply (k : ι → ℤ) (a : Coeff ι κ) (t : Time) :
    loop k a t = ∑ i, fourier (k i) t • mode a i := rfl

 theorem loop_coord (k : ι → ℤ) (a : Coeff ι κ) (t : Time) (j : κ) :
    loop k a t j = eval k (fun i => a (i,j)) t := by
  simp [loop_apply, eval, mul_comm]

 def loopCLM (k : ι → ℤ) : Coeff ι κ →L[ℝ] C(Time, Vector κ) :=
  LinearMap.toContinuousLinearMap {
    toFun := loop k
    map_add' := by
      intro a b
      ext t j
      simp only [ContinuousMap.add_apply, PiLp.add_apply, loop_coord, eval,
        add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro r a
      ext t j
      simp only [ContinuousMap.smul_apply, PiLp.smul_apply, loop_coord, eval,
        RingHom.id_apply, RCLike.real_smul_eq_coe_mul, mul_assoc, ← Finset.mul_sum] }

@[simp] theorem loopCLM_apply (k : ι → ℤ) (a : Coeff ι κ) : loopCLM k a = loop k a := rfl

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_4 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι : Type u108} {κ : Type u109} [Fintype ι] [Fintype κ]

 def project (k : ι → ℤ) (f : C(Time, Vector κ)) : Coeff ι κ :=
  (EuclideanSpace.equiv (ι × κ) ℂ).symm (fun p => fourierCoeff (fun t => f t p.2) (k p.1))

omit [Fintype ι] [Fintype κ] in
@[simp] theorem project_apply (k : ι → ℤ) (f : C(Time, Vector κ)) (p : ι × κ) :
    project k f p = fourierCoeff (fun t => f t p.2) (k p.1) := rfl

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_6 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]

 def average : C(Time, ℝ) →L[ℝ] ℝ := by
  let L : C(Time, ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun f => ∫ t : Time, f t ∂μ
    map_add' := fun f g => integral_add (integrable_continuous f.continuous)
      (integrable_continuous g.continuous)
    map_smul' := fun r f => by simp only [ContinuousMap.smul_apply,
      integral_smul, RingHom.id_apply] }
  apply L.mkContinuous 1
  intro f
  change ‖∫ t : Time, f t ∂μ‖ ≤ 1*‖f‖
  simpa using norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall (fun t => f.norm_coe_le_norm t))

@[simp] theorem average_apply (f : C(Time, ℝ)) : average f = ∫ t : Time, f t ∂μ := rfl

 def potential (k : ι → ℤ) (H : Vector κ → ℝ) (a : Coeff ι κ) : ℝ :=
  ∫ t : Time, H (loop k a t) ∂μ

 theorem contDiff_gradient_function {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (gradient H) :=
  (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.contDiff.comp
    (hH.fderiv_right (by simp))

 def gradLoop (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ) :
    C(Time, Vector κ) :=
  ⟨fun t => gradient H (loop k a t), (contDiff_gradient_function hH).continuous.comp
    (loop k a).continuous⟩

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.QuadraticAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u112

section NonsqueezingInline

namespace DiagonalQuadratic
noncomputable section
open Finset
open scoped ComplexConjugate ContDiff
variable {α : Type u112} [Fintype α]

 def diag (w : α → ℝ) (a : EuclideanSpace ℂ α) : EuclideanSpace ℂ α :=
  (EuclideanSpace.equiv α ℂ).symm (fun p => w p • a p)

omit [Fintype α] in
@[simp] theorem diag_apply (w : α → ℝ) (a : EuclideanSpace ℂ α) (p : α) :
    diag w a p = w p • a p := rfl

 def diagCLM (w : α → ℝ) : EuclideanSpace ℂ α →L[ℝ] EuclideanSpace ℂ α :=
  LinearMap.toContinuousLinearMap {
    toFun := diag w
    map_add' := by intros; ext; simp [smul_add]
    map_smul' := by intros; ext; simp; ring }

@[simp] theorem diagCLM_apply (w : α → ℝ) (a : EuclideanSpace ℂ α) : diagCLM w a = diag w a := rfl

 def energy (w : α → ℝ) (a : EuclideanSpace ℂ α) : ℝ := ∑ p, w p * ‖a p‖^2

end
end DiagonalQuadratic

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_7_rf9e987_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

 def action (k : ι → ℤ) (H : Vector κ → ℝ) (a : Coeff ι κ) : ℝ :=
   energy (fun p => Real.pi*(k p.1 : ℝ)) a - potential k H a

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_9_rf9e987_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

 def remainderLoop (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (d : κ → ℝ) (a : Coeff ι κ) : C(Time, Vector κ) :=
  gradLoop k hH a - loop k ((2 : ℝ) • diag (fun p => d p.2) a)

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.GalerkinBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u113

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_10_rf9e987_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

 def leftCoeff (a : Coeff (ι ⊕ ν) κ) : Coeff ι κ :=
  (EuclideanSpace.equiv (ι × κ) ℂ).symm (fun p => a (Sum.inl p.1,p.2))

 def rightCoeff (a : Coeff (ι ⊕ ν) κ) : Coeff ν κ :=
  (EuclideanSpace.equiv (ν × κ) ℂ).symm (fun p => a (Sum.inr p.1,p.2))

 def joinCoeff (a : Coeff ι κ) (b : Coeff ν κ) : Coeff (ι ⊕ ν) κ :=
  (EuclideanSpace.equiv ((ι ⊕ ν) × κ) ℂ).symm (fun p => Sum.elim
    (fun i => a (i,p.2)) (fun j => b (j,p.2)) p.1)

omit [Fintype ι] [Fintype ν] [Fintype κ] in
@[simp] theorem leftCoeff_apply (a : Coeff (ι ⊕ ν) κ) (p : ι × κ) :
    leftCoeff a p = a (Sum.inl p.1,p.2) := rfl
omit [Fintype ι] [Fintype ν] [Fintype κ] in
@[simp] theorem rightCoeff_apply (a : Coeff (ι ⊕ ν) κ) (p : ν × κ) :
    rightCoeff a p = a (Sum.inr p.1,p.2) := rfl
omit [Fintype ι] [Fintype ν] [Fintype κ] in
@[simp] theorem joinCoeff_inl (a : Coeff ι κ) (b : Coeff ν κ) (i : ι) (j : κ) :
    joinCoeff a b (Sum.inl i,j) = a (i,j) := rfl
omit [Fintype ι] [Fintype ν] [Fintype κ] in
@[simp] theorem joinCoeff_inr (a : Coeff ι κ) (b : Coeff ν κ) (i : ν) (j : κ) :
    joinCoeff a b (Sum.inr i,j) = b (i,j) := rfl

 def splitEquiv (d : ν → ℝ) (hd : ∀ i, d i ≠ 0) :
    Coeff (ι ⊕ ν) κ ≃L[ℝ] Coeff ι κ × Coeff ν κ :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun a => (leftCoeff a, diag (fun p => d p.1) (rightCoeff a))
    invFun := fun p => joinCoeff p.1 (diag (fun q => (d q.1)⁻¹) p.2)
    left_inv := by
      intro a
      ext ⟨i,j⟩
      cases i with
      | inl i => rfl
      | inr i => simp [hd i]
    right_inv := by
      intro ⟨a,b⟩
      ext p
      · rfl
      · simp [hd p.1]
    map_add' := by
      intro a b
      ext p
      · rfl
      · simp [smul_add]
    map_smul' := by
      intro r a
      ext p
      · rfl
      · simp
        ring }

 def positiveScale (k : ν → ℕ) (hk : ∀ i, 0 < k i) :
    Coeff (ι ⊕ ν) κ ≃L[ℝ] Coeff ι κ × Coeff ν κ :=
  splitEquiv (fun i => Real.sqrt (k i : ℝ)) (fun i =>
    (Real.sqrt_pos.2 (by exact_mod_cast hk i)).ne')

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_12 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

 def velocityCoeff (k : ι → ℤ) (a : Coeff ι κ) : Coeff ι κ :=
   Complex.I • ((2 : ℝ) • diag (fun p => Real.pi*(k p.1 : ℝ)) a)

 def meanAction {H : Vector κ → ℝ} (_hH : ContDiff ℝ ∞ H) (x : C(Time,Vector κ)) : ℝ :=
    ∫ t : Time, inner (𝕜 := ℝ) (gradient H (x t)) (x t)/2-H (x t) ∂μ

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_13_rf9e987_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

 def linkRadius (κ : Type) [Fintype κ] (M : ℝ) : ℝ :=
  Real.sqrt (Real.pi/(2*(M*(Fintype.card κ : ℝ)+1)))

 def linkLevel (κ : Type) [Fintype κ] (M : ℝ) : ℝ :=
  Real.pi/4*(linkRadius κ M)^2

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PeriodicFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u114 u115

section NonsqueezingInline

namespace L2Paths
noncomputable section
open Set intervalIntegral
open MeasureTheory (volume)
open scoped Topology BoundedContinuousFunction
variable {E : Type u114} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev Segment := Icc (0 : ℝ) 1

local instance instFactLtRealOfNat_solutions : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
abbrev Time := AddCircle (1 : ℝ)

def restriction (x : C(Time,E)) : C(Segment,E) :=
  ⟨fun t => x (t.val : Time), x.continuous.comp (continuous_quot_mk.comp continuous_subtype_val)⟩

end
end L2Paths

namespace PeriodicFourier
noncomputable section
open MeasureTheory AddCircle Finset Set
open scoped ComplexConjugate Topology
local instance instFactLtRealOfNat_solutions : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
abbrev Time := AddCircle (1 : ℝ)
abbrev μ : Measure Time := AddCircle.haarAddCircle
open FourierPolynomial (integrable_continuous)

 def coefficient (n : ℤ) : C(Time,ℂ) →L[ℂ] ℂ := by
  let L : C(Time,ℂ) →ₗ[ℂ] ℂ := {
    toFun := fun f => fourierCoeff f n
    map_add' := fun f g => congrFun (fourierCoeff.add
      (integrable_continuous f.continuous) (integrable_continuous g.continuous)) n
    map_smul' := fun c f => fourierCoeff.const_smul f c n }
  apply L.mkContinuous 1
  intro f
  change ‖∫ t : Time, fourier (-n) t • f t ∂μ‖ ≤ 1*‖f‖
  have h := norm_integral_le_of_norm_le_const (μ := μ) (C := ‖f‖)
    (Filter.Eventually.of_forall (fun t : Time => show ‖fourier (-n) t • f t‖ ≤ ‖f‖ by
      simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using f.norm_coe_le_norm t))
  simpa using h

@[simp] theorem coefficient_apply (n : ℤ) (f : C(Time,ℂ)) : coefficient n f = fourierCoeff f n := rfl

 theorem continuous_lift {E : Type u115} [TopologicalSpace E] {f : ℝ → E}
    (hf : Continuous f) (hp : Function.Periodic f 1) : Continuous hp.lift :=
  hf.quotient_liftOn' _

 def primitive (v : C(Time,ℂ)) (t : ℝ) : ℂ := ∫ s in (0:ℝ)..t, v (s : Time)

 theorem hasDerivAt_primitive (v : C(Time,ℂ)) (t : ℝ) :
    HasDerivAt (primitive v) (v (t : Time)) t := by
  have hv : Continuous (fun s : ℝ => v (s : Time)) := v.continuous.comp continuous_quot_mk
  exact intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable _ _) hv.stronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt

 theorem periodic_primitive (v : C(Time,ℂ)) (hzero : coefficient 0 v = 0) :
    Function.Periodic (primitive v) 1 := by
  have hv : Continuous (fun s : ℝ => v (s : Time)) := v.continuous.comp continuous_quot_mk
  have hp : Function.Periodic (fun s : ℝ => v (s : Time)) 1 := by
    intro t
    simp
  have hi : ∫ s in (0:ℝ)..1, v (s : Time) = 0 := by
    have h := hzero
    rw [coefficient_apply, fourierCoeff_eq_intervalIntegral _ _ 0] at h
    simpa only [one_div_one, one_smul, zero_add, neg_zero, fourier_zero] using h
  intro t
  unfold primitive
  rw [hp.intervalIntegral_add_eq_add 0 t (fun a b => hv.intervalIntegrable a b)]
  simp only [zero_add, hi, add_zero]

 def periodicPrimitive (v : C(Time,ℂ)) (hzero : coefficient 0 v = 0) : C(Time,ℂ) :=
  ⟨(periodic_primitive v hzero).lift,
    continuous_lift (continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_primitive v t).continuousAt)) _⟩

@[simp] theorem periodicPrimitive_coe (v : C(Time,ℂ)) (hzero : coefficient 0 v = 0) (t : ℝ) :
    periodicPrimitive v hzero (t : Time) = primitive v t := rfl

end
end PeriodicFourier

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PeriodicSolutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
local instance instFactLtRealOfNat_solutions_14 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

 def coordPath (j : κ) : C(Time,Vector κ) →L[ℂ] C(Time,ℂ) :=
   ContinuousLinearMap.compLeftContinuous ℂ Time (PiLp.proj 2 (fun _ : κ => ℂ) j)

@[simp] theorem coordPath_apply (j : κ) (x : C(Time,Vector κ)) (t : Time) : coordPath j x t = x t j := rfl

 def gradPath {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) : C(Time,Vector κ) → C(Time,Vector κ) :=
   SmoothPaths.superpose (contDiff_gradient_function hH).continuous

end
end FourierPolynomial

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
open DiagonalQuadratic FourierPolynomial

 local instance instFactLtRealOfNat_solutions_rf9e987_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
def negativeMode (N : ℕ) (i : Fin (N+1)) : ℤ := -(i.val : ℤ)
 def positiveMode (N : ℕ) (i : Fin (N+1)) : ℕ := i.val+1
 def frequency (N : ℕ) : Fin (N+1) ⊕ Fin (N+1) → ℤ :=
   Sum.elim (negativeMode N) (fun i => (positiveMode N i : ℤ))

end
end HamiltonianPeriodic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.HamiltonianGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u119 u120

section NonsqueezingInline

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic
variable {κ : Type u120} [Fintype κ]

 def actionIntegral (H : Vector κ → ℝ) (x : ℝ → Vector κ) : ℝ :=
   ∫ t in (0:ℝ)..1, inner (𝕜 := ℝ) (gradient H (x t)) (x t)/2-H (x t)

end
end HamiltonianPeriodic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.EmbeddingInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u121 u122

section NonsqueezingInline

namespace EmbeddingInverse
noncomputable section
open Set Filter
open scoped ContDiff Topology
variable {E : Type u121} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 def localEquiv {U : Set E} (hU : IsOpen U) (f : E → E)
    (hf : ContDiffOn ℝ ∞ f U) (hi : InjOn f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) : OpenPartialHomeomorph E E :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (hi.toPartialEquiv f U) hf.continuousOn
    (LocalEmbedding.isOpenEmbedding hU hf hi hD).isOpenMap hU

@[simp] theorem localEquiv_apply {U : Set E} (hU : IsOpen U) (f : E → E)
    (hf : ContDiffOn ℝ ∞ f U) (hi : InjOn f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) (x : E) :
    localEquiv hU f hf hi hD x = f x := rfl

@[simp] theorem localEquiv_source {U : Set E} (hU : IsOpen U) (f : E → E)
    (hf : ContDiffOn ℝ ∞ f U) (hi : InjOn f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) :
    (localEquiv hU f hf hi hD).source = U := rfl

@[simp] theorem localEquiv_target {U : Set E} (hU : IsOpen U) (f : E → E)
    (hf : ContDiffOn ℝ ∞ f U) (hi : InjOn f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) :
    (localEquiv hU f hf hi hD).target = f '' U := rfl

 def extendFunction (e : OpenPartialHomeomorph E E) (f : E → ℝ) (y : E) : ℝ := by
  classical
  exact if y ∈ e.target then f (e.symm y) else 0

end
end EmbeddingInverse

namespace ComplexSymplectic
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial
variable {κ : Type u122} [Fintype κ]

 def form (v w : Vector κ) : ℝ := inner (𝕜 := ℝ) (Complex.I • v) w
 def Preserves (A : Vector κ →L[ℝ] Vector κ) : Prop := ∀ v w, form (A v) (A w) = form v w

end
end ComplexSymplectic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.SmoothProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section NonsqueezingInline

namespace SmoothProfiles
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

 def primitive (v : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in (0:ℝ)..s, v t

 def exteriorSlope (δ : ℝ) (s : ℝ) : ℝ := Real.smoothTransition (s/δ)
 def exterior (δ : ℝ) : ℝ → ℝ := primitive (exteriorSlope δ)

 def ballSlope (r L ε s : ℝ) : ℝ :=
    r*Real.smoothTransition ((s-ε)/ε)*Real.smoothTransition ((L-ε-s)/ε)
 def ballProfile (r L ε : ℝ) : ℝ → ℝ := primitive (ballSlope r L ε)
 def ballHeight (r L ε : ℝ) : ℝ := ballProfile r L ε (L-ε)

end
end SmoothProfiles

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.ExteriorHamiltonian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u123 u124 u125 u126

section NonsqueezingInline

namespace PushedBall
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial SmoothProfiles EmbeddingInverse
variable {κ : Type u123} [Fintype κ]

 def domain (L : ℝ) : Set (Vector κ) := {z | ‖z‖^2 < L}
 def core (L ε : ℝ) : Set (Vector κ) := Metric.closedBall 0 (Real.sqrt (L-ε))
 def radial (r L ε : ℝ) (z : Vector κ) : ℝ := ballProfile r L ε (‖z‖^2)

 def pushed (e : OpenPartialHomeomorph (Vector κ) (Vector κ)) (r L ε : ℝ) (z : Vector κ) : ℝ :=
   extendFunction e (fun w => radial r L ε w-ballHeight r L ε) z+ballHeight r L ε

end
end PushedBall

namespace ExteriorHamiltonian
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic SmoothProfiles
variable {κ : Type u124} [Fintype κ]

 def potential (d : κ → ℝ) (T δ : ℝ) (z : Vector κ) : ℝ := exterior δ (energy d z-T)
 def full (H₀ : Vector κ → ℝ) (d : κ → ℝ) (T δ : ℝ) (z : Vector κ) : ℝ :=
   H₀ z+potential d T δ z

end
end ExteriorHamiltonian

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.Nonsqueezing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u127

section NonsqueezingInline

namespace CylinderParameters
noncomputable section
open Set Filter Finset
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic
variable {κ : Type u127} [Fintype κ] [DecidableEq κ]

 def weights (j₀ : κ) (a b : ℝ) (j : κ) : ℝ := if j=j₀ then a else b

end
end CylinderParameters

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.CanonicalCylinder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u128

section

namespace SymmetricPolar
open Set
noncomputable section
variable {n : ℕ}

def canonicalSquareCylinder (q₀ p₀ : Position n) : Set (Phase n) :=
  {z | |inner (𝕜 := ℝ) p₀ z.1| < 1 ∧ |inner (𝕜 := ℝ) q₀ z.2| < 1}

end
end SymmetricPolar
end

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PlanarSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u129 u130

section
namespace PlanarSquare
noncomputable section
open Set Filter
open scoped ContDiff Topology

def square : Set ℂ := {z | |z.re| < 1 ∧ |z.im| < 1}
def radius (z : ℂ) : ℝ := Real.sqrt (2*(z.im+1)/Real.pi)
def angle : ℂ →L[ℝ] ℂ := Complex.reCLM.smulRight (-(Real.pi : ℂ)*Complex.I)
def rotation (z : ℂ) : ℂ := Complex.exp (angle z)
def map (z : ℂ) : ℂ := (radius z : ℂ)*rotation z

@[simp] theorem angle_re (z : ℂ) : (angle z).re = 0 := by simp [angle, Complex.mul_re, Complex.mul_im]
@[simp] theorem angle_im (z : ℂ) : (angle z).im = -Real.pi*z.re := by
  simp [angle, Complex.mul_re, Complex.mul_im, mul_comm]

@[simp] theorem norm_rotation (z : ℂ) : ‖rotation z‖ = 1 := by simp [rotation, Complex.norm_exp]

def derivative (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (radius z : ℂ) • (rotation z • angle) +
    rotation z • (Complex.ofRealCLM.comp ((1/(Real.pi*radius z)) • Complex.imCLM))

def form (v w : ℂ) : ℝ := v.re*w.im - w.re*v.im

end
end PlanarSquare
end

section
namespace PlanarCylinder
noncomputable section
open Set Filter
open scoped ContDiff Topology
variable {κ : Type u129} [Fintype κ] [DecidableEq κ]
abbrev V (κ : Type u130) := EuclideanSpace ℂ κ

def domain (j₀ : κ) : Set (V κ) := {z | z j₀ ∈ PlanarSquare.square}
def map (j₀ : κ) (z : V κ) : V κ :=
  (EuclideanSpace.equiv κ ℂ).symm (fun j => if j = j₀ then PlanarSquare.map (z j) else z j)

omit [Fintype κ] in
@[simp] theorem map_apply (j₀ j : κ) (z : V κ) :
    map j₀ z j = if j = j₀ then PlanarSquare.map (z j) else z j := rfl

omit [Fintype κ] in
@[simp] theorem map_first (j₀ : κ) (z : V κ) : map j₀ z j₀ = PlanarSquare.map (z j₀) := by simp

def derivative (j₀ : κ) (z : V κ) : V κ →L[ℝ] V κ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => if j = j₀ then
      (PlanarSquare.derivative (z j)).comp (PiLp.proj 2 (fun _ : κ => ℂ) j)
      else (PiLp.proj 2 (fun _ : κ => ℂ) j)))

omit [Fintype κ] in
@[simp] theorem derivative_apply (j₀ j : κ) (z v : V κ) :
    derivative j₀ z v j = if j = j₀ then PlanarSquare.derivative (z j) (v j) else v j := by
  change (if j = j₀ then (PlanarSquare.derivative (z j)).comp (PiLp.proj 2 (fun _ : κ => ℂ) j)
    else (PiLp.proj 2 (fun _ : κ => ℂ) j)) v = _
  split_ifs <;> rfl

def form (v w : V κ) : ℝ := ∑ j, PlanarSquare.form (v j) (w j)

end
end PlanarCylinder
end

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.CanonicalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u131 u132 u133

section
namespace CanonicalLinear
noncomputable section
open scoped InnerProductSpace
variable {κ : Type u131} [Fintype κ] [DecidableEq κ]
abbrev E (κ : Type u132) := EuclideanSpace ℝ κ

def coordinate (j : κ) : E κ →L[ℝ] ℝ := PiLp.proj 2 (fun _ : κ => ℝ) j

def adaptedMap (u v : E κ) (j : κ) : E κ →L[ℝ] E κ :=
  ContinuousLinearMap.id ℝ (E κ) - (1 / u j) • (coordinate j).smulRight u +
    (innerSL ℝ v).smulRight (EuclideanSpace.single j 1)

@[simp] theorem adaptedMap_apply (u v q : E κ) (j : κ) :
    adaptedMap u v j q = q - (q j / u j) • u + (inner (𝕜 := ℝ) v q) • EuclideanSpace.single j 1 := by
  simp [adaptedMap, coordinate, div_eq_mul_inv, smul_smul, mul_comm]

theorem adaptedMap_coordinate (u v q : E κ) (j : κ) (huj : u j ≠ 0) :
    adaptedMap u v j q j = inner (𝕜 := ℝ) v q := by
  simp [adaptedMap_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, div_mul_cancel₀ _ huj]

theorem adaptedMap_injective {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) : Function.Injective (adaptedMap u v j) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro q hq
  change adaptedMap u v j q = 0 at hq
  have hi : inner (𝕜 := ℝ) v q = 0 := by
    have hh := congrArg (fun x : E κ => x j) hq
    simpa only [adaptedMap_coordinate u v q j huj, PiLp.zero_apply] using hh
  have he : q = (q j/u j) • u := by
    simpa only [adaptedMap_apply, hi, zero_smul, add_zero, sub_eq_zero] using hq
  have ht : q j/u j = 0 := by
    have hh := congrArg (fun x : E κ => inner (𝕜 := ℝ) v x) he
    simpa only [real_inner_smul_right, hvu, mul_one, hi] using hh.symm
  simp only [ht, zero_smul] at he
  exact he

def adapted {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) : E κ ≃L[ℝ] E κ :=
  ContinuousLinearEquiv.ofBijective (adaptedMap u v j)
    (LinearMap.ker_eq_bot.mpr (adaptedMap_injective j huj hvu))
    (LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective (adaptedMap_injective j huj hvu)))

@[simp] theorem adapted_apply {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) (q : E κ) :
    adapted j huj hvu q = adaptedMap u v j q := rfl

def cotangent (A : E κ ≃L[ℝ] E κ) : (E κ × E κ) →L[ℝ] (E κ × E κ) :=
  (A.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ (E κ) (E κ))).prod
    (A.symm.toContinuousLinearMap.adjoint.comp (ContinuousLinearMap.snd ℝ (E κ) (E κ)))

omit [DecidableEq κ] in
@[simp] theorem cotangent_apply (A : E κ ≃L[ℝ] E κ) (x : E κ × E κ) :
    cotangent A x = (A x.1, A.symm.toContinuousLinearMap.adjoint x.2) := rfl

end
end CanonicalLinear
end

section
namespace UpperCoordinates
noncomputable section
open Set
open scoped ContDiff
variable {κ : Type u133} [Fintype κ] [DecidableEq κ]
open ComplexCoordinates CanonicalLinear

def phaseForm (x y : R κ × R κ) : ℝ :=
  inner (𝕜 := ℝ) x.1 y.2 - inner (𝕜 := ℝ) y.1 x.2

def targetCoordinates (A : E κ ≃L[ℝ] E κ) : (E κ × E κ) →L[ℝ] C κ :=
  parts.symm.toContinuousLinearMap.comp (cotangent A)

end
end UpperCoordinates
end

end OAI
end


