-- Prove2me | solution 1 for AutomorphicForm.isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/acd59139-9586-51cf-901e-1b511805864b

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Module
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

namespace P2M
namespace ReflectedLowering

noncomputable section

open NumberField NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F]

private def mulRightArrayCLM (A : Matrix (Fin 2) (Fin 2) ℝ) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun e => Matrix.of.symm (Matrix.of e * A)
      map_add' := by
        intro a b
        ext i j
        simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        ext i j
        simp [Matrix.mul_apply, mul_add, mul_assoc] }

private theorem mulRightArrayCLM_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (e : Fin 2 → Fin 2 → ℝ) :
    mulRightArrayCLM A e = Matrix.of.symm (Matrix.of e * A) := rfl

private theorem isArchSmoothAt_archDerivAt_apply_mul_archRealLiftAt {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F)
    {e : Fin 2 → Fin 2 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    archDerivAt hw d φ (g * archRealLiftAt hw e) =
      fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) e (mulRightArrayCLM (archDirMatrix d) e) := by
  have hΦ := hφ g
  have hopen := isOpen_setOf_det_ne_zero
  have hdiff : HasFDerivAt (fun e' => φ (g * archRealLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) e)
      (Matrix.of.symm (Matrix.of e * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [of_symm_mul_archFlowMatrix_zero]
    exact ((hΦ.contDiffAt (hopen.mem_nhds he)).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) =
      fun t : ℝ => φ (g * archRealLiftAt hw
        (Matrix.of.symm (Matrix.of e * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)))) := by
    funext t
    rw [archFlowAt, mul_assoc, archRealLiftAt_mul_archRealGLAt hw he]
  rw [mulRightArrayCLM_apply]
  show deriv (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) 0 = _
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrix e d)).deriv

private theorem det_of_of_symm_one : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
  rw [Equiv.apply_symm_apply, Matrix.det_one]
  exact one_ne_zero

private theorem isArchSmoothAt_archDerivAt_apply_eq_fderiv {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d φ g =
      fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (mulRightArrayCLM (archDirMatrix d) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))) := by
  rw [← (isArchSmoothAt_archDerivAt_apply_mul_archRealLiftAt hφ) d g det_of_of_symm_one,
      archRealLiftAt_of_symm_one, mul_one]

private theorem isArchSmoothAt_archDerivAt_archDerivAt_apply {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d d' : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d' (archDerivAt hw d φ) g =
      fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (mulRightArrayCLM (archDirMatrix d)
            (mulRightArrayCLM (archDirMatrix d') (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)))) +
        fderiv ℝ (fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')))
          (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (mulRightArrayCLM (archDirMatrix d') (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)))
          (mulRightArrayCLM (archDirMatrix d) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))) := by
  have hopen := isOpen_setOf_det_ne_zero
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fun e'' => φ (g * archRealLiftAt hw e'')))
      {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0} :=
    (hφ g).fderiv_of_isOpen hopen (by exact WithTop.coe_le_coe.mpr (le_top : ((1 + 1 : ℕ) : ℕ∞) ≤ ⊤))
  have hΦ' : HasFDerivAt (fderiv ℝ (fun e'' => φ (g * archRealLiftAt hw e'')))
      (fderiv ℝ (fderiv ℝ (fun e'' => φ (g * archRealLiftAt hw e'')))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
    ((h1.contDiffAt (hopen.mem_nhds det_of_of_symm_one)).differentiableAt (by simp)).hasFDerivAt
  have hclm := hΦ'.clm_apply (mulRightArrayCLM (archDirMatrix d)).hasFDerivAt
  have hev : (fun e' => archDerivAt hw d φ (g * archRealLiftAt hw e')) =ᶠ[nhds
      (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))]
      fun e' => fderiv ℝ (fun e'' => φ (g * archRealLiftAt hw e'')) e' (mulRightArrayCLM (archDirMatrix d) e') :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds det_of_of_symm_one) fun e' he' =>
      (isArchSmoothAt_archDerivAt_apply_mul_archRealLiftAt hφ) d g he'
  rw [(isArchSmoothAt_archDerivAt_apply_eq_fderiv (hφ.archDerivAt d)) d' g, (hclm.congr_of_eventuallyEq hev).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

private theorem isArchSmoothAt_isSymmSndFDerivAt_of_symm_one {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F) :
    IsSymmSndFDerivAt ℝ (fun e' => φ (g * archRealLiftAt hw e')) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
  ((hφ g).contDiffAt (isOpen_setOf_det_ne_zero.mem_nhds det_of_of_symm_one)).isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

private theorem isArchSmoothAt_archDerivAt_E_Fm_sub_archDerivAt_Fm_E {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .E (archDerivAt hw .Fm φ) - archDerivAt hw .Fm (archDerivAt hw .E φ) = archDerivAt hw .H φ := by
  funext g
  rw [Pi.sub_apply, (isArchSmoothAt_archDerivAt_archDerivAt_apply hφ) .Fm .E g,
      (isArchSmoothAt_archDerivAt_archDerivAt_apply hφ) .E .Fm g,
    (isArchSmoothAt_archDerivAt_apply_eq_fderiv hφ) .H g,
    ((isArchSmoothAt_isSymmSndFDerivAt_of_symm_one hφ) g).eq (mulRightArrayCLM (archDirMatrix .Fm) _)
      (mulRightArrayCLM (archDirMatrix .E) _),
    add_sub_add_right_eq_sub, ← _root_.map_sub]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mulRightArrayCLM_apply, archDirMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.of_symm_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]

private theorem isArchSmoothAt_archDerivAt_H_E_sub_archDerivAt_E_H {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .H (archDerivAt hw .E φ) - archDerivAt hw .E (archDerivAt hw .H φ) =
      archDerivAt hw .E φ + archDerivAt hw .E φ := by
  funext g
  rw [Pi.sub_apply, Pi.add_apply, (isArchSmoothAt_archDerivAt_archDerivAt_apply hφ) .E .H g,
      (isArchSmoothAt_archDerivAt_archDerivAt_apply hφ) .H .E g,
    (isArchSmoothAt_archDerivAt_apply_eq_fderiv hφ) .E g,
    ((isArchSmoothAt_isSymmSndFDerivAt_of_symm_one hφ) g).eq (mulRightArrayCLM (archDirMatrix .E) _)
      (mulRightArrayCLM (archDirMatrix .H) _),
    add_sub_add_right_eq_sub, ← _root_.map_sub, ← _root_.map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mulRightArrayCLM_apply, archDirMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.of_symm_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]

private theorem isArchSmoothAt_archDerivAt_H_Fm_sub_archDerivAt_Fm_H {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .H (archDerivAt hw .Fm φ) - archDerivAt hw .Fm (archDerivAt hw .H φ) =
      -(archDerivAt hw .Fm φ + archDerivAt hw .Fm φ) := by
  funext g
  rw [Pi.sub_apply, Pi.neg_apply, Pi.add_apply, (isArchSmoothAt_archDerivAt_archDerivAt_apply hφ) .Fm .H g,
    (isArchSmoothAt_archDerivAt_archDerivAt_apply hφ) .H .Fm g, (isArchSmoothAt_archDerivAt_apply_eq_fderiv hφ) .Fm g,
    ((isArchSmoothAt_isSymmSndFDerivAt_of_symm_one hφ) g).eq (mulRightArrayCLM (archDirMatrix .Fm) _)
      (mulRightArrayCLM (archDirMatrix .H) _),
    add_sub_add_right_eq_sub, ← _root_.map_sub, ← _root_.map_add, ← _root_.map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mulRightArrayCLM_apply, archDirMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.of_symm_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]

private theorem archDerivAt_sub {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) (d : ArchDir) :
    archDerivAt hw d (φ - ψ) = archDerivAt hw d φ - archDerivAt hw d ψ := by
  rw [sub_eq_add_neg φ ψ, ← neg_one_smul ℂ ψ, archDerivAt_add hφ (hψ.smul (-1)) d, archDerivAt_smul, neg_one_smul ℂ]
  exact (sub_eq_add_neg _ _).symm

private def archRotDerivAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAt hw .E φ - archDerivAt hw .Fm φ

private def archRaiseAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

private def archLowerAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)

private theorem isArchSmoothAt_archRotDerivAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (archRotDerivAt hw φ) :=
  (hφ.archDerivAt .E).sub (hφ.archDerivAt .Fm)

private theorem isArchSmoothAt_archRaiseAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (archRaiseAt hw φ) :=
  (hφ.archDerivAt .H).add (((hφ.archDerivAt .E).add (hφ.archDerivAt .Fm)).smul Complex.I)

private theorem isArchSmoothAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (archLowerAt hw φ) :=
  (hφ.archDerivAt .H).sub (((hφ.archDerivAt .E).add (hφ.archDerivAt .Fm)).smul Complex.I)

private theorem isArchSmoothAt_archRaiseAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞
    F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archRaiseAt hw (archLowerAt hw φ) =
      (-4 : ℂ) • archCasimirAt hw φ + archRotDerivAt hw (archRotDerivAt hw φ) -
        (2 * Complex.I) • archRotDerivAt hw φ := by
  have hH := hφ.archDerivAt .H
  have hE := hφ.archDerivAt .E
  have hF := hφ.archDerivAt .Fm
  have hexp : ∀ a : ArchDir, archDerivAt hw a (archLowerAt hw φ) =
      archDerivAt hw a (archDerivAt hw .H φ) -
        Complex.I • (archDerivAt hw a (archDerivAt hw .E φ) + archDerivAt hw a (archDerivAt hw .Fm φ)) := by
    intro a
    rw [archLowerAt, archDerivAt_sub hH ((hE.add hF).smul Complex.I) a, archDerivAt_smul,
      archDerivAt_add hE hF a]
  have hR1 : archDerivAt hw .Fm (archDerivAt hw .E φ) =
      archDerivAt hw .E (archDerivAt hw .Fm φ) - archDerivAt hw .H φ := by
    rw [← (isArchSmoothAt_archDerivAt_E_Fm_sub_archDerivAt_Fm_E hφ)]
    abel
  have hR2 : archDerivAt hw .E (archDerivAt hw .H φ) =
      archDerivAt hw .H (archDerivAt hw .E φ) - (archDerivAt hw .E φ + archDerivAt hw .E φ) := by
    rw [← (isArchSmoothAt_archDerivAt_H_E_sub_archDerivAt_E_H hφ)]
    abel
  have hR3 : archDerivAt hw .Fm (archDerivAt hw .H φ) =
      archDerivAt hw .H (archDerivAt hw .Fm φ) + (archDerivAt hw .Fm φ + archDerivAt hw .Fm φ) := by
    rw [sub_eq_iff_eq_add.mp (isArchSmoothAt_archDerivAt_H_Fm_sub_archDerivAt_Fm_H hφ)]
    abel
  rw [archRaiseAt, hexp, hexp, hexp, AutomorphicForm.archCasimirAt, archRotDerivAt,
    archRotDerivAt, archDerivAt_sub hE hF, archDerivAt_sub hE hF, hR1, hR2, hR3]
  simp only [smul_sub, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  module

private def rotationArray (θ : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![Real.cos θ, Real.sin θ], ![-Real.sin θ, Real.cos θ]]

private theorem of_rotationArray (θ : ℝ) :
    Matrix.of (rotationArray θ) = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := rfl

private theorem det_of_rotationArray (θ : ℝ) : (Matrix.of (rotationArray θ)).det ≠ 0 := by
  rw [of_rotationArray, Matrix.det_fin_two_of]
  nlinarith [Real.cos_sq_add_sin_sq θ]

private theorem rotationArray_zero : rotationArray 0 = Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotationArray, Matrix.one_fin_two]

private theorem hasDerivAt_rotationArray :
    HasDerivAt rotationArray (![![0, 1], ![-1, 0]] : Fin 2 → Fin 2 → ℝ) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  fin_cases i <;> fin_cases j <;> simp only [rotationArray] <;>
    first
      | simpa using Real.hasDerivAt_cos 0
      | simpa using Real.hasDerivAt_sin 0
      | (have h__af := (Real.hasDerivAt_sin 0).neg; simp at h__af; exact h__af)

private theorem archRealLiftAt_rotationArray {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) :
    archRealLiftAt hw (rotationArray θ) = archRealGLAt hw (GL2Real.rotation θ) := by
  rw [archRealLiftAt_of_det_ne_zero hw (det_of_rotationArray θ)]
  rfl

private theorem rotation_mem_rowIsometrySubgroup₀ (θ : ℝ) : GL2Real.rotation θ ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  have hc : ((GL2Real.rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
    simp [GL2Real.rotation, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h1 : Real.cos θ * Real.cos θ - Real.sin θ * -Real.sin θ = 1 := by
    linear_combination Real.cos_sq_add_sin_sq θ
  refine ⟨?_, ?_, ?_⟩
  · rw [hc, Matrix.det_fin_two_of]
    exact h1
  · rw [hc, Matrix.det_fin_two_of, h1, norm_one]
  · intro x y
    rw [hc]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq θ

omit [NumberField F] in
private theorem norm_ringEquivRealOfIsReal_symm {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  rw [← norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x), RingEquiv.apply_symm_apply]

private def rotationAt {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) : rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm (norm_ringEquivRealOfIsReal_symm hw)
    ⟨GL2Real.rotation θ, rotation_mem_rowIsometrySubgroup₀ θ⟩

private theorem archRealGLAt_rotation {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) :
    archRealGLAt hw (GL2Real.rotation θ) =
      adelicArchGLInclAt F w ((rotationAt hw θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) := rfl

omit [NumberField F] in

private theorem archWeightCharAt_one_rotationAt {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) :
    ((archWeightCharAt hw 1 (rotationAt hw θ) : ℂˣ) : ℂ) = ⟨Real.cos θ, Real.sin θ⟩ := by
  have hentry : ∀ i j : Fin 2,
      ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw)
          (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (GL2Real.rotation θ)) : GL (Fin 2) ℝ) :
            Matrix (Fin 2) (Fin 2) ℝ) i j =
        ((GL2Real.rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    intro i j
    rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry, RingEquiv.apply_symm_apply]
  show ((archWeightOneℝ (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      (rotationAt hw θ)) ^ (1 : ℤ) : ℂˣ) : ℂ) = _
  rw [zpow_one]
  show firstRowℂ _ = _
  unfold firstRowℂ
  refine Complex.ext ?_ ?_
  · exact hentry 0 0
  · exact hentry 0 1

private theorem isArchSmoothAt_archRotDerivAt_eq_of_hasArchCharacterAt₀_one {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hwt : HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ) :
    archRotDerivAt hw φ = Complex.I • φ := by
  funext g
  have hopen := isOpen_setOf_det_ne_zero

  have hcurve : (fun θ : ℝ => φ (g * archRealLiftAt hw (rotationArray θ))) =
      fun θ : ℝ => (⟨Real.cos θ, Real.sin θ⟩ : ℂ) * φ g := by
    funext θ
    rw [archRealLiftAt_rotationArray, archRealGLAt_rotation, hwt (rotationAt hw θ) g, archWeightCharAt_one_rotationAt]

  have hder : HasDerivAt (fun θ : ℝ => (⟨Real.cos θ, Real.sin θ⟩ : ℂ) * φ g) (Complex.I * φ g) 0 := by
    have hfun : (fun θ : ℝ => (⟨Real.cos θ, Real.sin θ⟩ : ℂ) * φ g) =
        fun θ : ℝ => (((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I) * φ g := by
      funext θ
      rw [Complex.mk_eq_add_mul_I]
    have h2 : HasDerivAt (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I)
        (((-Real.sin 0 : ℝ) : ℂ) + ((Real.cos 0 : ℝ) : ℂ) * Complex.I) 0 :=
      ((Real.hasDerivAt_cos 0).ofReal_comp).add ((Real.hasDerivAt_sin 0).ofReal_comp.mul_const Complex.I)
    rw [hfun]
    simpa using h2.mul_const (φ g)

  have hΦ : HasFDerivAt (fun e' => φ (g * archRealLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      (rotationArray 0) := by
    rw [rotationArray_zero]
    exact (((hφ g).contDiffAt (hopen.mem_nhds det_of_of_symm_one)).differentiableAt (by simp)).hasFDerivAt
  have hchain := hΦ.comp_hasDerivAt (0 : ℝ) hasDerivAt_rotationArray
  have hdir : mulRightArrayCLM (archDirMatrix .E) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) -
      mulRightArrayCLM (archDirMatrix .Fm) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        (![![0, 1], ![-1, 0]] : Fin 2 → Fin 2 → ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [mulRightArrayCLM_apply, archDirMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.of_symm_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
  rw [archRotDerivAt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, (isArchSmoothAt_archDerivAt_apply_eq_fderiv hφ) .E g,
    (isArchSmoothAt_archDerivAt_apply_eq_fderiv hφ) .Fm g, ← _root_.map_sub, hdir]
  have hcomp : (fun e' => φ (g * archRealLiftAt hw e')) ∘ rotationArray =
      fun θ : ℝ => (⟨Real.cos θ, Real.sin θ⟩ : ℂ) * φ g := hcurve
  rw [hcomp] at hchain
  exact hchain.unique hder

private def reflJ : GL (Fin 2) ℝ := UpperHalfPlane.J

private theorem reflJ_coe : (reflJ : Matrix (Fin 2) (Fin 2) ℝ) = !![(-1 : ℝ), 0; 0, 1] := UpperHalfPlane.val_J

private theorem reflJ_mul_reflJ : reflJ * reflJ = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [reflJ_coe, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]

private def reflSign : ArchDir → ℝ
  | .H => 1
  | .E => -1
  | .Fm => -1

private theorem archFlowMatrix_mul_reflJ (d : ArchDir) (t : ℝ) :
    archFlowMatrix d t * reflJ = reflJ * archFlowMatrix d (reflSign d * t) := by
  cases d <;> refine Units.ext ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [archFlowMatrix, reflSign, reflJ_coe, splitTorusGL2_coe, unipotentGL2_coe, lowerUnipotentGL2_coe,
      Matrix.mul_apply, Fin.sum_univ_two]

private theorem archFlowAt_mul_archRealGLAt_reflJ {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    archFlowAt hw d t * archRealGLAt hw reflJ = archRealGLAt hw reflJ * archFlowAt hw d (reflSign d * t) := by
  simp only [archFlowAt]
  rw [← map_mul, ← map_mul, archFlowMatrix_mul_reflJ]

private def reflAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => φ (g * archRealGLAt hw reflJ)

private theorem reflAt_reflAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    reflAt hw (reflAt hw φ) = φ := by
  funext g
  simp only [reflAt]
  rw [mul_assoc, ← map_mul, reflJ_mul_reflJ, map_one, mul_one]

private theorem archDerivAt_neg {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAt hw d (-φ) = -archDerivAt hw d φ := by
  rw [← neg_one_smul ℂ φ, archDerivAt_smul, neg_one_smul ℂ]

private theorem archDerivAt_reflAt {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAt hw d (reflAt hw φ) = reflSign d • reflAt hw (archDerivAt hw d φ) := by
  funext g
  have hfun : (fun t : ℝ => reflAt hw φ (g * archFlowAt hw d t)) =
      fun t : ℝ => φ (g * archRealGLAt hw reflJ * archFlowAt hw d (reflSign d * t)) := by
    funext t
    simp only [reflAt]
    rw [mul_assoc g (archFlowAt hw d t), archFlowAt_mul_archRealGLAt_reflJ, ← mul_assoc]
  show deriv (fun t : ℝ => reflAt hw φ (g * archFlowAt hw d t)) 0 =
    reflSign d • archDerivAt hw d φ (g * archRealGLAt hw reflJ)
  rw [hfun, deriv_comp_mul_left (reflSign d) (fun s : ℝ => φ (g * archRealGLAt hw reflJ * archFlowAt hw d s)) 0,
    mul_zero]
  rfl

private theorem archCasimirAt_reflAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archCasimirAt hw (reflAt hw φ) = reflAt hw (archCasimirAt hw φ) := by
  simp only [AutomorphicForm.archCasimirAt, archDerivAt_reflAt, reflSign, one_smul, neg_one_smul, archDerivAt_neg,
    neg_neg]
  funext g
  simp only [reflAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

private theorem archRotDerivAt_reflAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archRotDerivAt hw (reflAt hw φ) = -reflAt hw (archRotDerivAt hw φ) := by
  simp only [archRotDerivAt, archDerivAt_reflAt, reflSign, neg_one_smul]
  funext g
  simp only [reflAt, Pi.neg_apply, Pi.sub_apply]
  ring

private theorem archLowerAt_reflAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archLowerAt hw (reflAt hw φ) = reflAt hw (archRaiseAt hw φ) := by
  simp only [archLowerAt, archRaiseAt, archDerivAt_reflAt, reflSign, one_smul,
    neg_one_smul]
  funext g
  simp only [reflAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem isArchSmoothAt_reflAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (reflAt hw φ) := by
  intro g
  have hdetJ : ((reflJ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 reflJ.isUnit).ne_zero
  have hmaps : Set.MapsTo (fun e : Fin 2 → Fin 2 → ℝ =>
      (Matrix.of.symm (Matrix.of e * (reflJ : Matrix (Fin 2) (Fin 2) ℝ)) : Fin 2 → Fin 2 → ℝ))
      {e | (Matrix.of e).det ≠ 0} {e | (Matrix.of e).det ≠ 0} := by
    intro e he
    show (Matrix.of (Matrix.of.symm (Matrix.of e * (reflJ : Matrix (Fin 2) (Fin 2) ℝ)))).det ≠ 0
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero he hdetJ
  refine ((hφ g).comp ((contDiff_of_symm_mul_const (reflJ : Matrix (Fin 2) (Fin 2) ℝ)).contDiffOn) hmaps).congr ?_
  intro e he
  show φ (g * archRealLiftAt hw e * archRealGLAt hw reflJ) =
    φ (g * archRealLiftAt hw (Matrix.of.symm (Matrix.of e * (reflJ : Matrix (Fin 2) (Fin 2) ℝ))))
  rw [mul_assoc, archRealLiftAt_mul_archRealGLAt hw he]

private theorem isArchSmoothAt_archDerivAt_Fm_E {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .Fm (archDerivAt hw .E φ) = archDerivAt hw .E (archDerivAt hw .Fm φ) - archDerivAt hw .H φ := by
  rw [← (isArchSmoothAt_archDerivAt_E_Fm_sub_archDerivAt_Fm_E hφ)]
  abel

private theorem isArchSmoothAt_archDerivAt_E_H {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .E (archDerivAt hw .H φ) =
      archDerivAt hw .H (archDerivAt hw .E φ) - (archDerivAt hw .E φ + archDerivAt hw .E φ) := by
  rw [← (isArchSmoothAt_archDerivAt_H_E_sub_archDerivAt_E_H hφ)]
  abel

private theorem isArchSmoothAt_archDerivAt_Fm_H {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .Fm (archDerivAt hw .H φ) =
      archDerivAt hw .H (archDerivAt hw .Fm φ) + (archDerivAt hw .Fm φ + archDerivAt hw .Fm φ) := by
  rw [sub_eq_iff_eq_add.mp (isArchSmoothAt_archDerivAt_H_Fm_sub_archDerivAt_Fm_H hφ)]
  abel

private theorem isArchSmoothAt_archCasimirAt_archDerivAt_H {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2
    (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archCasimirAt hw (archDerivAt hw .H φ) = archDerivAt hw .H (archCasimirAt hw φ) := by
  have hH := hφ.archDerivAt .H
  have hF := hφ.archDerivAt .Fm
  have hHH := hH.archDerivAt .H
  have hEF := hF.archDerivAt .E
  simp only [AutomorphicForm.archCasimirAt, archDerivAt_neg, archDerivAt_smul,
    archDerivAt_add ((hHH.smul (1 / 4 : ℂ)).sub (hH.smul (1 / 2 : ℂ))) hEF .H,
    archDerivAt_sub (hHH.smul (1 / 4 : ℂ)) (hH.smul (1 / 2 : ℂ)) .H, (isArchSmoothAt_archDerivAt_Fm_H hφ),
    archDerivAt_add (hF.archDerivAt .H) (hF.add hF) .E, archDerivAt_add hF hF .E, (isArchSmoothAt_archDerivAt_E_H hF)]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem isArchSmoothAt_archCasimirAt_archDerivAt_E {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2
    (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archCasimirAt hw (archDerivAt hw .E φ) = archDerivAt hw .E (archCasimirAt hw φ) := by
  have hH := hφ.archDerivAt .H
  have hE := hφ.archDerivAt .E
  have hF := hφ.archDerivAt .Fm
  have hHH := hH.archDerivAt .H
  have hEF := hF.archDerivAt .E
  simp only [AutomorphicForm.archCasimirAt, archDerivAt_neg, archDerivAt_smul,
    archDerivAt_add ((hHH.smul (1 / 4 : ℂ)).sub (hH.smul (1 / 2 : ℂ))) hEF .E,
    archDerivAt_sub (hHH.smul (1 / 4 : ℂ)) (hH.smul (1 / 2 : ℂ)) .E, (isArchSmoothAt_archDerivAt_E_H hH),
        (isArchSmoothAt_archDerivAt_E_H hφ),
    archDerivAt_sub (hE.archDerivAt .H) (hE.add hE) .H, archDerivAt_add hE hE .H, (isArchSmoothAt_archDerivAt_Fm_E hφ),
    archDerivAt_sub hEF hH .E]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem isArchSmoothAt_archCasimirAt_archDerivAt_Fm {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2
    (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archCasimirAt hw (archDerivAt hw .Fm φ) = archDerivAt hw .Fm (archCasimirAt hw φ) := by
  have hH := hφ.archDerivAt .H
  have hF := hφ.archDerivAt .Fm
  have hHH := hH.archDerivAt .H
  have hEF := hF.archDerivAt .E
  simp only [AutomorphicForm.archCasimirAt, archDerivAt_neg, archDerivAt_smul,
    archDerivAt_add ((hHH.smul (1 / 4 : ℂ)).sub (hH.smul (1 / 2 : ℂ))) hEF .Fm,
    archDerivAt_sub (hHH.smul (1 / 4 : ℂ)) (hH.smul (1 / 2 : ℂ)) .Fm, (isArchSmoothAt_archDerivAt_Fm_H hH),
        (isArchSmoothAt_archDerivAt_Fm_H hφ),
    archDerivAt_add (hF.archDerivAt .H) (hF.add hF) .H, archDerivAt_add hF hF .H, (isArchSmoothAt_archDerivAt_Fm_E hF)]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem archCasimirAt_sub {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) :
    archCasimirAt hw (φ - ψ) = archCasimirAt hw φ - archCasimirAt hw ψ := by
  rw [sub_eq_add_neg φ ψ, ← neg_one_smul ℂ ψ, archCasimirAt_add hφ (hψ.smul (-1)), archCasimirAt_smul, neg_one_smul ℂ]
  exact (sub_eq_add_neg _ _).symm

private theorem isArchSmoothAt_archCasimirAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞
    F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archCasimirAt hw (archLowerAt hw φ) = archLowerAt hw (archCasimirAt hw φ) := by
  have hH := hφ.archDerivAt .H
  have hE := hφ.archDerivAt .E
  have hF := hφ.archDerivAt .Fm
  show archCasimirAt hw (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)) =
    archLowerAt hw (archCasimirAt hw φ)
  rw [archCasimirAt_sub hH ((hE.add hF).smul Complex.I), archCasimirAt_smul, archCasimirAt_add hE hF,
    (isArchSmoothAt_archCasimirAt_archDerivAt_H hφ), (isArchSmoothAt_archCasimirAt_archDerivAt_E hφ),
        (isArchSmoothAt_archCasimirAt_archDerivAt_Fm hφ)]
  rfl

private theorem archLowerAt_smul {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archLowerAt hw (c • φ) = c • archLowerAt hw φ := by
  simp only [archLowerAt, archDerivAt_smul]
  module

private theorem reflAt_smul {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    reflAt hw (c • φ) = c • reflAt hw φ := rfl

private theorem isArchSmoothAt_archCasimirAt_reflAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) {lam : ℂ} (hlam : archCasimirAt hw φ = lam • φ) :
    archCasimirAt hw (reflAt hw (archLowerAt hw φ)) = lam • reflAt hw (archLowerAt hw φ) := by
  rw [archCasimirAt_reflAt, (isArchSmoothAt_archCasimirAt_archLowerAt hφ), hlam, archLowerAt_smul, reflAt_smul]

private theorem isArchSmoothAt_archRotDerivAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2
    (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) :
    archRotDerivAt hw (archLowerAt hw φ) =
      archLowerAt hw (archRotDerivAt hw φ) - (2 * Complex.I) • archLowerAt hw φ := by
  have hH := hφ.archDerivAt .H
  have hE := hφ.archDerivAt .E
  have hF := hφ.archDerivAt .Fm
  simp only [archRotDerivAt, archLowerAt, archDerivAt_smul,
    archDerivAt_sub hH ((hE.add hF).smul Complex.I) .E, archDerivAt_sub hH ((hE.add hF).smul Complex.I) .Fm,
    archDerivAt_add hE hF .E, archDerivAt_add hE hF .Fm, archDerivAt_sub hE hF .H, archDerivAt_sub hE hF .E,
    archDerivAt_sub hE hF .Fm, (isArchSmoothAt_archDerivAt_E_H hφ), (isArchSmoothAt_archDerivAt_Fm_H hφ),
        (isArchSmoothAt_archDerivAt_Fm_E hφ)]
  funext g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-2 * (archDerivAt hw .E φ g + archDerivAt hw .Fm φ g)) * Complex.I_sq

private theorem isArchSmoothAt_archRotDerivAt_archLowerAt_of_eq {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hW : archRotDerivAt hw φ = Complex.I • φ) :
    archRotDerivAt hw (archLowerAt hw φ) = (-Complex.I) • archLowerAt hw φ := by
  rw [(isArchSmoothAt_archRotDerivAt_archLowerAt hφ), hW, archLowerAt_smul]
  module

private theorem isArchSmoothAt_archRotDerivAt_reflAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hW : archRotDerivAt hw φ = Complex.I • φ) :
    archRotDerivAt hw (reflAt hw (archLowerAt hw φ)) = Complex.I • reflAt hw (archLowerAt hw φ) := by
  rw [archRotDerivAt_reflAt, (isArchSmoothAt_archRotDerivAt_archLowerAt_of_eq hφ) hW, reflAt_smul]
  module

private theorem hasDerivAt_rotationArray' (θ : ℝ) :
    HasDerivAt rotationArray
      (![![-Real.sin θ, Real.cos θ], ![-Real.cos θ, -Real.sin θ]] : Fin 2 → Fin 2 → ℝ) θ := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  fin_cases i <;> fin_cases j <;> simp only [rotationArray] <;>
    first
      | simpa using Real.hasDerivAt_cos θ
      | simpa using Real.hasDerivAt_sin θ
      | (have h__af := (Real.hasDerivAt_sin θ).neg; simp at h__af ⊢; exact h__af)

private theorem mulRightArrayCLM_E_sub_Fm_rotationArray (θ : ℝ) :
    mulRightArrayCLM (archDirMatrix .E) (rotationArray θ) - mulRightArrayCLM (archDirMatrix .Fm) (rotationArray θ) =
      (![![-Real.sin θ, Real.cos θ], ![-Real.cos θ, -Real.sin θ]] : Fin 2 → Fin 2 → ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mulRightArrayCLM_apply, archDirMatrix, rotationArray, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.of_symm_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]

private theorem exp_neg_ofReal_mul_I_mul_exp (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-((θ : ℂ) * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

private theorem exp_ofReal_mul_I_eq_mk (θ : ℝ) : Complex.exp ((θ : ℂ) * Complex.I) = ⟨Real.cos θ, Real.sin θ⟩ := by
  refine Complex.ext ?_ ?_
  · exact Complex.exp_ofReal_mul_I_re θ
  · exact Complex.exp_ofReal_mul_I_im θ

private theorem isArchSmoothAt_apply_mul_archRealLiftAt_rotationArray {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hW : archRotDerivAt hw φ = Complex.I • φ)
    (θ : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    φ (g * archRealLiftAt hw (rotationArray θ)) = (⟨Real.cos θ, Real.sin θ⟩ : ℂ) * φ g := by
  have hopen := isOpen_setOf_det_ne_zero
  set f : ℝ → ℂ := fun θ => φ (g * archRealLiftAt hw (rotationArray θ)) with hf

  have hf' : ∀ θ : ℝ, HasDerivAt f (Complex.I * f θ) θ := by
    intro θ
    have hΦ : HasFDerivAt (fun e' => φ (g * archRealLiftAt hw e'))
        (fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (rotationArray θ)) (rotationArray θ) :=
      (((hφ g).contDiffAt (hopen.mem_nhds (det_of_rotationArray θ))).differentiableAt (by simp)).hasFDerivAt
    have hchain := hΦ.comp_hasDerivAt θ (hasDerivAt_rotationArray' θ)
    have hkey : fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (rotationArray θ)
        (![![-Real.sin θ, Real.cos θ], ![-Real.cos θ, -Real.sin θ]] : Fin 2 → Fin 2 → ℝ) = Complex.I * f θ := by
      rw [← mulRightArrayCLM_E_sub_Fm_rotationArray, _root_.map_sub,
        ← (isArchSmoothAt_archDerivAt_apply_mul_archRealLiftAt hφ) .E g (det_of_rotationArray θ),
        ← (isArchSmoothAt_archDerivAt_apply_mul_archRealLiftAt hφ) .Fm g (det_of_rotationArray θ)]
      have h := congrFun hW (g * archRealLiftAt hw (rotationArray θ))
      simp only [archRotDerivAt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
      exact h
    rw [hkey] at hchain
    exact hchain

  have hu : ∀ θ : ℝ,
      HasDerivAt (fun θ : ℝ => Complex.exp (-((θ : ℂ) * Complex.I)) * f θ)
        (Complex.exp (-((θ : ℂ) * Complex.I)) * -(((1 : ℝ) : ℂ) * Complex.I) * f θ +
          Complex.exp (-((θ : ℂ) * Complex.I)) * (Complex.I * f θ)) θ := by
    intro θ
    exact ((((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I).neg.cexp).mul (hf' θ)
  have hconst : ∀ θ : ℝ, Complex.exp (-((θ : ℂ) * Complex.I)) * f θ = f 0 := by
    intro θ
    have h := is_const_of_deriv_eq_zero (fun θ => (hu θ).differentiableAt) (fun θ => by
      rw [(hu θ).deriv]
      push_cast
      ring) θ 0
    simpa using h
  have hf0 : f 0 = φ g := by
    simp only [hf, rotationArray_zero, archRealLiftAt_of_symm_one, mul_one]
  calc f θ = Complex.exp ((θ : ℂ) * Complex.I) * (Complex.exp (-((θ : ℂ) * Complex.I)) * f θ) := by
        rw [← mul_assoc, exp_neg_ofReal_mul_I_mul_exp, one_mul]
    _ = (⟨Real.cos θ, Real.sin θ⟩ : ℂ) * φ g := by rw [hconst θ, hf0, exp_ofReal_mul_I_eq_mk]

private theorem rotation_coe (θ : ℝ) :
    ((GL2Real.rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
  simp [GL2Real.rotation, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem exists_rotation_eq_of_mem {m : GL (Fin 2) ℝ} (hm : m ∈ rowIsometrySubgroup₀ ℝ) :
    ∃ θ : ℝ, GL2Real.rotation θ = m := by
  have hk := entries_of_mem_rowIsometrySubgroup₀ hm
  dsimp only at hk
  obtain ⟨h10, h11, hab⟩ := hk
  set a : ℝ := (m : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b : ℝ := (m : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  set z : ℂ := ⟨a, b⟩ with hz
  have hnorm : ‖z‖ = 1 := by
    have h2 : ‖z‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq, hz, Complex.normSq_mk]
      nlinarith [hab]
    nlinarith [norm_nonneg z, h2]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hcos : Real.cos (Complex.arg z) = a := by
    rw [Complex.cos_arg hz0, hnorm, div_one]
  have hsin : Real.sin (Complex.arg z) = b := by
    rw [Complex.sin_arg, hnorm, div_one]
  refine ⟨Complex.arg z, Units.ext ?_⟩
  rw [rotation_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hcos, hsin, h10, h11, ← ha, ← hb]

omit [NumberField F] in

private theorem exists_rotationAt_eq {w : InfinitePlace F} (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    ∃ θ : ℝ, rotationAt hw θ = k := by
  obtain ⟨θ, hθ⟩ := exists_rotation_eq_of_mem
    (map_mem_rowIsometrySubgroup₀_of_normPreserving (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      (k : GL (Fin 2) w.Completion) k.2)
  refine ⟨θ, Subtype.ext ?_⟩
  show glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (GL2Real.rotation θ) = (k : GL (Fin 2) w.Completion)
  rw [hθ]
  refine Units.ext ?_
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry, RingEquiv.symm_apply_apply]

private theorem isArchSmoothAt_hasArchCharacterAt₀_one_of_archRotDerivAt {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hW : archRotDerivAt hw φ = Complex.I • φ) :
    HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ := by
  intro k g
  obtain ⟨θ, rfl⟩ := exists_rotationAt_eq hw k
  rw [archWeightCharAt_one_rotationAt, ← archRealGLAt_rotation, ← archRealLiftAt_rotationArray]
  exact (isArchSmoothAt_apply_mul_archRealLiftAt_rotationArray hφ) hW θ g

private theorem isArchSmoothAt_hasArchCharacterAt₀_one_reflAt_archLowerAt {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hwt : HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ) :
    HasArchCharacterAt₀ F w (archWeightCharAt hw 1) (reflAt hw (archLowerAt hw φ)) :=
  (isArchSmoothAt_hasArchCharacterAt₀_one_of_archRotDerivAt ((isArchSmoothAt_reflAt (isArchSmoothAt_archLowerAt hφ))))
    ((isArchSmoothAt_archRotDerivAt_reflAt_archLowerAt hφ)
        ((isArchSmoothAt_archRotDerivAt_eq_of_hasArchCharacterAt₀_one hφ) hwt))

private def archT {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  reflAt hw (archLowerAt hw φ)

private theorem isArchSmoothAt_archT {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (archT hw φ) :=
  (isArchSmoothAt_reflAt (isArchSmoothAt_archLowerAt hφ))

private theorem archLowerAt_add {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) :
    archLowerAt hw (φ + ψ) = archLowerAt hw φ + archLowerAt hw ψ := by
  simp only [archLowerAt, archDerivAt_add hφ hψ]
  module

private theorem reflAt_add {w : InfinitePlace F} (hw : w.IsReal) (φ ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    reflAt hw (φ + ψ) = reflAt hw φ + reflAt hw ψ := rfl

private theorem archT_add {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) : archT hw (φ + ψ) = archT hw φ + archT hw ψ := by
  simp only [archT, archLowerAt_add hφ hψ, reflAt_add]

private theorem archT_smul {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archT hw (c • φ) = c • archT hw φ := by
  simp only [archT, archLowerAt_smul, reflAt_smul]

private theorem archRotDerivAt_smul {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archRotDerivAt hw (c • φ) = c • archRotDerivAt hw φ := by
  simp only [archRotDerivAt, archDerivAt_smul]
  exact (smul_sub c _ _).symm

private theorem isArchSmoothAt_archCasimirAt_archT {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) {lam : ℂ} (hlam : archCasimirAt hw φ = lam • φ) :
    archCasimirAt hw (archT hw φ) = lam • archT hw φ :=
  (isArchSmoothAt_archCasimirAt_reflAt_archLowerAt hφ) hlam

private theorem isArchSmoothAt_hasArchCharacterAt₀_one_archT {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hwt : HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ) :
    HasArchCharacterAt₀ F w (archWeightCharAt hw 1) (archT hw φ) :=
  (isArchSmoothAt_hasArchCharacterAt₀_one_reflAt_archLowerAt hφ) hwt

private theorem isArchSmoothAt_archT_archT {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) {lam : ℂ} (hlam : archCasimirAt hw φ = lam • φ)
    (hW : archRotDerivAt hw φ = Complex.I • φ) : archT hw (archT hw φ) = (1 - 4 * lam) • φ := by
  simp only [archT]
  rw [archLowerAt_reflAt, reflAt_reflAt, (isArchSmoothAt_archRaiseAt_archLowerAt hφ), hlam, hW,
      archRotDerivAt_smul, hW]
  funext g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(φ g)) * Complex.I_mul_I

end

end P2M.ReflectedLowering

open P2M.ReflectedLowering in

theorem solution (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (T : (AdelicGL2 (𝓞 F) F → ℂ) → AdelicGL2 (𝓞 F) F → ℂ)
    (hT : T = fun (θ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) =>
      (archDerivAt hw ArchDir.H θ - Complex.I • (archDerivAt hw ArchDir.E θ + archDerivAt hw ArchDir.Fm θ))
        (g * archRealGLAt hw UpperHalfPlane.J))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) :
    (HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ →
        archDerivAt hw ArchDir.E φ - archDerivAt hw ArchDir.Fm φ = Complex.I • φ) ∧
      IsArchSmoothAt hw (T φ) ∧
      (HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ → HasArchCharacterAt₀ F w (archWeightCharAt hw 1) (T φ)) ∧
      (∀ lam : ℂ, archCasimirAt hw φ = lam • φ → archCasimirAt hw (T φ) = lam • T φ) ∧
      (∀ lam : ℂ, archCasimirAt hw φ = lam • φ → HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ →
        T (T φ) = (1 - 4 * lam) • φ) := by
  have hT' : ∀ θ : AdelicGL2 (𝓞 F) F → ℂ, T θ = archT hw θ := fun θ => by rw [hT]; rfl
  refine ⟨fun hwt => isArchSmoothAt_archRotDerivAt_eq_of_hasArchCharacterAt₀_one hφ hwt, ?_, ?_, ?_, ?_⟩
  · rw [hT']
    exact isArchSmoothAt_archT hφ
  · intro hwt
    rw [hT']
    exact isArchSmoothAt_hasArchCharacterAt₀_one_archT hφ hwt
  · intro lam hlam
    rw [hT']
    exact isArchSmoothAt_archCasimirAt_archT hφ hlam
  · intro lam hlam hwt
    rw [hT', hT']
    exact isArchSmoothAt_archT_archT hφ hlam (isArchSmoothAt_archRotDerivAt_eq_of_hasArchCharacterAt₀_one hφ hwt)

end S_AutomorphicForm_isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul (solution)
