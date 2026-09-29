-- Prove2me | solution 1 for AutomorphicForm.mdifferentiable_cpow_mul_descent_iff_lower_eq_smul_of_isArchSmoothAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a2d98513-1e69-5e64-8d3a-e73d5ff7976a

import Definitions.Def_AutomorphicForm_ArchLowestWeight
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mdifferentiable_cpow_mul_descent_iff_lower_eq_smul_of_isArchSmoothAt

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Manifold

noncomputable section

namespace Ws23
namespace M3core

p2m_open "NumberField NumberField.InfinitePlace.NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix"
open scoped Manifold

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

def iota : GL (Fin 2) ℝ →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLInclAt F w).comp (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom)

theorem iota_apply (m : GL (Fin 2) ℝ) :
    iota hw m = adelicArchGLInclAt F w
      (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom m) := rfl

theorem iota_eq_archRealGLAt (m : GL (Fin 2) ℝ) : iota hw m = archRealGLAt hw m := by
  show _ = adelicArchGLInclAt F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m)
  rw [iota_apply]
  congr 1

theorem archFlowAt_eq_iota (d : ArchDir) (t : ℝ) : archFlowAt hw d t = iota hw (archFlowMatrix d t) := by
  rw [archFlowAt, iota_eq_archRealGLAt]

theorem iwasawaSectionGL_val (z : UpperHalfPlane) :
    (iwasawaSectionGL z : Matrix (Fin 2) (Fin 2) ℝ) = !![z.im, z.re; 0, 1] := rfl

theorem mk_im' (ζ : ℂ) (h : 0 < ζ.im) : (UpperHalfPlane.mk ζ h).im = ζ.im := rfl

theorem mk_re' (ζ : ℂ) (h : 0 < ζ.im) : (UpperHalfPlane.mk ζ h).re = ζ.re := rfl

theorem im_coe_add_ofReal (z : UpperHalfPlane) (a : ℝ) : ((z : ℂ) + (a : ℂ)).im = z.im := by
  rw [Complex.add_im, Complex.ofReal_im, add_zero]; rfl

theorem im_ofReal_add_ofReal_mul_I (a b : ℝ) : ((a : ℂ) + (b : ℂ) * Complex.I).im = b := by
  simp

theorem re_ofReal_add_ofReal_mul_I (a b : ℝ) : ((a : ℂ) + (b : ℂ) * Complex.I).re = a := by
  simp

theorem iwasawaSectionGL_I : iwasawaSectionGL UpperHalfPlane.I = 1 := by
  apply Units.ext
  rw [iwasawaSectionGL_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UpperHalfPlane.I_im, UpperHalfPlane.I_re]

def ptE (z : UpperHalfPlane) (t : ℝ) : UpperHalfPlane :=
  ⟨(z : ℂ) + (t * z.im : ℝ), by rw [im_coe_add_ofReal]; exact z.im_pos⟩

theorem ptE_coe (z : UpperHalfPlane) (t : ℝ) : (ptE z t : ℂ) = (z : ℂ) + (t * z.im : ℝ) := rfl

theorem ptE_im (z : UpperHalfPlane) (t : ℝ) : (ptE z t).im = z.im := im_coe_add_ofReal z _

theorem ptE_re (z : UpperHalfPlane) (t : ℝ) : (ptE z t).re = z.re + t * z.im := by
  show ((z : ℂ) + ((t * z.im : ℝ) : ℂ)).re = _
  rw [Complex.add_re, Complex.ofReal_re]
  rfl

def ptH (z : UpperHalfPlane) (τ : ℝ) : UpperHalfPlane :=
  ⟨(z.re : ℂ) + (z.im * Real.exp (2 * τ) : ℝ) * Complex.I,
    by rw [im_ofReal_add_ofReal_mul_I]; exact mul_pos z.im_pos (Real.exp_pos _)⟩

theorem ptH_coe (z : UpperHalfPlane) (τ : ℝ) :
    (ptH z τ : ℂ) = (z.re : ℂ) + (z.im * Real.exp (2 * τ) : ℝ) * Complex.I := rfl

theorem ptH_im (z : UpperHalfPlane) (τ : ℝ) : (ptH z τ).im = z.im * Real.exp (2 * τ) :=
  im_ofReal_add_ofReal_mul_I _ _

theorem ptH_re (z : UpperHalfPlane) (τ : ℝ) : (ptH z τ).re = z.re :=
  re_ofReal_add_ofReal_mul_I _ _

theorem iwasawaSectionGL_mul_unipotentGL2 (z : UpperHalfPlane) (t : ℝ) :
    iwasawaSectionGL z * unipotentGL2 t = iwasawaSectionGL (ptE z t) := by
  apply Units.ext
  rw [Units.val_mul, iwasawaSectionGL_val, iwasawaSectionGL_val, unipotentGL2_coe, ptE_re, ptE_im]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def expUnit (s : ℝ) : ℝˣ :=
  ⟨Real.exp s, Real.exp (-s), by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero],
    by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]⟩

theorem expUnit_val (s : ℝ) : ((expUnit s : ℝˣ) : ℝ) = Real.exp s := rfl

theorem iwasawaSectionGL_mul_splitTorusGL2 (z : UpperHalfPlane) (τ : ℝ) :
    iwasawaSectionGL z * splitTorusGL2 τ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (expUnit (-τ)) * iwasawaSectionGL (ptH z τ) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, iwasawaSectionGL_val, iwasawaSectionGL_val, splitTorusGL2_coe,
    ptH_re, ptH_im]
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (expUnit (-τ)) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = Matrix.scalar (Fin 2) (Real.exp (-τ)) := rfl
  rw [hs]
  have h2 : Real.exp (2 * τ) = Real.exp τ * Real.exp τ := by rw [two_mul, Real.exp_add]
  have hn : Real.exp (-τ) * Real.exp τ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply]
  all_goals first
    | (rw [h2]
       calc (z.im : ℝ) * Real.exp τ = (Real.exp (-τ) * Real.exp τ) * (z.im * Real.exp τ) := by rw [hn, one_mul]
         _ = _ := by ring)
    | ring

theorem adelicArchGLInclAt_val_apply (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      (archMatrixUpdate F w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j,
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) :=
  rfl

theorem centralScalar_val_apply (c : (AdeleRing (𝓞 F) F)ˣ) (i j : Fin 2) :
    ((centralScalar (𝓞 F) F c : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      if i = j then (c : AdeleRing (𝓞 F) F) else 0 := by
  show (Matrix.scalar (Fin 2) (c : AdeleRing (𝓞 F) F)) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem iota_scalar (t : ℝˣ) :
    iota hw (Matrix.GeneralLinearGroup.scalar (Fin 2) t) =
      centralScalar (𝓞 F) F (NumberField.AdelicVolume.archCentralUnit F w
        (Units.map ((ringEquivRealOfIsReal hw).symm.toRingHom : ℝ →* w.Completion) t)) := by
  classical
  rw [iota_apply]
  apply Units.ext
  ext i j
  rw [adelicArchGLInclAt_val_apply, centralScalar_val_apply]
  have hM : ((Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
      (Matrix.GeneralLinearGroup.scalar (Fin 2) t) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j =
      if i = j then (ringEquivRealOfIsReal hw).symm (t : ℝ) else 0 := by
    show (ringEquivRealOfIsReal hw).symm.toRingHom ((Matrix.scalar (Fin 2) (t : ℝ)) i j) = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  refine Prod.ext (funext fun v => ?_) ?_
  · show archMatrixUpdate F w _ i j v = _
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self, hM]
      split_ifs with hij
      · show _ = Function.update (1 : InfiniteAdeleRing F) v _ v
        rw [Function.update_self]; rfl
      · rfl
    · rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv]
      split_ifs with hij
      · subst hij
        rw [Matrix.one_apply_eq]
        show (1 : v.Completion) = Function.update (1 : InfiniteAdeleRing F) w _ v
        rw [Function.update_of_ne hv]; rfl
      · rw [Matrix.one_apply_ne hij]; rfl
  · show (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j = _
    split_ifs with hij
    · subst hij; rw [Matrix.one_apply_eq]; rfl
    · rw [Matrix.one_apply_ne hij]; rfl

theorem iota_scalar_mul_comm (t : ℝˣ) (g : AdelicGL2 (𝓞 F) F) :
    iota hw (Matrix.GeneralLinearGroup.scalar (Fin 2) t) * g =
      g * iota hw (Matrix.GeneralLinearGroup.scalar (Fin 2) t) := by
  rw [iota_scalar]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

theorem archRealGLAt_eq_archRealLiftAt (M : GL (Fin 2) ℝ) :
    archRealGLAt hw M = archRealLiftAt hw (Matrix.of.symm (M : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hdet : (Matrix.of (Matrix.of.symm (M : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  rw [archRealLiftAt_of_det_ne_zero hw hdet]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

def slice (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ → ℂ :=
  fun ζ => φ (g * iota hw (iwasawaSectionGL (UpperHalfPlane.ofComplex ζ)))

theorem slice_apply_coe (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (z : UpperHalfPlane) :
    slice hw φ g (z : ℂ) = φ (g * iota hw (iwasawaSectionGL z)) := by
  show φ (g * iota hw (iwasawaSectionGL (UpperHalfPlane.ofComplex (z : ℂ)))) = _
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos z.im_pos]

def sliceArr (ζ : ℂ) : Fin 2 → Fin 2 → ℝ := Matrix.of.symm !![ζ.im, ζ.re; 0, 1]

theorem sliceArr_apply (ζ : ℂ) (i j : Fin 2) : sliceArr ζ i j = !![ζ.im, ζ.re; 0, 1] i j := rfl

theorem contDiff_sliceArr : ContDiff ℝ (⊤ : ℕ∞) sliceArr := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [sliceArr_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first
      | exact contDiff_const
      | exact Complex.imCLM.contDiff
      | exact Complex.reCLM.contDiff

theorem det_of_sliceArr (ζ : ℂ) : (Matrix.of (sliceArr ζ)).det = ζ.im := by
  rw [sliceArr, Equiv.apply_symm_apply, Matrix.det_fin_two_of]; ring

theorem slice_eq_chart_of_im_pos {ζ : ℂ} (hζ : 0 < ζ.im) (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    slice hw φ g ζ = φ (g * archRealLiftAt hw (sliceArr ζ)) := by
  show φ (g * iota hw (iwasawaSectionGL (UpperHalfPlane.ofComplex ζ))) = _
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hζ, iota_eq_archRealGLAt, archRealGLAt_eq_archRealLiftAt]
  rfl

omit hw in
theorem isOpen_im_pos : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im

theorem contDiffAt_slice {φ : AdelicGL2 (𝓞 F) F → ℂ} (hs : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F)
    {ζ : ℂ} (hζ : 0 < ζ.im) : ContDiffAt ℝ (⊤ : ℕ∞) (slice hw φ g) ζ := by
  have hmem : sliceArr ζ ∈ {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0} := by
    show (Matrix.of (sliceArr ζ)).det ≠ 0
    rw [det_of_sliceArr]
    exact hζ.ne'
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e)) (sliceArr ζ) :=
    (hs g).contDiffAt (isOpen_setOf_det_ne_zero.mem_nhds hmem)
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun ζ' => φ (g * archRealLiftAt hw (sliceArr ζ'))) ζ :=
    h1.comp ζ contDiff_sliceArr.contDiffAt
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_im_pos.mem_nhds hζ] with ζ' hζ'
  exact slice_eq_chart_of_im_pos hw hζ' φ g

theorem hasFDerivAt_slice {φ : AdelicGL2 (𝓞 F) F → ℂ} (hs : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F)
    {ζ : ℂ} (hζ : 0 < ζ.im) : HasFDerivAt (slice hw φ g) (fderiv ℝ (slice hw φ g) ζ) ζ :=
  ((contDiffAt_slice hw hs g hζ).differentiableAt (by simp)).hasFDerivAt

omit hw in
theorem clm_apply_ofReal_mul (L : ℂ →L[ℝ] ℂ) (a : ℝ) (v : ℂ) : L ((a : ℂ) * v) = (a : ℂ) * L v := by
  rw [← Complex.real_smul, map_smul, Complex.real_smul]

theorem archDerivAt_E_slice {φ : AdelicGL2 (𝓞 F) F → ℂ} (hs : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F)
    (z : UpperHalfPlane) :
    archDerivAt hw .E φ (g * iota hw (iwasawaSectionGL z)) =
      (z.im : ℂ) * fderiv ℝ (slice hw φ g) (z : ℂ) 1 := by
  have hfun : (fun t : ℝ => φ (g * iota hw (iwasawaSectionGL z) * archFlowAt hw .E t)) =
      fun t : ℝ => slice hw φ g ((z : ℂ) + (t * z.im : ℝ)) := by
    funext t
    rw [archFlowAt_eq_iota, mul_assoc, ← map_mul, show archFlowMatrix .E t = unipotentGL2 t from rfl,
      iwasawaSectionGL_mul_unipotentGL2, slice,
      UpperHalfPlane.ofComplex_apply_of_im_pos (by rw [im_coe_add_ofReal]; exact z.im_pos)]
    rfl
  have hγ : HasDerivAt (fun t : ℝ => (z : ℂ) + (t * z.im : ℝ)) ((1 * z.im : ℝ) : ℂ) 0 :=
    (((hasDerivAt_id (0 : ℝ)).mul_const (z.im : ℝ)).ofReal_comp).const_add _
  have h0 : (z : ℂ) = (z : ℂ) + ((0 : ℝ) * z.im : ℝ) := by simp
  have hcomp := (hasFDerivAt_slice hw hs g z.im_pos).comp_hasDerivAt_of_eq (0 : ℝ) hγ h0
  show deriv (fun t : ℝ => φ (g * iota hw (iwasawaSectionGL z) * archFlowAt hw .E t)) 0 = _
  rw [hfun]
  have hd : deriv (fun t : ℝ => slice hw φ g ((z : ℂ) + (t * z.im : ℝ))) 0 =
      fderiv ℝ (slice hw φ g) (z : ℂ) ((1 * z.im : ℝ) : ℂ) := by
    simpa only [Function.comp_def] using hcomp.deriv
  rw [hd, one_mul, show ((z.im : ℝ) : ℂ) = (z.im : ℂ) * 1 from (mul_one _).symm, clm_apply_ofReal_mul, mul_one]

omit hw in
theorem cpow_ofReal_exp (s : ℝ) (c : ℂ) : ((Real.exp s : ℝ) : ℂ) ^ c = Complex.exp (s * c) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos s).ne'), ← Complex.ofReal_log (Real.exp_pos s).le,
    Real.log_exp]

theorem archDerivAt_H_slice {φ : AdelicGL2 (𝓞 F) F → ℂ} (hs : IsArchSmoothAt hw φ) {c₀ : ℂ}
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g)
    (g : AdelicGL2 (𝓞 F) F) (z : UpperHalfPlane) :
    archDerivAt hw .H φ (g * iota hw (iwasawaSectionGL z)) =
      -c₀ * φ (g * iota hw (iwasawaSectionGL z)) + 2 * (z.im : ℂ) * fderiv ℝ (slice hw φ g) (z : ℂ) Complex.I := by

  have hγim : ∀ τ : ℝ, 0 < ((z.re : ℂ) + (z.im * Real.exp (2 * τ) : ℝ) * Complex.I).im := fun τ => by
    rw [im_ofReal_add_ofReal_mul_I]; exact mul_pos z.im_pos (Real.exp_pos _)
  have hfun : (fun τ : ℝ => φ (g * iota hw (iwasawaSectionGL z) * archFlowAt hw .H τ)) =
      fun τ : ℝ => Complex.exp ((-τ : ℝ) * c₀) *
        slice hw φ g ((z.re : ℂ) + (z.im * Real.exp (2 * τ) : ℝ) * Complex.I) := by
    funext τ
    rw [archFlowAt_eq_iota, mul_assoc, ← map_mul, show archFlowMatrix .H τ = splitTorusGL2 τ from rfl,
      iwasawaSectionGL_mul_splitTorusGL2, map_mul, ← mul_assoc, ← iota_scalar_mul_comm, mul_assoc, iota_apply,
      hc (expUnit (-τ)) (Real.exp_pos _) _, expUnit_val, cpow_ofReal_exp, slice,
      UpperHalfPlane.ofComplex_apply_of_im_pos (hγim τ)]
    rfl

  have h1 : HasDerivAt (fun τ : ℝ => Complex.exp ((-τ : ℝ) * c₀)) (-c₀) 0 := by
    have h := ((hasDerivAt_neg (0 : ℝ)).ofReal_comp.mul_const c₀).cexp
    have hval : Complex.exp (((-0 : ℝ) : ℝ) * c₀) * (((-1 : ℝ) : ℂ) * c₀) = -c₀ := by simp
    rw [hval] at h
    exact h

  have he2 : HasDerivAt (fun τ : ℝ => Real.exp (2 * τ)) (Real.exp (2 * 0) * (2 * 1)) 0 :=
    (Real.hasDerivAt_exp (2 * 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_mul 2)
  have he : HasDerivAt (fun τ : ℝ => (z.im : ℝ) * Real.exp (2 * τ)) (z.im * (Real.exp (2 * 0) * (2 * 1))) 0 :=
    he2.const_mul _
  have h2 : HasDerivAt (fun τ : ℝ => (z.re : ℂ) + (z.im * Real.exp (2 * τ) : ℝ) * Complex.I)
      (((z.im * (Real.exp (2 * 0) * (2 * 1)) : ℝ) : ℂ) * Complex.I) 0 :=
    (he.ofReal_comp.mul_const Complex.I).const_add _
  have hγ0 : (z : ℂ) = (z.re : ℂ) + (z.im * Real.exp (2 * 0) : ℝ) * Complex.I := by
    rw [mul_zero, Real.exp_zero, mul_one]
    exact (Complex.re_add_im (z : ℂ)).symm
  have h3 : HasDerivAt (fun τ : ℝ => slice hw φ g ((z.re : ℂ) + (z.im * Real.exp (2 * τ) : ℝ) * Complex.I))
      (fderiv ℝ (slice hw φ g) (z : ℂ) ((((z.im : ℝ) * (Real.exp (2 * 0) * (2 * 1)) : ℝ) : ℂ) * Complex.I)) 0 := by
    have := (hasFDerivAt_slice hw hs g z.im_pos).comp_hasDerivAt_of_eq (0 : ℝ) h2 hγ0
    simpa only [Function.comp_def] using this
  have h4 : HasDerivAt (fun τ : ℝ => Complex.exp ((-τ : ℝ) * c₀) *
      slice hw φ g ((z.re : ℂ) + (z.im * Real.exp (2 * τ) : ℝ) * Complex.I))
      (-c₀ * slice hw φ g ((z.re : ℂ) + (z.im * Real.exp (2 * 0) : ℝ) * Complex.I) +
        Complex.exp (((-0 : ℝ) : ℝ) * c₀) *
          fderiv ℝ (slice hw φ g) (z : ℂ) ((((z.im : ℝ) * (Real.exp (2 * 0) * (2 * 1)) : ℝ) : ℂ) * Complex.I)) 0 :=
    h1.mul h3
  show deriv (fun τ : ℝ => φ (g * iota hw (iwasawaSectionGL z) * archFlowAt hw .H τ)) 0 = _
  rw [hfun, h4.deriv]
  have hL : fderiv ℝ (slice hw φ g) (z : ℂ) ((((z.im : ℝ) * (Real.exp (2 * 0) * (2 * 1)) : ℝ) : ℂ) * Complex.I) =
      2 * (z.im : ℂ) * fderiv ℝ (slice hw φ g) (z : ℂ) Complex.I := by
    rw [clm_apply_ofReal_mul, mul_zero, Real.exp_zero, one_mul, mul_one]
    push_cast
    ring
  rw [hL, ← hγ0, slice_apply_coe]
  simp only [neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]

omit hw

theorem differentiableAt_iff_of_hasFDerivAt {f : ℂ → ℂ} {ζ : ℂ} {L : ℂ →L[ℝ] ℂ} (hf : HasFDerivAt f L ζ) :
    DifferentiableAt ℂ f ζ ↔ L Complex.I = Complex.I * L 1 := by
  rw [differentiableAt_iff_restrictScalars ℝ hf.differentiableAt, hf.fderiv]
  constructor
  · rintro ⟨g', hg'⟩
    have h1 : L 1 = g' 1 := by rw [← hg']; rfl
    have hI : L Complex.I = g' Complex.I := by rw [← hg']; rfl
    rw [h1, hI, ← smul_eq_mul Complex.I (g' 1), ← map_smul, smul_eq_mul, mul_one]
  · intro h
    refine ⟨(L 1) • ContinuousLinearMap.id ℂ ℂ, ?_⟩
    ext v
    show L 1 * v = L v
    conv_rhs => rw [← Complex.re_add_im v]
    rw [map_add, clm_apply_ofReal_mul, h, show ((v.re : ℝ) : ℂ) = (v.re : ℂ) * 1 from (mul_one _).symm,
      clm_apply_ofReal_mul]
    conv_lhs => rw [← Complex.re_add_im v]
    ring

theorem hasDerivAt_ofReal_cpow {s : ℝ} (hs : 0 < s) (σ : ℂ) :
    HasDerivAt (fun r : ℝ => ((r : ℝ) : ℂ) ^ σ) (σ * ((s : ℂ) ^ σ / (s : ℂ))) s := by
  have h : HasDerivAt (fun r : ℝ => Complex.exp ((Real.log r : ℂ) * σ))
      (Complex.exp ((Real.log s : ℂ) * σ) * ((s⁻¹ : ℝ) * σ)) s :=
    ((Real.hasDerivAt_log hs.ne').ofReal_comp.mul_const σ).cexp
  have heq : (fun r : ℝ => ((r : ℝ) : ℂ) ^ σ) =ᶠ[nhds s] fun r => Complex.exp ((Real.log r : ℂ) * σ) := by
    filter_upwards [lt_mem_nhds hs] with r hr
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← Complex.ofReal_log hr.le]
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [Complex.ofReal_log hs.le, ← Complex.cpow_def_of_ne_zero (by exact_mod_cast hs.ne')]
  push_cast
  field_simp

theorem hasFDerivAt_im_cpow {ζ : ℂ} (hζ : 0 < ζ.im) (σ : ℂ) :
    ∃ Q' : ℂ →L[ℝ] ℂ, HasFDerivAt (fun ζ' : ℂ => ((ζ'.im : ℝ) : ℂ) ^ σ) Q' ζ ∧ Q' 1 = 0 ∧
      Q' Complex.I = σ * (((ζ.im : ℝ) : ℂ) ^ σ / ((ζ.im : ℝ) : ℂ)) := by
  have h := (hasDerivAt_ofReal_cpow hζ σ).hasFDerivAt.comp ζ Complex.imCLM.hasFDerivAt
  refine ⟨_, h, ?_, ?_⟩ <;>
    simp [ContinuousLinearMap.comp_apply]

theorem key {w : InfinitePlace F} (hw : w.IsReal) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hs : IsArchSmoothAt hw φ)
    (m c₀ σ : ℂ) (hm : archDerivAt hw .E φ - archDerivAt hw .Fm φ = m • φ)
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g)
    (g : AdelicGL2 (𝓞 F) F) (z : UpperHalfPlane) :
    DifferentiableAt ℂ ((fun z' : UpperHalfPlane =>
        (((z'.im : ℝ) : ℂ) ^ σ) * φ (g * iota hw (iwasawaSectionGL z'))) ∘ UpperHalfPlane.ofComplex) (z : ℂ) ↔
      (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ))
          (g * iota hw (iwasawaSectionGL z)) =
        (Complex.I * m - c₀ - 2 * σ) * φ (g * iota hw (iwasawaSectionGL z)) := by

  set G : ℂ → ℂ := fun ζ => (((ζ.im : ℝ) : ℂ) ^ σ) * slice hw φ g ζ with hG
  have hev : ((fun z' : UpperHalfPlane => (((z'.im : ℝ) : ℂ) ^ σ) * φ (g * iota hw (iwasawaSectionGL z'))) ∘
      UpperHalfPlane.ofComplex) =ᶠ[nhds (z : ℂ)] G := by
    filter_upwards [isOpen_im_pos.mem_nhds (z.im_pos : 0 < (z : ℂ).im)] with ζ hζ
    show (((UpperHalfPlane.ofComplex ζ).im : ℝ) : ℂ) ^ σ * φ (g * iota hw (iwasawaSectionGL (UpperHalfPlane.ofComplex ζ))) =
      (((ζ.im : ℝ) : ℂ) ^ σ) * φ (g * iota hw (iwasawaSectionGL (UpperHalfPlane.ofComplex ζ)))
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hζ]
    rfl
  rw [hev.differentiableAt_iff]

  obtain ⟨Q', hQ', hQ'1, hQ'I⟩ := hasFDerivAt_im_cpow (z.im_pos : 0 < (z : ℂ).im) σ
  have hsl := hasFDerivAt_slice hw hs g (z.im_pos : 0 < (z : ℂ).im)
  have hGd : HasFDerivAt G ((((((z : ℂ).im : ℝ) : ℂ) ^ σ) • fderiv ℝ (slice hw φ g) (z : ℂ)) +
      (slice hw φ g (z : ℂ)) • Q') (z : ℂ) := hQ'.mul hsl
  rw [differentiableAt_iff_of_hasFDerivAt hGd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hQ'1, hQ'I, mul_zero,
    add_zero]

  have hE := archDerivAt_E_slice hw hs g z
  have hH := archDerivAt_H_slice hw hs hc g z
  have hFm : archDerivAt hw .Fm φ (g * iota hw (iwasawaSectionGL z)) =
      archDerivAt hw .E φ (g * iota hw (iwasawaSectionGL z)) - m * φ (g * iota hw (iwasawaSectionGL z)) := by
    have := congrFun hm (g * iota hw (iwasawaSectionGL z))
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination -this
  rw [slice_apply_coe]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hFm, hE, hH, UpperHalfPlane.coe_im]

  set y : ℂ := ((z.im : ℝ) : ℂ) with hy
  set h : ℂ := φ (g * iota hw (iwasawaSectionGL z)) with hh
  set L1 : ℂ := fderiv ℝ (slice hw φ g) (z : ℂ) 1 with hL1
  set LI : ℂ := fderiv ℝ (slice hw φ g) (z : ℂ) Complex.I with hLI
  have hy0 : y ≠ 0 := by rw [hy]; exact_mod_cast z.im_pos.ne'
  have hP : y ^ σ = y ^ (σ - 1) * y := by
    rw [Complex.cpow_sub _ _ hy0, Complex.cpow_one, div_mul_cancel₀ _ hy0]
  rw [hP, mul_div_assoc, div_self hy0, mul_one]
  have hP0 : y ^ (σ - 1) ≠ 0 := fun h0 => hy0 (Complex.cpow_eq_zero_iff _ _ |>.mp h0).1
  constructor
  · intro hCR

    have h' : y ^ (σ - 1) * (y * (LI - Complex.I * L1) + σ * h) = 0 := by linear_combination hCR
    have h'' : y * (LI - Complex.I * L1) + σ * h = 0 := (mul_eq_zero.mp h').resolve_left hP0
    linear_combination 2 * h''
  · intro hMaass
    have h'' : y * (LI - Complex.I * L1) + σ * h = 0 := by linear_combination hMaass / 2
    linear_combination y ^ (σ - 1) * h''

theorem main {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hs : IsArchSmoothAt hw φ) (m c₀ σ : ℂ)
    (hm : archDerivAt hw .E φ - archDerivAt hw .Fm φ = m • φ)
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g) :
    (∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * φ (g * adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (iwasawaSectionGL z)))) ↔
      archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) =
        (Complex.I * m - c₀ - 2 * σ) • φ := by
  have hι : ∀ mm : GL (Fin 2) ℝ, adelicArchGLInclAt F w
      (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom mm) =
        iota hw mm := fun _ => rfl
  simp only [hι]
  constructor
  · intro hhol
    funext x
    have hx : x = x * iota hw (iwasawaSectionGL UpperHalfPlane.I) := by
      rw [iwasawaSectionGL_I, map_one, mul_one]
    have hk := (key hw hs m c₀ σ hm hc x UpperHalfPlane.I).mp
      (UpperHalfPlane.mdifferentiableAt_iff.mp (hhol x UpperHalfPlane.I))
    rw [← hx] at hk
    simpa only [Pi.smul_apply, smul_eq_mul] using hk
  · intro hL g
    rw [UpperHalfPlane.mdifferentiable_iff]
    intro ζ hζ
    have hpt := congrFun hL (g * iota hw (iwasawaSectionGL (UpperHalfPlane.mk ζ hζ)))
    simp only [Pi.smul_apply, smul_eq_mul] at hpt
    exact ((key hw hs m c₀ σ hm hc g (UpperHalfPlane.mk ζ hζ)).mpr hpt).differentiableWithinAt

end Ws23.M3core

end

open _root_.NumberField _root_.NumberField.InfinitePlace.NumberField AutomorphicForm _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion in
open scoped Manifold in
theorem solution
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hs : IsArchSmoothAt hw φ) (m c₀ σ : ℂ)
    (hm : archDerivAt hw .E φ - archDerivAt hw .Fm φ = m • φ)
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g) :
    (∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * φ (g * adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (iwasawaSectionGL z)))) ↔
      archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) =
        (Complex.I * m - c₀ - 2 * σ) • φ :=
  Ws23.M3core.main hw φ hs m c₀ σ hm hc

end S_AutomorphicForm_mdifferentiable_cpow_mul_descent_iff_lower_eq_smul_of_isArchSmoothAt
end P2MW
export P2MW.S_AutomorphicForm_mdifferentiable_cpow_mul_descent_iff_lower_eq_smul_of_isArchSmoothAt (solution)
