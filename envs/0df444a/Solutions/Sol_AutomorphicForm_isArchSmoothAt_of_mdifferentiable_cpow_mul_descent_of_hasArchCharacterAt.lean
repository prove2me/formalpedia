-- Prove2me | solution 1 for AutomorphicForm.isArchSmoothAt_of_mdifferentiable_cpow_mul_descent_of_hasArchCharacterAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c4e313ad-501c-552d-8b23-9d477239971a

import Definitions.Def_AutomorphicForm_ArchLowestWeight
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isArchSmoothAt_of_mdifferentiable_cpow_mul_descent_of_hasArchCharacterAt

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Manifold

noncomputable section

namespace Ws23
namespace M4

p2m_open "NumberField NumberField.InfinitePlace.NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix"
open scoped Manifold

section Coordinates

def rho (e : Fin 2 → Fin 2 → ℝ) : ℝ := e 1 0 ^ 2 + e 1 1 ^ 2

def tE (e : Fin 2 → Fin 2 → ℝ) : ℝ := Real.sqrt (rho e)

def detE (e : Fin 2 → Fin 2 → ℝ) : ℝ := e 0 0 * e 1 1 - e 0 1 * e 1 0

def xE (e : Fin 2 → Fin 2 → ℝ) : ℝ := (e 0 0 * e 1 0 + e 0 1 * e 1 1) / rho e

def yE (e : Fin 2 → Fin 2 → ℝ) : ℝ := detE e / rho e

def rotM (e : Fin 2 → Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![e 1 1 / tE e, -(e 1 0) / tE e; e 1 0 / tE e, e 1 1 / tE e]

theorem detE_eq (e : Fin 2 → Fin 2 → ℝ) : (Matrix.of e).det = detE e := by
  rw [Matrix.det_fin_two]; rfl

theorem rho_pos {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) : 0 < rho e := by
  have h' : e 0 0 * e 1 1 - e 0 1 * e 1 0 ≠ 0 := by rwa [detE_eq] at h
  unfold rho
  by_contra hle
  push Not at hle
  clear h
  have h := h'
  have h1 : e 1 0 ^ 2 = 0 := by nlinarith [sq_nonneg (e 1 0), sq_nonneg (e 1 1)]
  have h2 : e 1 1 ^ 2 = 0 := by nlinarith [sq_nonneg (e 1 0), sq_nonneg (e 1 1)]
  rw [sq_eq_zero_iff] at h1 h2
  apply h
  rw [h1, h2, mul_zero, mul_zero, sub_zero]

theorem rho_ne_zero {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) : rho e ≠ 0 := (rho_pos h).ne'

theorem tE_pos {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) : 0 < tE e := Real.sqrt_pos.mpr (rho_pos h)

theorem tE_ne_zero {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) : tE e ≠ 0 := (tE_pos h).ne'

theorem tE_sq {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) : tE e ^ 2 = rho e :=
  Real.sq_sqrt (rho_pos h).le

theorem yE_pos {e : Fin 2 → Fin 2 → ℝ} (h : 0 < (Matrix.of e).det) : 0 < yE e := by
  unfold yE
  exact div_pos (by rwa [← detE_eq]) (rho_pos h.ne')

theorem det_rotM {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) : (rotM e).det = 1 := by
  have ht := tE_ne_zero h
  have hsq := tE_sq h
  unfold rotM
  rw [Matrix.det_fin_two_of]
  unfold rho at hsq
  field_simp
  nlinarith [hsq]

theorem isRowIsometry_rotM {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) (hdet : (rotM e).det ≠ 0) :
    WindowedSiegel.IsRowIsometry (Matrix.GeneralLinearGroup.mkOfDetNeZero (rotM e) hdet) := by
  have ht := tE_ne_zero h
  have hsq := tE_sq h
  unfold rho at hsq
  constructor
  · show ‖(rotM e).det‖ = 1
    rw [det_rotM h, norm_one]
  · intro x y
    show ‖x * rotM e 0 0 + y * rotM e 1 0‖ ^ 2 + ‖x * rotM e 0 1 + y * rotM e 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2
    simp only [rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    field_simp
    nlinarith [hsq]

def rotGL {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) : rowIsometrySubgroup₀ ℝ :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (rotM e) (by rw [det_rotM h]; exact one_ne_zero),
    (mem_rowIsometrySubgroup₀_iff ℝ).mpr ⟨det_rotM h, isRowIsometry_rotM h _⟩⟩

theorem rotGL_val {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) :
    ((rotGL h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM e := rfl

def tUnit {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) : ℝˣ := Units.mk0 (tE e) (tE_ne_zero h)

def zE {e : Fin 2 → Fin 2 → ℝ} (h : 0 < (Matrix.of e).det) : UpperHalfPlane :=
  ⟨(xE e : ℂ) + (yE e : ℂ) * Complex.I, by simpa using yE_pos h⟩

theorem zE_im {e : Fin 2 → Fin 2 → ℝ} (h : 0 < (Matrix.of e).det) : (zE h).im = yE e := by
  show ((xE e : ℂ) + (yE e : ℂ) * Complex.I).im = yE e
  simp

theorem zE_re {e : Fin 2 → Fin 2 → ℝ} (h : 0 < (Matrix.of e).det) : (zE h).re = xE e := by
  show ((xE e : ℂ) + (yE e : ℂ) * Complex.I).re = xE e
  simp

theorem iwasawa_decomposition {e : Fin 2 → Fin 2 → ℝ} (h : 0 < (Matrix.of e).det) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h.ne' =
      iwasawaSectionGL (zE h) * Matrix.GeneralLinearGroup.scalar (Fin 2) (tUnit h.ne') *
        (rotGL h.ne' : GL (Fin 2) ℝ) := by
  have hρ := rho_ne_zero h.ne'
  have ht := tE_ne_zero h.ne'
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, rotGL_val]
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (tUnit h.ne') : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.scalar (Fin 2) (tE e) := rfl
  have hi : ((iwasawaSectionGL (zE h) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![yE e, xE e; 0, 1] := by
    show !![(zE h).im, (zE h).re; 0, 1] = _
    rw [zE_im, zE_re]
  rw [hs, hi]
  have hρ1 : e 1 0 ^ 2 + e 1 1 ^ 2 ≠ 0 := hρ
  have hρ2 : e 1 1 ^ 2 + e 1 0 ^ 2 ≠ 0 := by rwa [add_comm]
  show Matrix.of e = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, rotM, Matrix.scalar_apply, xE, yE, detE, rho] <;>
    field_simp <;> ring

end Coordinates

section Value

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

omit [NumberField F] in
theorem norm_symm_ringEquivRealOfIsReal (x : ℝ) : ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  rw [← norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x), RingEquiv.apply_symm_apply]

def kappa (r : rowIsometrySubgroup₀ ℝ) : rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm (norm_symm_ringEquivRealOfIsReal hw) r

theorem adelicArchGLInclAt_kappa (r : rowIsometrySubgroup₀ ℝ) :
    adelicArchGLInclAt F w (kappa hw r : GL (Fin 2) w.Completion) = iota hw (r : GL (Fin 2) ℝ) := by
  rw [iota_eq_archRealGLAt]
  rfl

theorem archWeightCharAt_kappa (k : ℤ) (r : rowIsometrySubgroup₀ ℝ) :
    ((archWeightCharAt hw k (kappa hw r) : ℂˣ) : ℂ) = firstRowℂ (r : GL (Fin 2) ℝ) ^ k := by
  have hr : rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) (kappa hw r) = r := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    show ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm ((r : GL (Fin 2) ℝ) i j)) = _
    exact RingEquiv.apply_symm_apply _ _
  show (((zpowGroupHom k) (archWeightOneℝ (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
    (norm_ringEquivRealOfIsReal hw) (kappa hw r))) : ℂˣ) : ℂ) = _
  rw [hr, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val]
  rfl

theorem apply_archRealLiftAt_of_det_pos (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : ℤ) (c₀ : ℂ)
    (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ)
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g)
    (g : AdelicGL2 (𝓞 F) F) {e : Fin 2 → Fin 2 → ℝ} (h : 0 < (Matrix.of e).det) :
    φ (g * archRealLiftAt hw e) =
      firstRowℂ ((rotGL h.ne' : rowIsometrySubgroup₀ ℝ) : GL (Fin 2) ℝ) ^ k * (((tE e : ℝ) : ℂ) ^ c₀) *
        φ (g * iota hw (iwasawaSectionGL (zE h))) := by
  rw [archRealLiftAt_of_det_ne_zero hw h.ne', ← iota_eq_archRealGLAt, iwasawa_decomposition h, map_mul, map_mul,
    ← mul_assoc, ← mul_assoc, ← adelicArchGLInclAt_kappa hw, hk (kappa hw (rotGL h.ne')) _,
    archWeightCharAt_kappa, ← iota_scalar_mul_comm, iota_apply,
    hc (tUnit h.ne') (tE_pos h.ne') _, ← mul_assoc]
  rfl

theorem firstRowℂ_rotGL {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) :
    firstRowℂ ((rotGL h : rowIsometrySubgroup₀ ℝ) : GL (Fin 2) ℝ) =
      ((e 1 1 / tE e : ℝ) : ℂ) + ((-(e 1 0) / tE e : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · show rotM e 0 0 = _
    simp [rotM]
  · show rotM e 0 1 = _
    simp [rotM]

end Value

section Smooth

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

omit hw in
theorem contDiff_entry (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 2 → Fin 2 → ℝ => e i j :=
  (contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 2 → ℝ) i)

omit hw in
theorem contDiff_rho : ContDiff ℝ (⊤ : ℕ∞) rho :=
  ((contDiff_entry 1 0).pow 2).add ((contDiff_entry 1 1).pow 2)

omit hw in
theorem contDiff_detE : ContDiff ℝ (⊤ : ℕ∞) detE :=
  ((contDiff_entry 0 0).mul (contDiff_entry 1 1)).sub ((contDiff_entry 0 1).mul (contDiff_entry 1 0))

omit hw in
theorem contDiffAt_xE {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) xE e :=
  ((((contDiff_entry 0 0).mul (contDiff_entry 1 0)).add ((contDiff_entry 0 1).mul (contDiff_entry 1 1))).contDiffAt).div
    contDiff_rho.contDiffAt (rho_ne_zero h)

omit hw in
theorem contDiffAt_yE {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) yE e :=
  contDiff_detE.contDiffAt.div contDiff_rho.contDiffAt (rho_ne_zero h)

omit hw in
theorem contDiffAt_tE {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) tE e :=
  (Real.contDiffAt_sqrt (rho_ne_zero h)).comp e contDiff_rho.contDiffAt

omit hw in

theorem contDiffAt_ofReal_cpow_const {s : ℝ} (hs : 0 < s) (c : ℂ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℝ => ((r : ℝ) : ℂ) ^ c) s := by
  have h : ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℝ => Complex.exp (((Real.log r : ℝ) : ℂ) * c)) s :=
    (((Complex.ofRealCLM.contDiff.comp_contDiffAt s (Real.contDiffAt_log.mpr hs.ne')).mul
      contDiffAt_const).cexp)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hs] with r hr
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← Complex.ofReal_log hr.le]

omit hw in
theorem contDiffAt_tE_cpow {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) (c : ℂ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun e' : Fin 2 → Fin 2 → ℝ => ((tE e' : ℝ) : ℂ) ^ c) e :=
  (contDiffAt_ofReal_cpow_const (tE_pos h) c).comp e (contDiffAt_tE h)

omit hw in

theorem contDiffAt_firstRowℂ_rotGL_zpow {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) (k : ℤ) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun e' : Fin 2 → Fin 2 → ℝ => (((e' 1 1 / tE e' : ℝ) : ℂ) + ((-(e' 1 0) / tE e' : ℝ) : ℂ) * Complex.I) ^ k) e := by
  have hbase : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun e' : Fin 2 → Fin 2 → ℝ => ((e' 1 1 / tE e' : ℝ) : ℂ) + ((-(e' 1 0) / tE e' : ℝ) : ℂ) * Complex.I) e :=
    (Complex.ofRealCLM.contDiff.comp_contDiffAt e ((contDiff_entry 1 1).contDiffAt.div (contDiffAt_tE h)
      (tE_ne_zero h))).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffAt e (((contDiff_entry 1 0).neg).contDiffAt.div (contDiffAt_tE h)
        (tE_ne_zero h))).mul contDiffAt_const)
  have hne : ((e 1 1 / tE e : ℝ) : ℂ) + ((-(e 1 0) / tE e : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp at hre him
    have ht := tE_ne_zero h
    rcases hre with hre | hre
    · rcases him with him | him
      · apply h
        rw [detE_eq]
        unfold detE
        rw [hre, him]; ring
      · exact ht him
    · exact ht hre
  have hz : ∀ {z : ℂ}, z ≠ 0 → ContDiffAt ℂ (⊤ : ℕ∞) (fun z' : ℂ => z' ^ k) z := by
    intro z hz0
    rcases Int.eq_nat_or_neg k with ⟨n, hn | hn⟩
    · subst hn
      simp_rw [zpow_natCast]
      exact (contDiff_id.pow n).contDiffAt
    · subst hn
      simp_rw [_root_.zpow_neg, zpow_natCast]
      exact ((contDiff_id.pow n).contDiffAt).inv (pow_ne_zero n hz0)
  exact ((hz hne).restrict_scalars ℝ).comp e hbase

def zetaE (e : Fin 2 → Fin 2 → ℝ) : ℂ := (xE e : ℂ) + (yE e : ℂ) * Complex.I

omit hw in
theorem zetaE_im (e : Fin 2 → Fin 2 → ℝ) : (zetaE e).im = yE e := by simp [zetaE]

omit hw in
theorem contDiffAt_zetaE {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) zetaE e :=
  (Complex.ofRealCLM.contDiff.comp_contDiffAt e (contDiffAt_xE h)).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffAt e (contDiffAt_yE h)).mul contDiffAt_const)

def slice (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ → ℂ :=
  fun ζ => φ (g * iota hw (iwasawaSectionGL (UpperHalfPlane.ofComplex ζ)))

theorem slice_zetaE (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) {e : Fin 2 → Fin 2 → ℝ}
    (h : 0 < (Matrix.of e).det) : slice hw φ g (zetaE e) = φ (g * iota hw (iwasawaSectionGL (zE h))) := by
  show φ (g * iota hw (iwasawaSectionGL (UpperHalfPlane.ofComplex (zetaE e)))) = _
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by rw [zetaE_im]; exact yE_pos h)]
  rfl

omit hw in
theorem isOpen_im_pos : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im

theorem contDiffAt_slice (φ : AdelicGL2 (𝓞 F) F → ℂ) (σ : ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hσ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * φ (g * iota hw (iwasawaSectionGL z)))
    {ζ : ℂ} (hζ : 0 < ζ.im) : ContDiffAt ℝ (⊤ : ℕ∞) (slice hw φ g) ζ := by
  set G : ℂ → ℂ := (fun z : UpperHalfPlane => (((z.im : ℝ) : ℂ) ^ σ) * φ (g * iota hw (iwasawaSectionGL z))) ∘
    UpperHalfPlane.ofComplex with hG
  have hGd : DifferentiableOn ℂ G {ζ : ℂ | 0 < ζ.im} := UpperHalfPlane.mdifferentiable_iff.mp hσ
  have hGs : ContDiffAt ℝ (⊤ : ℕ∞) G ζ :=
    ((hGd.contDiffOn isOpen_im_pos).contDiffAt (isOpen_im_pos.mem_nhds hζ)).restrict_scalars ℝ
  have hpow : ContDiffAt ℝ (⊤ : ℕ∞) (fun ζ' : ℂ => ((ζ'.im : ℝ) : ℂ) ^ (-σ)) ζ :=
    (contDiffAt_ofReal_cpow_const hζ (-σ)).comp ζ Complex.imCLM.contDiff.contDiffAt
  refine (hpow.mul hGs).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_im_pos.mem_nhds hζ] with ζ' hζ'
  have hne : (((ζ'.im : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hζ'.ne'
  show slice hw φ g ζ' = ((ζ'.im : ℝ) : ℂ) ^ (-σ) *
    ((((UpperHalfPlane.ofComplex ζ').im : ℝ) : ℂ) ^ σ * φ (g * iota hw (iwasawaSectionGL (UpperHalfPlane.ofComplex ζ'))))
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hζ']
  show slice hw φ g ζ' = ((ζ'.im : ℝ) : ℂ) ^ (-σ) *
    ((((ζ'.im : ℝ) : ℂ) ^ σ) * φ (g * iota hw (iwasawaSectionGL ⟨ζ', hζ'⟩)))
  rw [← mul_assoc, Complex.cpow_neg, inv_mul_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl hne)), one_mul]
  show φ (g * iota hw (iwasawaSectionGL (UpperHalfPlane.ofComplex ζ'))) = _
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hζ']

omit hw in
theorem isOpen_det_pos : IsOpen {e : Fin 2 → Fin 2 → ℝ | 0 < (Matrix.of e).det} :=
  isOpen_lt continuous_const (continuous_id.matrix_det)

omit hw in
theorem isOpen_det_neg : IsOpen {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det < 0} :=
  isOpen_lt (continuous_id.matrix_det) continuous_const

theorem contDiffAt_of_det_pos (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : ℤ) (c₀ σ : ℂ)
    (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ)
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g)
    (hσ : ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * φ (g * iota hw (iwasawaSectionGL z)))
    (g : AdelicGL2 (𝓞 F) F) {e : Fin 2 → Fin 2 → ℝ} (h : 0 < (Matrix.of e).det) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun e' : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e')) e := by
  have hsm : ContDiffAt ℝ (⊤ : ℕ∞) (fun e' : Fin 2 → Fin 2 → ℝ =>
      (((e' 1 1 / tE e' : ℝ) : ℂ) + ((-(e' 1 0) / tE e' : ℝ) : ℂ) * Complex.I) ^ k * (((tE e' : ℝ) : ℂ) ^ c₀) *
        slice hw φ g (zetaE e')) e :=
    ((contDiffAt_firstRowℂ_rotGL_zpow h.ne' k).mul (contDiffAt_tE_cpow h.ne' c₀)).mul
      ((contDiffAt_slice hw φ σ g (hσ g) (by rw [zetaE_im]; exact yE_pos h)).comp e (contDiffAt_zetaE h.ne'))
  refine hsm.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_det_pos.mem_nhds h] with e' he'
  rw [apply_archRealLiftAt_of_det_pos hw φ k c₀ hk hc g he', slice_zetaE hw φ g he', firstRowℂ_rotGL]

def epsGL : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![-1, 0; 0, 1] (by rw [Matrix.det_fin_two_of]; norm_num)

def flipCLM : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun e => Matrix.of.symm ((epsGL : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e)
      map_add' := fun x y => by
        rw [show Matrix.of (x + y) = Matrix.of x + Matrix.of y from rfl, Matrix.mul_add]; rfl
      map_smul' := fun c x => by
        rw [show Matrix.of (c • x) = c • Matrix.of x from rfl, Matrix.mul_smul]; rfl }

omit hw in
theorem flipCLM_apply (e : Fin 2 → Fin 2 → ℝ) :
    flipCLM e = Matrix.of.symm ((epsGL : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e) := rfl

omit hw in
theorem det_of_flipCLM (e : Fin 2 → Fin 2 → ℝ) : (Matrix.of (flipCLM e)).det = -(Matrix.of e).det := by
  rw [flipCLM_apply, Equiv.apply_symm_apply, Matrix.det_mul]
  have : ((epsGL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = -1 := by
    show (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = -1
    rw [Matrix.det_fin_two_of]; norm_num
  rw [this]; ring

omit hw in
theorem epsGL_mul_epsGL : ((epsGL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * (epsGL : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  show (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![-1, 0; 0, 1] = 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem archRealGLAt_mul_archRealLiftAt (M : GL (Fin 2) ℝ) {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) :
    archRealGLAt hw M * archRealLiftAt hw e =
      archRealLiftAt hw (Matrix.of.symm ((M : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e)) := by
  have hM : ((M : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  have h' : (Matrix.of (Matrix.of.symm ((M : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero hM h
  rw [archRealLiftAt_of_det_ne_zero hw h, archRealLiftAt_of_det_ne_zero hw h', ← map_mul]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

theorem archRealLiftAt_eq_of_det_ne_zero {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) :
    archRealLiftAt hw e = archRealGLAt hw epsGL * archRealLiftAt hw (flipCLM e) := by
  have h' : (Matrix.of (flipCLM e)).det ≠ 0 := by rw [det_of_flipCLM]; exact neg_ne_zero.mpr h
  rw [archRealGLAt_mul_archRealLiftAt hw epsGL h', flipCLM_apply, Equiv.apply_symm_apply, ← Matrix.mul_assoc,
    epsGL_mul_epsGL, Matrix.one_mul, Equiv.symm_apply_apply]

theorem contDiffAt_of_det_neg (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : ℤ) (c₀ σ : ℂ)
    (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ)
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g)
    (hσ : ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * φ (g * iota hw (iwasawaSectionGL z)))
    (g : AdelicGL2 (𝓞 F) F) {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det < 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun e' : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e')) e := by
  have hpos : 0 < (Matrix.of (flipCLM e)).det := by rw [det_of_flipCLM]; exact neg_pos.mpr h
  have h1 := contDiffAt_of_det_pos hw φ k c₀ σ hk hc hσ (g * archRealGLAt hw epsGL) hpos
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun e' : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw epsGL * archRealLiftAt hw (flipCLM e'))) e :=
    h1.comp e flipCLM.contDiff.contDiffAt
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_det_neg.mem_nhds h] with e' he'
  show φ (g * archRealLiftAt hw e') = φ (g * archRealGLAt hw epsGL * archRealLiftAt hw (flipCLM e'))
  rw [archRealLiftAt_eq_of_det_ne_zero hw he'.ne, mul_assoc]

theorem main (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : ℤ) (c₀ σ : ℂ)
    (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ)
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g)
    (hσ : ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * φ (g * adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (iwasawaSectionGL z)))) :
    IsArchSmoothAt hw φ := by
  have hι : ∀ mm : GL (Fin 2) ℝ, adelicArchGLInclAt F w
      (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom mm) =
        iota hw mm := fun _ => rfl
  simp only [hι] at hσ
  intro g e he
  rcases lt_or_gt_of_ne he with hneg | hpos
  · exact (contDiffAt_of_det_neg hw φ k c₀ σ hk hc hσ g hneg).contDiffWithinAt
  · exact (contDiffAt_of_det_pos hw φ k c₀ σ hk hc hσ g hpos).contDiffWithinAt

end Smooth

end Ws23.M4

end

open _root_.NumberField _root_.NumberField.InfinitePlace.NumberField AutomorphicForm _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion in
open scoped Manifold in
theorem solution
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : ℤ) (c₀ σ : ℂ)
    (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ)
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g)
    (hσ : ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * φ (g * adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (iwasawaSectionGL z)))) :
    IsArchSmoothAt hw φ :=
  Ws23.M4.main hw φ k c₀ σ hk hc hσ

end S_AutomorphicForm_isArchSmoothAt_of_mdifferentiable_cpow_mul_descent_of_hasArchCharacterAt
end P2MW
export P2MW.S_AutomorphicForm_isArchSmoothAt_of_mdifferentiable_cpow_mul_descent_of_hasArchCharacterAt (solution)
