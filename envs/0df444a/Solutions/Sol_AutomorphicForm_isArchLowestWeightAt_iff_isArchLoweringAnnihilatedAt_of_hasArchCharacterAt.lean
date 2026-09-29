-- Prove2me | solution 1 for AutomorphicForm.isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3af65a31-1d58-5a90-b3d1-c67f28900528

import Mathlib
import Definitions.Def_AutomorphicForm_ArchLowestWeight
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated
import Theorems.Thm_AutomorphicForm_mdifferentiable_im_cpow_mul_iff_forall_lowering_fderiv_eq
import Theorems.Thm_AutomorphicForm_contDiffAt_of_mdifferentiable_im_cpow_mul_of_weight_of_central
import Theorems.Thm_AutomorphicForm_lowering_fderiv_mul_rotation_eq_exp_mul_of_weight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt

set_option autoImplicit false

p2m_open "NumberField AutomorphicForm P2MW.S_AutomorphicForm_isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt.AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion"
open scoped Manifold Topology Classical

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsArchLowestWeightAt isArchLowestWeightAt_zero iwasawaSectionGL AdelicGL2 centralScalar rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archWeightOneℝ archWeightCharℝ HasArchCharacterAt₀ adelicArchGLInclAt loweringAt loweringAt_eq archSliceAt archSliceAt_apply_of_det_ne_zero archSliceAt_apply_of_det_eq_zero archSliceAt_coe_generalLinearGroup archSliceAt_iwasawa IsArchLoweringAnnihilatedAt isArchLoweringAnnihilatedAt_zero mdifferentiable_im_cpow_mul_iff_forall_lowering_fderiv_eq contDiffAt_of_mdifferentiable_im_cpow_mul_of_weight_of_central lowering_fderiv_mul_rotation_eq_exp_mul_of_weight"
p2m_open "AutomorphicForm"

namespace MaassDictionary

theorem exists_eq_exp_of_continuous_mul (f : ℝ → ℂ) (hf : Continuous f) (h0 : f 0 = 1)
    (hmul : ∀ s t : ℝ, f (s + t) = f s * f t) :
    ∃ α : ℂ, ∀ t : ℝ, f t = Complex.exp (α * t) := by
  set Φ : ℝ → ℂ := fun t => ∫ x in (0 : ℝ)..t, f x with hΦ
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (f t) t := fun t =>
    (hf.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b := fun a b =>
    hf.intervalIntegrable a b
  have htrans : ∀ s t : ℝ, Φ (t + s) = Φ t + f t * Φ s := by
    intro s t
    have h1 : Φ (t + s) = (∫ x in (0 : ℝ)..t, f x) + ∫ x in t..t + s, f x :=
      (intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t (t + s))).symm
    have h2 : (∫ x in t..t + s, f x) = ∫ x in (0 : ℝ)..s, f (x + t) := by
      rw [intervalIntegral.integral_comp_add_right f t, zero_add, add_comm s t]
    have h3 : (fun x : ℝ => f (x + t)) = fun x => f t * f x := by
      funext x
      rw [add_comm, hmul]
    rw [h1, h2, h3, intervalIntegral.integral_const_mul]
  by_cases hzero : ∀ s : ℝ, Φ s = 0
  · exfalso
    have hΦ0 : Φ = fun _ => (0 : ℂ) := funext hzero
    have hd := hΦderiv 0
    rw [hΦ0] at hd
    have : f 0 = 0 := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    rw [h0] at this
    exact one_ne_zero this
  · push Not at hzero
    obtain ⟨s, hs⟩ := hzero
    set c : ℂ := (f s - 1) / Φ s with hc
    have hf_eq : ∀ t : ℝ, f t = 1 + c * Φ t := by
      intro t
      have h1 := htrans s t
      have h2 := htrans t s
      rw [add_comm t s] at h1
      have key : f t * Φ s = Φ s + (f s - 1) * Φ t := by
        linear_combination h1.symm.trans h2
      calc f t = f t * Φ s / Φ s := by field_simp
        _ = 1 + c * Φ t := by
          rw [key, hc]
          field_simp
    have hfderiv : ∀ t : ℝ, HasDerivAt f (c * f t) t := by
      intro t
      have h := ((hΦderiv t).const_mul c).const_add 1
      have hfun : (fun x : ℝ => 1 + c * Φ x) = f := (funext hf_eq).symm
      rw [hfun] at h
      exact h
    refine ⟨c, fun t => ?_⟩
    have hexp : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (-(c * y)))
        (Complex.exp (-(c * x)) * (-(c * 1))) x := by
      intro x
      have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-(c * z)))
          (Complex.exp (-(c * (x : ℂ))) * (-(c * 1))) (x : ℂ) :=
        ((hasDerivAt_id (x : ℂ)).const_mul c).neg.cexp
      exact h1.comp_ofReal
    have hg : ∀ x y : ℝ, Complex.exp (-(c * x)) * f x = Complex.exp (-(c * y)) * f y := by
      apply is_const_of_deriv_eq_zero
      · intro x
        exact ((hexp x).mul (hfderiv x)).differentiableAt
      · intro x
        change deriv ((fun y : ℝ => Complex.exp (-(c * y))) * f) x = 0
        rw [((hexp x).mul (hfderiv x)).deriv]
        ring
    have h1 := hg t 0
    rw [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul, h0] at h1
    calc f t = Complex.exp (c * t) * (Complex.exp (-(c * t)) * f t) := by
          rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
      _ = Complex.exp (c * t) := by rw [h1, mul_one]

def rotMat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

theorem det_rotMat (θ : ℝ) : (rotMat θ).det = 1 := by
  have h : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    rw [← sq, ← sq]; exact Real.cos_sq_add_sin_sq θ
  simp [rotMat, Matrix.det_fin_two]
  linarith

def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotMat θ) (by rw [det_rotMat]; exact one_ne_zero)

theorem rotGL_coe (θ : ℝ) : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat θ := rfl

theorem rotGL_mem (θ : ℝ) : rotGL θ ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨det_rotMat θ, ?_, ?_⟩
  · rw [rotGL_coe, det_rotMat, norm_one]
  · intro x y
    have h00 : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = Real.cos θ := rfl
    have h01 : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = Real.sin θ := rfl
    have h10 : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -Real.sin θ := rfl
    have h11 : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = Real.cos θ := rfl
    rw [h00, h01, h10, h11, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs, sq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq θ

def rotSO (θ : ℝ) : rowIsometrySubgroup₀ ℝ := ⟨rotGL θ, rotGL_mem θ⟩

theorem archWeightOneℝ_rotSO (θ : ℝ) :
    ((archWeightOneℝ (rotSO θ) : ℂˣ) : ℂ) = ⟨Real.cos θ, Real.sin θ⟩ := rfl

theorem archWeightOneℝ_rotSO_eq_exp (θ : ℝ) :
    ((archWeightOneℝ (rotSO θ) : ℂˣ) : ℂ) = Complex.exp (θ * Complex.I) := by
  rw [archWeightOneℝ_rotSO, Complex.exp_mul_I]
  apply Complex.ext <;>
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_im]

theorem archWeightCharℝ_rotSO_eq_exp (k : ℤ) (θ : ℝ) :
    ((archWeightCharℝ k (rotSO θ) : ℂˣ) : ℂ) = Complex.exp (Complex.I * k * θ) := by
  rw [archWeightCharℝ, MonoidHom.comp_apply, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val,
    archWeightOneℝ_rotSO_eq_exp, ← Complex.exp_int_mul]
  congr 1
  ring

section Transport

variable (F : Type) [Field F] [NumberField F]

def rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm he (rotSO θ)

omit [NumberField F] in
theorem norm_symm_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  have := norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

variable {F}

omit [NumberField F] in
theorem rowIsometrySubgroup₀Map_rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      (rotAt F hw he θ) = rotSO θ := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change (ringEquivRealOfIsReal hw) ((ringEquivRealOfIsReal hw).symm (rotMat θ i j)) = rotMat θ i j
  exact RingEquiv.apply_symm_apply _ _

omit [NumberField F] in

theorem map_rotGL_eq_rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom (rotGL θ) =
      ((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) := by
  apply Units.ext
  ext i j
  rfl

end Transport

section Slices

variable {F : Type} [Field F] [NumberField F]

theorem slice_mul_rotMat (w : InfinitePlace F) (hw : w.IsReal) (k : ℤ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hk : HasArchCharacterAt₀ F w
      ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) φ)
    (g : AdelicGL2 (𝓞 F) F) (m : Matrix (Fin 2) (Fin 2) ℝ) (hm : m.det ≠ 0) (θ : ℝ) :
    archSliceAt w hw φ g (m * rotMat θ) = Complex.exp (Complex.I * k * θ) * archSliceAt w hw φ g m := by
  have he := norm_symm_ringEquivRealOfIsReal F hw
  set mGL : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero m hm with hmGL
  have h1 : archSliceAt w hw φ g (m * rotMat θ) =
      archSliceAt w hw φ g (((mGL * rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) := rfl
  have h2 : archSliceAt w hw φ g m =
      archSliceAt w hw φ g (((mGL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) := rfl
  rw [h1, archSliceAt_coe_generalLinearGroup, h2, archSliceAt_coe_generalLinearGroup, map_mul, map_mul,
    ← mul_assoc, map_rotGL_eq_rotAt hw he]
  have h := hk (rotAt F hw he θ)
    (g * adelicArchGLInclAt F w (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom mGL))
  rw [MonoidHom.comp_apply, rowIsometrySubgroup₀Map_rotAt, archWeightCharℝ_rotSO_eq_exp] at h
  exact h

def scalarGL (t : ℝ) (ht : t ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact pow_ne_zero 2 ht)

theorem scalarGL_coe (t : ℝ) (ht : t ≠ 0) :
    ((scalarGL t ht : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = t • (1 : Matrix (Fin 2) (Fin 2) ℝ) := rfl

def scalarIdele (w : InfinitePlace F) (hw : w.IsReal) (t : ℝ) (ht : t ≠ 0) : (AdeleRing (𝓞 F) F)ˣ where
  val := ((Function.update (1 : ∀ v : InfinitePlace F, v.Completion) w
      ((ringEquivRealOfIsReal hw).symm t) : InfiniteAdeleRing F), (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
  inv := ((Function.update (1 : ∀ v : InfinitePlace F, v.Completion) w
      ((ringEquivRealOfIsReal hw).symm t⁻¹) : InfiniteAdeleRing F), (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
  val_inv := by
    refine Prod.ext ?_ (mul_one _)
    show (fun v => Function.update (1 : ∀ v : InfinitePlace F, v.Completion) w ((ringEquivRealOfIsReal hw).symm t) v *
        Function.update (1 : ∀ v : InfinitePlace F, v.Completion) w ((ringEquivRealOfIsReal hw).symm t⁻¹) v) =
      fun _ => 1
    funext v
    by_cases hv : v = w
    · subst hv
      rw [Function.update_self, Function.update_self, ← map_mul, mul_inv_cancel₀ ht, map_one]
    · rw [Function.update_of_ne hv, Function.update_of_ne hv, Pi.one_apply, mul_one]
  inv_val := by
    refine Prod.ext ?_ (mul_one _)
    show (fun v => Function.update (1 : ∀ v : InfinitePlace F, v.Completion) w ((ringEquivRealOfIsReal hw).symm t⁻¹) v *
        Function.update (1 : ∀ v : InfinitePlace F, v.Completion) w ((ringEquivRealOfIsReal hw).symm t) v) =
      fun _ => 1
    funext v
    by_cases hv : v = w
    · subst hv
      rw [Function.update_self, Function.update_self, ← map_mul, inv_mul_cancel₀ ht, map_one]
    · rw [Function.update_of_ne hv, Function.update_of_ne hv, Pi.one_apply, mul_one]

theorem scalarIdele_congr (w : InfinitePlace F) (hw : w.IsReal) {t t' : ℝ} (h : t = t') (ht : t ≠ 0) (ht' : t' ≠ 0) :
    scalarIdele w hw t ht = scalarIdele w hw t' ht' := by
  subst h; rfl

theorem scalarIdele_coe (w : InfinitePlace F) (hw : w.IsReal) (t : ℝ) (ht : t ≠ 0) :
    ((scalarIdele w hw t ht : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) =
      ((Function.update (1 : ∀ v : InfinitePlace F, v.Completion) w
        ((ringEquivRealOfIsReal hw).symm t) : InfiniteAdeleRing F), (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :=
  rfl

theorem centralScalar_coe_apply (z : (AdeleRing (𝓞 F) F)ˣ) (i j : Fin 2) :
    ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      if i = j then (z : AdeleRing (𝓞 F) F) else 0 := by
  show Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem adelicArchGLInclAt_coe_apply (w : InfinitePlace F) (kk : GL (Fin 2) w.Completion) (i j : Fin 2) :
    ((adelicArchGLInclAt F w kk : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      ((fun v : InfinitePlace F =>
          (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w
            (kk : Matrix (Fin 2) (Fin 2) w.Completion) v) i j : InfiniteAdeleRing F),
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) :=
  rfl

theorem adelicArchGLInclAt_scalarGL (w : InfinitePlace F) (hw : w.IsReal) (t : ℝ) (ht : t ≠ 0) :
    adelicArchGLInclAt F w (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom (scalarGL t ht)) =
      centralScalar (𝓞 F) F (scalarIdele w hw t ht) := by
  apply Units.ext
  ext i j
  rw [adelicArchGLInclAt_coe_apply, centralScalar_coe_apply]

  have hK : ∀ i j : Fin 2,
      ((Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom (scalarGL t ht) :
          GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j =
        (ringEquivRealOfIsReal hw).symm ((t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j) := fun _ _ => rfl
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, scalarIdele_coe]
    refine Prod.ext ?_ ?_
    · show (fun v : InfinitePlace F =>
          Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w
            ((Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom (scalarGL t ht) :
                GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) v i i) =
        Function.update (1 : ∀ v : InfinitePlace F, v.Completion) w ((ringEquivRealOfIsReal hw).symm t)
      funext v
      by_cases hv : v = w
      · subst hv
        rw [Function.update_self, Function.update_self, hK]
        simp
      · rw [Function.update_of_ne hv, Function.update_of_ne hv]
        simp
    · show (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i i = 1
      simp
  · rw [if_neg hij]
    refine Prod.ext ?_ ?_
    · show (fun v : InfinitePlace F =>
          Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w
            ((Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom (scalarGL t ht) :
                GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) v i j) =
        (0 : InfiniteAdeleRing F)
      funext v
      by_cases hv : v = w
      · subst hv
        rw [Function.update_self, hK]
        simp [hij]
        rfl
      · rw [Function.update_of_ne hv]
        simp [hij]
        rfl
    · show (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j = 0
      simp [hij]

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * g = g * centralScalar (𝓞 F) F z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

theorem slice_smul (w : InfinitePlace F) (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξ : ∀ (z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g)
    (g : AdelicGL2 (𝓞 F) F) (m : Matrix (Fin 2) (Fin 2) ℝ) (hm : m.det ≠ 0) (t : ℝ) (ht : t ≠ 0) :
    archSliceAt w hw φ g (t • m) =
      ((ξ ⟨scalarIdele w hw t ht, trivial⟩ : ℂˣ) : ℂ) * archSliceAt w hw φ g m := by
  set mGL : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero m hm with hmGL
  have h1 : archSliceAt w hw φ g (t • m) =
      archSliceAt w hw φ g (((scalarGL t ht * mGL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) := by
    congr 1
    rw [Units.val_mul, scalarGL_coe, smul_mul_assoc, one_mul]
    rfl
  have h2 : archSliceAt w hw φ g m =
      archSliceAt w hw φ g (((mGL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) := rfl
  rw [h1, archSliceAt_coe_generalLinearGroup, h2, archSliceAt_coe_generalLinearGroup, map_mul, map_mul,
    ← mul_assoc, adelicArchGLInclAt_scalarGL, ← centralScalar_mul_comm, mul_assoc]
  exact hξ ⟨scalarIdele w hw t ht, trivial⟩ _

theorem scalarIdele_exp_add (w : InfinitePlace F) (hw : w.IsReal) (a b : ℝ) :
    scalarIdele w hw (Real.exp (a + b)) (Real.exp_pos _).ne' =
      scalarIdele w hw (Real.exp a) (Real.exp_pos _).ne' * scalarIdele w hw (Real.exp b) (Real.exp_pos _).ne' := by
  apply Units.ext
  refine Prod.ext ?_ (mul_one _).symm
  show (fun v => Function.update (1 : ∀ v : InfinitePlace F, v.Completion) w ((ringEquivRealOfIsReal hw).symm (Real.exp (a + b))) v) =
    fun v => Function.update (1 : ∀ v : InfinitePlace F, v.Completion) w ((ringEquivRealOfIsReal hw).symm (Real.exp a)) v *
      Function.update (1 : ∀ v : InfinitePlace F, v.Completion) w ((ringEquivRealOfIsReal hw).symm (Real.exp b)) v
  funext v
  by_cases hv : v = w
  · subst hv
    simp only [Function.update_self]
    rw [Real.exp_add, map_mul]
  · simp [Function.update_of_ne hv]

theorem scalarIdele_exp_zero (w : InfinitePlace F) (hw : w.IsReal) :
    scalarIdele w hw (Real.exp 0) (Real.exp_pos _).ne' = 1 := by
  apply Units.ext
  refine Prod.ext ?_ rfl
  show (fun v => Function.update (1 : ∀ v : InfinitePlace F, v.Completion) w ((ringEquivRealOfIsReal hw).symm (Real.exp 0)) v) =
    fun _ => 1
  funext v
  by_cases hv : v = w
  · subst hv
    simp only [Function.update_self, Real.exp_zero, map_one]
  · simp [Function.update_of_ne hv]

theorem scalarIdele_exp_neg (w : InfinitePlace F) (hw : w.IsReal) (a : ℝ) :
    scalarIdele w hw (Real.exp (-a)) (Real.exp_pos _).ne' = (scalarIdele w hw (Real.exp a) (Real.exp_pos _).ne')⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← scalarIdele_exp_add]
  rw [scalarIdele_congr w hw (neg_add_cancel a ▸ rfl : Real.exp (-a + a) = Real.exp 0) _ (Real.exp_pos _).ne']
  exact scalarIdele_exp_zero w hw

theorem continuous_centralScalar_scalarIdele_exp (w : InfinitePlace F) (hw : w.IsReal) :
    Continuous fun a : ℝ => (centralScalar (𝓞 F) F (scalarIdele w hw (Real.exp a) (Real.exp_pos _).ne') :
      AdelicGL2 (𝓞 F) F) := by

  have hentry : ∀ (s : ℝ → ℝ), Continuous s →
      Continuous fun a : ℝ => ((Function.update (1 : ∀ v : InfinitePlace F, v.Completion) w
        ((ringEquivRealOfIsReal hw).symm (s a)) : InfiniteAdeleRing F), (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) := by
    intro s hs
    refine Continuous.prodMk ?_ continuous_const
    apply continuous_pi
    intro v
    by_cases hv : v = w
    · subst hv
      simp only [Function.update_self]
      exact (isometryEquivRealOfIsReal hw).symm.continuous.comp hs
    · simp only [Function.update_of_ne hv]
      exact continuous_const
  have hval : ∀ (s : ℝ → ℝ) (hs : Continuous s) (hs0 : ∀ a, s a ≠ 0), Continuous fun a : ℝ =>
      ((centralScalar (𝓞 F) F (scalarIdele w hw (s a) (hs0 a)) : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    intro s hs hs0
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [centralScalar_coe_apply]
    by_cases hij : i = j
    · simp only [if_pos hij]
      exact hentry s hs
    · simp only [if_neg hij]
      exact continuous_const
  rw [Units.continuous_iff]
  refine ⟨hval Real.exp Real.continuous_exp _, ?_⟩
  have : (fun a : ℝ => (((centralScalar (𝓞 F) F (scalarIdele w hw (Real.exp a) (Real.exp_pos _).ne'))⁻¹ :
      AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) =
      fun a : ℝ => ((centralScalar (𝓞 F) F (scalarIdele w hw (Real.exp (-a)) (Real.exp_pos _).ne') :
        AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    funext a
    rw [scalarIdele_exp_neg, map_inv]
  rw [this]
  exact hval (fun a => Real.exp (-a)) (Real.continuous_exp.comp continuous_neg) _

theorem exists_cpow_of_ne_zero (w : InfinitePlace F) (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : Continuous φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξ : ∀ (z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g)
    {g₀ : AdelicGL2 (𝓞 F) F} (hg₀ : φ g₀ ≠ 0) :
    ∃ c₀ : ℂ, ∀ (t : ℝ) (ht : 0 < t),
      ((ξ ⟨scalarIdele w hw t ht.ne', trivial⟩ : ℂˣ) : ℂ) = ((t : ℂ) ^ c₀) := by
  set f : ℝ → ℂ := fun a => ((ξ ⟨scalarIdele w hw (Real.exp a) (Real.exp_pos _).ne', trivial⟩ : ℂˣ) : ℂ) with hf
  have hmul : ∀ a b : ℝ, f (a + b) = f a * f b := by
    intro a b
    have hab : (⟨scalarIdele w hw (Real.exp (a + b)) (Real.exp_pos _).ne', trivial⟩ :
        (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) =
        ⟨scalarIdele w hw (Real.exp a) (Real.exp_pos _).ne', trivial⟩ *
          ⟨scalarIdele w hw (Real.exp b) (Real.exp_pos _).ne', trivial⟩ :=
      Subtype.ext (scalarIdele_exp_add w hw a b)
    simp only [hf]
    rw [hab, map_mul, Units.val_mul]
  have h0 : f 0 = 1 := by
    simp only [hf]
    have : (⟨scalarIdele w hw (Real.exp 0) (Real.exp_pos _).ne', trivial⟩ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) = 1 := by
      apply Subtype.ext
      exact scalarIdele_exp_zero w hw
    rw [this, map_one, Units.val_one]
  have hfφ : ∀ a : ℝ, f a = φ (centralScalar (𝓞 F) F (scalarIdele w hw (Real.exp a) (Real.exp_pos _).ne') * g₀) / φ g₀ := by
    intro a
    rw [hξ ⟨_, trivial⟩ g₀, mul_div_assoc, div_self hg₀, mul_one]
  have hcont : Continuous f := by
    rw [show f = _ from funext hfφ]
    exact (hφ.comp ((continuous_centralScalar_scalarIdele_exp w hw).mul continuous_const)).div_const _
  obtain ⟨α, hα⟩ := exists_eq_exp_of_continuous_mul f hcont h0 hmul
  refine ⟨α, fun t ht => ?_⟩
  have hlog : Real.exp (Real.log t) = t := Real.exp_log ht
  have hsub : (⟨scalarIdele w hw t ht.ne', trivial⟩ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) =
      ⟨scalarIdele w hw (Real.exp (Real.log t)) (Real.exp_pos _).ne', trivial⟩ :=
    Subtype.ext (scalarIdele_congr w hw hlog.symm ht.ne' (Real.exp_pos _).ne')
  rw [hsub]
  change f (Real.log t) = _
  rw [hα, Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne'), ← Complex.ofReal_log ht.le]
  congr 1
  ring

def lmul (M : Matrix (Fin 2) (Fin 2) ℝ) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun n => ((M * Matrix.of n : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ)
      map_add' := fun a b => by
        show (M * (Matrix.of a + Matrix.of b) : Matrix (Fin 2) (Fin 2) ℝ) = _
        rw [Matrix.mul_add]; rfl
      map_smul' := fun r a => by
        show (M * (r • Matrix.of a) : Matrix (Fin 2) (Fin 2) ℝ) = _
        rw [Matrix.mul_smul]; rfl }

theorem lmul_apply (M n : Matrix (Fin 2) (Fin 2) ℝ) :
    lmul M n = ((M * n : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) := rfl

theorem loweringAt_comp_lmul (G : (Fin 2 → Fin 2 → ℝ) → ℂ) (M n : Matrix (Fin 2) (Fin 2) ℝ)
    (hG : DifferentiableAt ℝ G (M * n)) :
    loweringAt (fun p => G (lmul M p)) n = loweringAt G (M * n) := by
  let nP : Fin 2 → Fin 2 → ℝ := n
  have hcomp : HasFDerivAt (fun p : Fin 2 → Fin 2 → ℝ => G (lmul M p)) ((fderiv ℝ G (M * n)).comp (lmul M)) nP := by
    have h1 : HasFDerivAt G (fderiv ℝ G (M * n)) (lmul M nP) := hG.hasFDerivAt
    exact h1.comp nP (lmul M).hasFDerivAt
  rw [loweringAt_eq, loweringAt_eq, hcomp.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  have e1 : (fderiv ℝ G (M * n)) (lmul M (n * !![1, 0; 0, -1])) = (fderiv ℝ G (M * n)) ((M * n) * !![1, 0; 0, -1]) := by
    congr 1
    exact (Matrix.mul_assoc M n _).symm
  have e2 : (fderiv ℝ G (M * n)) (lmul M (n * !![0, 1; 1, 0])) = (fderiv ℝ G (M * n)) ((M * n) * !![0, 1; 1, 0]) := by
    congr 1
    exact (Matrix.mul_assoc M n _).symm
  rw [e1, e2]

theorem slice_mul_incl (w : InfinitePlace F) (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ) :
    archSliceAt w hw φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom h)) =
      fun p => archSliceAt w hw φ g (lmul (h : Matrix (Fin 2) (Fin 2) ℝ) p) := by
  funext p
  by_cases hp : (Matrix.of p).det ≠ 0
  · have hp' : (Matrix.of (lmul (h : Matrix (Fin 2) (Fin 2) ℝ) p)).det ≠ 0 := by
      show ((h : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of p).det ≠ 0
      rw [Matrix.det_mul, ← Matrix.GeneralLinearGroup.val_det_apply]
      exact mul_ne_zero (Matrix.GeneralLinearGroup.det h).ne_zero hp
    rw [archSliceAt_apply_of_det_ne_zero w hw φ _ _ hp, archSliceAt_apply_of_det_ne_zero w hw φ _ _ hp']
    have hGL : Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of (lmul (h : Matrix (Fin 2) (Fin 2) ℝ) p)) hp' =
        h * Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of p) hp := by
      apply Units.ext
      rfl
    rw [hGL, map_mul, map_mul, mul_assoc]
  · push Not at hp
    have hp' : (Matrix.of (lmul (h : Matrix (Fin 2) (Fin 2) ℝ) p)).det = 0 := by
      show ((h : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of p).det = 0
      rw [Matrix.det_mul, hp, mul_zero]
    rw [archSliceAt_apply_of_det_eq_zero w hw φ _ _ hp, archSliceAt_apply_of_det_eq_zero w hw φ _ _ hp']

theorem slice_one (w : InfinitePlace F) (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    archSliceAt w hw φ g ((1 : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) = φ g := by
  have h : ((1 : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) =
      (((1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) := rfl
  rw [h, archSliceAt_coe_generalLinearGroup, map_one, map_one, mul_one]

end Slices

theorem main (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal) (k : ℤ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hk : HasArchCharacterAt₀ F w
      ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξ : ∀ (z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g) :
    IsArchLowestWeightAt w hw φ ↔ IsArchLoweringAnnihilatedAt w hw φ := by

  by_cases hzero : ∀ g, φ g = 0
  · have hφ0 : φ = fun _ => 0 := funext hzero
    subst hφ0
    exact iff_of_true (isArchLowestWeightAt_zero w hw) (isArchLoweringAnnihilatedAt_zero w hw)
  push Not at hzero
  obtain ⟨g₀, hg₀⟩ := hzero

  obtain ⟨c₀, hc₀⟩ := exists_cpow_of_ne_zero w hw φ hφ ξ hξ hg₀

  set f : AdelicGL2 (𝓞 F) F → (Fin 2 → Fin 2 → ℝ) → ℂ := fun g => archSliceAt w hw φ g with hf
  have hkf : ∀ (g : AdelicGL2 (𝓞 F) F) (m : Matrix (Fin 2) (Fin 2) ℝ), 0 < m.det → ∀ θ : ℝ,
      f g (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) = Complex.exp (Complex.I * k * θ) * f g m :=
    fun g m hm θ => slice_mul_rotMat w hw k φ hk g m hm.ne' θ
  have hcf : ∀ (g : AdelicGL2 (𝓞 F) F) (m : Matrix (Fin 2) (Fin 2) ℝ), 0 < m.det → ∀ t : ℝ, 0 < t →
      f g (t • m) = ((t : ℂ) ^ c₀) * f g m := by
    intro g m hm t ht
    rw [← hc₀ t ht]
    exact slice_smul w hw φ ξ hξ g m hm.ne' t ht.ne'
  have hsecdet : ∀ z : UpperHalfPlane, 0 < (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det := by
    intro z
    rw [Matrix.det_fin_two_of]
    simpa using z.im_pos

  have hdesc : ∀ (σ : ℂ) (g : AdelicGL2 (𝓞 F) F),
      (fun z : UpperHalfPlane => (((z.im : ℝ) : ℂ) ^ σ) *
          φ (g * adelicArchGLInclAt F w (Matrix.GeneralLinearGroup.map
            (ringEquivRealOfIsReal hw).symm.toRingHom (iwasawaSectionGL z)))) =
        fun z : UpperHalfPlane => (((z.im : ℝ) : ℂ) ^ σ) * f g (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro σ g
    funext z
    simp only [hf]
    rw [archSliceAt_iwasawa]
  constructor
  ·
    rintro ⟨σ, hσ⟩
    have hhol : ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (fun z : UpperHalfPlane => (((z.im : ℝ) : ℂ) ^ σ) * f g (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)) := by
      intro g
      rw [← hdesc σ g]
      exact hσ g

    have hdiff : ∀ (g : AdelicGL2 (𝓞 F) F) (m : Matrix (Fin 2) (Fin 2) ℝ), 0 < m.det → DifferentiableAt ℝ (f g) m := by
      intro g m hm
      exact (AutomorphicForm.contDiffAt_of_mdifferentiable_im_cpow_mul_of_weight_of_central (f g) k c₀ σ
        (hkf g) (hcf g) (hhol g) m hm).differentiableAt (by simp)

    set δ : ℂ := -(σ + (k + c₀) / 2) with hδ
    have heig : ∀ (g : AdelicGL2 (𝓞 F) F) (z : UpperHalfPlane),
        loweringAt (f g) !![z.im, z.re; 0, 1] = δ * f g (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
      intro g
      exact (AutomorphicForm.mdifferentiable_im_cpow_mul_iff_forall_lowering_fderiv_eq (f g) k c₀ σ
        (fun z => hdiff g _ (hsecdet z)) (fun z θ => hkf g _ (hsecdet z) θ) (fun z t ht => hcf g _ (hsecdet z) t ht)).mp
        (hhol g)

    have heig' : ∀ (g : AdelicGL2 (𝓞 F) F) (m : Matrix (Fin 2) (Fin 2) ℝ), 0 < m.det →
        loweringAt (f g) m = δ * f g m := by
      intro g m hm
      set mGL : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero m hm.ne' with hmGL
      have h1 := heig (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom mGL)) UpperHalfPlane.I
      have hsec1 : (!![UpperHalfPlane.I.im, UpperHalfPlane.I.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [UpperHalfPlane.I]
      simp only [hf] at h1 ⊢
      rw [slice_mul_incl, hsec1] at h1
      have hG : DifferentiableAt ℝ (archSliceAt w hw φ g)
          ((((mGL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * 1 : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) := by
        rw [Matrix.mul_one]; exact hdiff g m hm
      have h2 : loweringAt (fun p => archSliceAt w hw φ g (lmul (mGL : Matrix (Fin 2) (Fin 2) ℝ) p)) 1 =
          loweringAt (archSliceAt w hw φ g) ((mGL : Matrix (Fin 2) (Fin 2) ℝ) * 1) :=
        loweringAt_comp_lmul (archSliceAt w hw φ g) _ 1 hG
      rw [h2, Matrix.mul_one] at h1
      simp only [lmul_apply, Matrix.mul_one] at h1
      exact h1

    by_cases hδ0 : δ = 0
    · intro g z
      refine ⟨hdiff g _ (hsecdet z), ?_⟩
      have := heig g z
      rw [hδ0, zero_mul] at this
      exact this
    · exfalso
      apply hg₀

      have hvan : ∀ (g : AdelicGL2 (𝓞 F) F) (m : Matrix (Fin 2) (Fin 2) ℝ), 0 < m.det → f g m = 0 := by
        intro g m hm
        set θ : ℝ := Real.pi / 2 with hθ
        have hmr : 0 < (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]).det := by
          rw [Matrix.det_mul, show (!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ) = rotMat θ from rfl,
            det_rotMat, mul_one]
          exact hm

        have hshift := AutomorphicForm.lowering_fderiv_mul_rotation_eq_exp_mul_of_weight (f g) k (hdiff g) (hkf g) m hm θ
        change loweringAt (f g) (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) =
          Complex.exp (Complex.I * (k - 2) * θ) * loweringAt (f g) m at hshift
        rw [heig' g m hm] at hshift
        have hA : loweringAt (f g) (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) =
            δ * (Complex.exp (Complex.I * k * θ) * f g m) := by
          rw [heig' g _ hmr]
          congr 1
          exact hkf g m hm θ
        have hB := hA.symm.trans hshift

        have hexp : Complex.exp (Complex.I * (k - 2) * θ) = -Complex.exp (Complex.I * k * θ) := by
          rw [show Complex.I * (k - 2) * (θ : ℂ) = Complex.I * k * θ - (2 * θ : ℂ) * Complex.I by ring,
            Complex.exp_sub, hθ]
          push_cast
          rw [show (2 : ℂ) * (Real.pi / 2 : ℂ) * Complex.I = Real.pi * Complex.I by ring, Complex.exp_pi_mul_I]
          ring
        rw [hexp] at hB
        have h3 : (2 * δ * Complex.exp (Complex.I * k * θ)) * f g m = 0 := by linear_combination hB
        rcases mul_eq_zero.mp h3 with h4 | h4
        · exfalso
          rcases mul_eq_zero.mp h4 with h5 | h5
          · rcases mul_eq_zero.mp h5 with h6 | h6
            · norm_num at h6
            · exact hδ0 h6
          · exact Complex.exp_ne_zero _ h5
        · exact h4
      have := hvan g₀ 1 (by rw [Matrix.det_one]; exact one_pos)
      simp only [hf] at this
      rwa [slice_one] at this
  ·
    intro hann
    refine ⟨-((k : ℂ) + c₀) / 2, fun g => ?_⟩
    rw [hdesc]
    refine (AutomorphicForm.mdifferentiable_im_cpow_mul_iff_forall_lowering_fderiv_eq (f g) k c₀ (-((k : ℂ) + c₀) / 2)
      (fun z => (hann g z).1) (fun z θ => hkf g _ (hsecdet z) θ) (fun z t ht => hcf g _ (hsecdet z) t ht)).mpr ?_
    intro z
    have h0 : -(-((k : ℂ) + c₀) / 2 + (k + c₀) / 2) * f g (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by ring
    rw [h0]
    exact (hann g z).2

end MaassDictionary

end AutomorphicForm

end

theorem solution
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal) (k : ℤ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hk : HasArchCharacterAt₀ F w
      ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξ : ∀ (z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g) :
    IsArchLowestWeightAt w hw φ ↔ IsArchLoweringAnnihilatedAt w hw φ :=
  AutomorphicForm.MaassDictionary.main F w hw k φ hφ hk ξ hξ

end S_AutomorphicForm_isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt
end P2MW
export P2MW.S_AutomorphicForm_isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt (solution)
