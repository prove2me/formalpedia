-- Prove2me | solution 1 for AutomorphicForm.detBand_eq_inf_twistedCentralizer_detBand_and_pos_and_lt_top_of_coupled
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/46660565-c92c-554f-b914-316dbdf2d6b3

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_detBand_eq_inf_twistedCentralizer_detBand_and_pos_and_lt_top_of_coupled

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real
open scoped TensorProduct TensorProduct.RightActions

open Filter Topology

noncomputable section

namespace BandTransfer

section Group

theorem locallyCompactSpace_GL : LocallyCompactSpace (GL (Fin 2) ℝ) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  haveI : T2Space (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → ℝ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem det_val_ne_zero (g : GL (Fin 2) ℝ) : Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero

theorem continuous_det_val : Continuous fun g : GL (Fin 2) ℝ => Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) :=
  (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℝ)).matrix_det

def rotAB (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : GL (Fin 2) ℝ :=
  ⟨!![a, b; -b, a], !![a, -b; b, a],
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination h | ring,
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination h | ring⟩

@[scoped simp] theorem rotAB_val (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ((rotAB a b h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; -b, a] := rfl

theorem rotAB_mem (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : rotAB a b h ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [rotAB_val, Matrix.det_fin_two_of]
    linear_combination h
  · rw [rotAB_val, Matrix.det_fin_two_of]
    rw [show a * a - b * -b = 1 by linear_combination h, norm_one]
  · intro x y
    simp only [rotAB_val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * h

def rotGL (θ : ℝ) : GL (Fin 2) ℝ := rotAB (Real.cos θ) (Real.sin θ) (Real.cos_sq_add_sin_sq θ)

theorem rotGL_val (θ : ℝ) :
    ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] :=
  rfl

theorem rotGL_inv_val (θ : ℝ) :
    (((rotGL θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] :=
  rfl

theorem continuous_rotGL : Continuous rotGL := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ rotGL) = fun θ => !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := rfl
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun θ => (((rotGL θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) =
        fun θ => !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := rfl
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem rotGL_zero : rotGL 0 = 1 := by
  refine Units.ext ?_
  rw [rotGL_val, Real.cos_zero, Real.sin_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

def triU (q : ℝ × ℝ × ℝ) : GL (Fin 2) ℝ :=
  ⟨!![max q.1 1, max q.1 1 * q.2.2; 0, max q.2.1 1],
    !![(max q.1 1)⁻¹, -(q.2.2 * (max q.2.1 1)⁻¹); 0, (max q.2.1 1)⁻¹],
    by
      have h1 : max q.1 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
      have h2 : max q.2.1 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2]
      ring,
    by
      have h1 : max q.1 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
      have h2 : max q.2.1 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2]⟩

theorem triU_val (q : ℝ × ℝ × ℝ) :
    ((triU q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![max q.1 1, max q.1 1 * q.2.2; 0, max q.2.1 1] := rfl

theorem continuous_triU : Continuous triU := by
  have c1 : Continuous fun q : ℝ × ℝ × ℝ => max q.1 1 := continuous_fst.max continuous_const
  have c2 : Continuous fun q : ℝ × ℝ × ℝ => max q.2.1 1 := (continuous_fst.comp continuous_snd).max continuous_const
  have c3 : Continuous fun q : ℝ × ℝ × ℝ => q.2.2 := continuous_snd.comp continuous_snd
  have h1 : ∀ q : ℝ × ℝ × ℝ, max q.1 1 ≠ 0 := fun q => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have h2 : ∀ q : ℝ × ℝ × ℝ, max q.2.1 1 ≠ 0 := fun q => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have c1i : Continuous fun q : ℝ × ℝ × ℝ => (max q.1 1)⁻¹ := c1.inv₀ h1
  have c2i : Continuous fun q : ℝ × ℝ × ℝ => (max q.2.1 1)⁻¹ := c2.inv₀ h2
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ triU) = fun q : ℝ × ℝ × ℝ => !![max q.1 1, max q.1 1 * q.2.2; 0, max q.2.1 1] := rfl
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j
    · simpa using c1
    · have h__af := c1.mul c3
      simp at h__af ⊢
      exact h__af
    · simpa using continuous_const
    · simpa using c2
  · have : (fun q => (((triU q)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) =
        fun q : ℝ × ℝ × ℝ => !![(max q.1 1)⁻¹, -(q.2.2 * (max q.2.1 1)⁻¹); 0, (max q.2.1 1)⁻¹] := rfl
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j
    · simpa using c1i
    · simp
      exact (c3.mul c2i).neg
    · simpa using continuous_const
    · simpa using c2i

theorem exists_angle {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ θ ∈ Set.Icc (-Real.pi) Real.pi, Real.cos θ = a ∧ Real.sin θ = b := by
  set z : ℂ := ⟨a, b⟩ with hz
  have hz1 : ‖z‖ = 1 := by
    have h2 : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_mk]
      nlinarith [h]
    have h0 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [h2, h0]
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz1
    exact zero_ne_one hz1
  refine ⟨Complex.arg z, ⟨(Complex.arg_mem_Ioc z).1.le, (Complex.arg_mem_Ioc z).2⟩, ?_, ?_⟩
  · rw [Complex.cos_arg hz0, hz1, div_one]
  · rw [Complex.sin_arg, hz1, div_one]

theorem ellipticElt_val (r θ : ℝ) (hr : 0 < r) :
    ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * Real.cos θ, r * Real.sin θ; -(r * Real.sin θ), r * Real.cos θ] := rfl

theorem val_scalar_two (cu : ℝˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) cu : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(cu : ℝ), 0; 0, (cu : ℝ)] := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem ellipticElt_eq (r θ : ℝ) (hr : 0 < r) (cu : ℝˣ) (hcu : (cu : ℝ) = r) :
    ellipticElt r θ hr = Matrix.GeneralLinearGroup.scalar (Fin 2) cu * rotGL θ := by
  refine Units.ext ?_
  rw [Units.val_mul, ellipticElt_val, val_scalar_two, rotGL_val, hcu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem continuous_ellipticElt (r : ℝ) (hr : 0 < r) : Continuous fun θ => ellipticElt r θ hr := by
  have : (fun θ => ellipticElt r θ hr) =
      fun θ => Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr.ne') * rotGL θ :=
    funext fun θ => ellipticElt_eq r θ hr _ rfl
  rw [this]
  exact continuous_const.mul continuous_rotGL

theorem ellipticElt_zero (r : ℝ) (hr : 0 < r) (cu : ℝˣ) (hcu : (cu : ℝ) = r) :
    ellipticElt r 0 hr = Matrix.GeneralLinearGroup.scalar (Fin 2) cu := by
  rw [ellipticElt_eq r 0 hr cu hcu, rotGL_zero, mul_one]

theorem det_ellipticElt (r θ : ℝ) (hr : 0 < r) (cu : ℝˣ) (hcu : (cu : ℝ) = r) :
    Matrix.GeneralLinearGroup.det (ellipticElt r θ hr) = cu ^ 2 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, ellipticElt_val, Matrix.det_fin_two_of, Units.val_pow_eq_pow_val, hcu]
  linear_combination r ^ 2 * Real.cos_sq_add_sin_sq θ

theorem isRegularSemisimple_ellipticElt {r θ : ℝ} (hr : 0 < r) (hs : Real.sin θ ≠ 0) :
    IsRegularSemisimple (ellipticElt r θ hr) := by
  rw [isRegularSemisimple_iff_ne_zero, ellipticElt_val, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  intro h
  have h2 : (r * Real.sin θ) ^ 2 = 0 := by linear_combination (-1 / 4 : ℝ) * h
  exact mul_ne_zero hr.ne' hs (pow_eq_zero_iff two_ne_zero |>.1 h2)

end Group

section Torus

theorem centralizer_entries {r θ : ℝ} (hr : 0 < r) (hs : Real.sin θ ≠ 0) {g : GL (Fin 2) ℝ}
    (hg : g ∈ Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ))) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -(g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
  have h := Subgroup.mem_centralizer_iff.1 hg (ellipticElt r θ hr) (Set.mem_singleton _)
  have hm := congrArg (fun u : GL (Fin 2) ℝ => (u : Matrix (Fin 2) (Fin 2) ℝ)) h
  simp only [Units.val_mul, ellipticElt_val] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  have hrs : r * Real.sin θ ≠ 0 := mul_ne_zero hr.ne' hs
  constructor
  · apply mul_left_cancel₀ hrs
    linarith
  · apply mul_left_cancel₀ hrs
    linarith

private theorem _root_.BandTransfer.isClosed_centralizer (γ : GL (Fin 2) ℝ) :
    IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) : Set (GL (Fin 2) ℝ)) := by
  change IsClosed (({γ} : Set (GL (Fin 2) ℝ)).centralizer)
  exact Set.isClosed_centralizer _

p2m_export "BandTransfer" "isClosed_centralizer"
theorem three_lt_exp_two : (3 : ℝ) < Real.exp 2 := by
  have := Real.add_one_lt_exp (two_ne_zero)
  linarith

theorem exp_two_eq : Real.exp 2 = Real.exp 1 ^ 2 := by
  rw [sq, ← Real.exp_add]; norm_num

theorem centralizerBox_subset {r θ : ℝ} (hr : 0 < r) (hs : Real.sin θ ≠ 0) :
    (Subtype.val '' {t : Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) |
        Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)}) ⊆
      (fun p : ℝ × ℝ => triU (p.1, p.1, 0) * rotGL p.2) '' (Set.Icc 1 (Real.exp 1) ×ˢ Set.Icc (-Real.pi) Real.pi) := by
  rintro g ⟨t, ht, rfl⟩
  obtain ⟨hd1, hd2⟩ := ht
  obtain ⟨h10, h11⟩ := centralizer_entries hr hs t.2
  set g00 : ℝ := ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with hg00
  set g01 : ℝ := ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hg01
  have hdet : Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = g00 ^ 2 + g01 ^ 2 := by
    rw [Matrix.det_fin_two, h10, h11]
    ring
  rw [hdet] at hd1 hd2
  set ρ : ℝ := Real.sqrt (g00 ^ 2 + g01 ^ 2) with hρ
  have hρpos : 0 < ρ := Real.sqrt_pos.2 (by linarith)
  have hρsq : ρ ^ 2 = g00 ^ 2 + g01 ^ 2 := Real.sq_sqrt (by linarith)
  have hρ1 : 1 ≤ ρ := by
    rw [hρ, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hd1
  have hρe : ρ ≤ Real.exp 1 := by
    rw [hρ]
    refine Real.sqrt_le_iff.2 ⟨(Real.exp_pos 1).le, ?_⟩
    rw [← exp_two_eq]
    exact hd2
  set a : ℝ := g00 / ρ with ha
  set b : ℝ := g01 / ρ with hb
  have hab : a ^ 2 + b ^ 2 = 1 := by
    rw [ha, hb, div_pow, div_pow, ← add_div, hρsq]
    exact div_self (by positivity)
  obtain ⟨φ, hφ, hcos, hsin⟩ := exists_angle hab
  refine ⟨(ρ, φ), ⟨⟨hρ1, hρe⟩, hφ⟩, ?_⟩
  refine Units.ext ?_
  show (triU (ρ, ρ, 0) : Matrix (Fin 2) (Fin 2) ℝ) * (rotGL φ : Matrix (Fin 2) (Fin 2) ℝ) =
    ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Matrix.eta_fin_two ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), h10, h11, triU_val, rotGL_val,
    hcos, hsin, ← hg00, ← hg01]
  simp only [max_eq_left hρ1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb] <;> field_simp

theorem isCompact_centralizerBox {r θ : ℝ} (hr : 0 < r) (hs : Real.sin θ ≠ 0) :
    IsCompact {t : Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) |
        Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} := by
  rw [Subtype.isCompact_iff]
  refine ((isCompact_Icc.prod isCompact_Icc).image ?_).of_isClosed_subset ?_ (centralizerBox_subset hr hs)
  · exact (continuous_triU.comp (Continuous.prodMk continuous_fst (Continuous.prodMk continuous_fst
      continuous_const))).mul (continuous_rotGL.comp continuous_snd)
  · have hset : Subtype.val '' {t : Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) |
          Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} =
        ((Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ))) : Set (GL (Fin 2) ℝ)) ∩
          (fun g : GL (Fin 2) ℝ => Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ)) ⁻¹' Set.Icc (1 : ℝ) (Real.exp 2) := by
      ext g
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t.2, ht⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨g, h1⟩, h2, rfl⟩
    rw [hset]
    exact (isClosed_centralizer _).inter (isClosed_Icc.preimage continuous_det_val)

theorem triU_mem_centralizer {r θ : ℝ} (hr : 0 < r) :
    triU (6 / 5, 6 / 5, 0) ∈ Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, ellipticElt_val, triU_val]
  have hm : max (6 / 5 : ℝ) 1 = 6 / 5 := max_eq_left (by norm_num)
  simp only [hm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem centralizerBox_pos {r θ : ℝ} (hr : 0 < r) (hs : Real.sin θ ≠ 0)
    [MeasurableSpace (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))]
    [BorelSpace (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))]
    (τ : Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))) [Measure.IsHaarMeasure τ] :
    0 < τ {t : Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) |
        Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} := by
  set O : Set (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ))) :=
    {t | Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Ioo (1 : ℝ) (Real.exp 2)} with hO_def
  have hO : IsOpen O := isOpen_Ioo.preimage (continuous_det_val.comp continuous_subtype_val)
  have hne : O.Nonempty := by
    refine ⟨⟨triU (6 / 5, 6 / 5, 0), triU_mem_centralizer hr⟩, ?_⟩
    show Matrix.det ((triU (6 / 5, 6 / 5, 0) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Ioo (1 : ℝ) (Real.exp 2)
    rw [triU_val, Matrix.det_fin_two_of]
    have hm : max (6 / 5 : ℝ) 1 = 6 / 5 := max_eq_left (by norm_num)
    simp only [hm]
    have := three_lt_exp_two
    constructor <;> norm_num
    linarith
  exact (hO.measure_pos τ hne).trans_le (measure_mono fun t ht => ⟨ht.1.le, ht.2.le⟩)

theorem toReal_centralizerBox_pos {r θ : ℝ} (hr : 0 < r) (hs : Real.sin θ ≠ 0)
    [MeasurableSpace (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))]
    [BorelSpace (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))]
    (τ : Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))) [Measure.IsHaarMeasure τ] :
    0 < (τ {t : Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) |
        Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)}).toReal :=
  ENNReal.toReal_pos (centralizerBox_pos hr hs τ).ne' (isCompact_centralizerBox hr hs).measure_lt_top.ne

end Torus

def ρr : (ℂ ⊗[ℝ] ℝ) ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)

theorem ρr_tmul (z : ℂ) (s : ℝ) : ρr (z ⊗ₜ s) = (s : ℂ) * z := by
  simp [ρr, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

theorem ρr_one_tmul (s : ℝ) : ρr ((1 : ℂ) ⊗ₜ s) = (s : ℂ) := by rw [ρr_tmul, mul_one]

def ρrLin : (ℂ ⊗[ℝ] ℝ) →ₗ[ℝ] ℂ where
  toFun := ρr
  map_add' := map_add ρr
  map_smul' := by
    intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z s =>
        rw [TensorProduct.RightActions.smul_def]
        simp only [TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.comm_symm_tmul,
          ρr_tmul, RingHom.id_apply, Complex.real_smul]
        push_cast
        ring
    | add x y hx hy =>
        rw [TensorProduct.RightActions.smul_def, map_add, smul_add, map_add, map_add,
          ← TensorProduct.RightActions.smul_def, ← TensorProduct.RightActions.smul_def, hx, hy, map_add, smul_add]

theorem continuous_ρr : Continuous ρr := by
  haveI := AutomorphicForm.t2Space_tensor ℝ ℂ ℝ
  exact LinearMap.continuous_of_finiteDimensional ρrLin

theorem band_iff (e : ℂ ⊗[ℝ] ℝ) :
    (∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2), e = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)) ↔
      ρr e ∈ {z : ℂ | z.im = 0 ∧ z.re ∈ Set.Icc (1 : ℝ) (Real.exp 2)} := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [ρr_one_tmul]
    exact ⟨Complex.ofReal_im d, by simpa using hd⟩
  · rintro ⟨him, hre⟩
    refine ⟨(ρr e).re, hre, ?_⟩
    apply ρr.injective
    rw [ρr_one_tmul]
    exact Complex.ext rfl (by simp [him])

theorem isClosed_bandC : IsClosed {z : ℂ | z.im = 0 ∧ z.re ∈ Set.Icc (1 : ℝ) (Real.exp 2)} :=
  (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_Icc.preimage Complex.continuous_re)

def iotaE (a : ℝ) : ℂ ⊗[ℝ] ℝ := (1 : ℂ) ⊗ₜ[ℝ] a

theorem continuous_iotaE : Continuous iotaE := by
  have : (iotaE : ℝ → ℂ ⊗[ℝ] ℝ) = algebraMap ℝ (ℂ ⊗[ℝ] ℝ) := rfl
  rw [this]
  haveI := AutomorphicForm.isTopologicalRing_tensor ℝ ℂ ℝ
  exact continuous_algebraMap ℝ (ℂ ⊗[ℝ] ℝ)

theorem continuous_toTensorGL :
    Continuous (AutomorphicForm.toTensorGL ℝ ℂ ℝ : GL (Fin 2) ℝ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor ℝ ℂ ℝ
  exact Continuous.units_map _ (continuous_id.matrix_map continuous_iotaE)

theorem toTensorGL_apply (m : GL (Fin 2) ℝ) (i j : Fin 2) :
    ((AutomorphicForm.toTensorGL ℝ ℂ ℝ m : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) i j =
      (1 : ℂ) ⊗ₜ (((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j) := rfl

theorem det_toTensorGL (t : GL (Fin 2) ℝ) :
    Matrix.det ((AutomorphicForm.toTensorGL ℝ ℂ ℝ t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
      ((1 : ℂ) ⊗ₜ[ℝ] Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) : ℂ ⊗[ℝ] ℝ) := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, toTensorGL_apply, toTensorGL_apply, toTensorGL_apply, toTensorGL_apply,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_sub]

end BandTransfer
p2m_reactivate "P2MW.S_AutomorphicForm_detBand_eq_inf_twistedCentralizer_detBand_and_pos_and_lt_top_of_coupled.BandTransfer"

end
p2m_reactivate "P2MW.S_AutomorphicForm_detBand_eq_inf_twistedCentralizer_detBand_and_pos_and_lt_top_of_coupled.BandTransfer"

open BandTransfer in
theorem solution
    (c : ℝˣ) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (u₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (τS : @Measure ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS)
    (θ₁ : ℝ) (γ₀ : GL (Fin 2) ℝ)
    (hγ₀ : ((γ₀ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (c : ℝ) • !![Real.cos θ₁, -Real.sin θ₁; Real.sin θ₁, Real.cos θ₁])
    (hreg : IsRegularSemisimple γ₀)
    (y₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hn₀ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ₀ (u₀ * δ) y₀)
    (τT : @Measure (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ₀))
    (hτT : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ₀) τT)
    (νT : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (hνT : @Measure.map _ _ (centralizerBorel ℝ γ₀) (glBorelOf ℝ) Subtype.val τT = νT)
    (τu : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ))
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u₀ * δ)))
    (hτu : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) τu)
    (hτuS : (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
       letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u₀ * δ)
       letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
           twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := borel _
       Measure.map Subtype.val τu = Measure.map Subtype.val τS))
    (hcoup : Coupled ℝ ℂ ℝ Complex.conjAe γ₀ (u₀ * δ) y₀ τT τu) :
    νT {g : GL (Fin 2) ℝ | Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} =
        τS {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) |
        ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} ∧
      0 < νT {g : GL (Fin 2) ℝ | Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} ∧ νT {g : GL (Fin 2) ℝ | Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} < ⊤ := by
  classical

  letI mG : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf _
  letI mT : MeasurableSpace (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) ℝ))) := centralizerBorel ℝ γ₀
  haveI : BorelSpace (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) ℝ))) := ⟨rfl⟩
  letI mU : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) :=
    twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u₀ * δ)
  haveI : BorelSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := ⟨rfl⟩
  letI mS : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
      twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := borel _
  haveI : BorelSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  haveI := AutomorphicForm.isTopologicalRing_tensor ℝ ℂ ℝ
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL ℝ ℂ ℝ

  set E : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := {g | ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
    Matrix.det ((g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} with hE
  have hdetc : Continuous fun g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
      ρr (Matrix.det ((g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) :=
    continuous_ρr.comp (Units.continuous_val.matrix_det)
  have hEeq : E = (fun g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
      ρr (Matrix.det ((g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)))) ⁻¹'
      {z : ℂ | z.im = 0 ∧ z.re ∈ Set.Icc (1 : ℝ) (Real.exp 2)} := by
    ext g; exact band_iff _
  have hEm : MeasurableSet E := by
    rw [hEeq]; exact (isClosed_bandC.preimage hdetc).measurableSet

  have hTm : MeasurableSet {g : GL (Fin 2) ℝ | Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} :=
    (isClosed_Icc.preimage continuous_det_val).measurableSet

  have hval : Measurable (Subtype.val : Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) ℝ)) → GL (Fin 2) ℝ) :=
    continuous_subtype_val.measurable
  have hA : νT {g : GL (Fin 2) ℝ | Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} =
      τT {t : ↥(Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) ℝ))) | Matrix.det (((t : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} := by
    rw [← hνT, Measure.map_apply hval hTm]
    rfl

  have htoT : Measurable (fun t : Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) ℝ)) =>
      AutomorphicForm.toTensorGL ℝ ℂ ℝ (t : GL (Fin 2) ℝ)) :=
    (continuous_toTensorGL.comp continuous_subtype_val).measurable
  have hconj : Measurable (fun t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ) =>
      y₀⁻¹ * (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * y₀) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hB : τT {t : ↥(Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) ℝ))) | Matrix.det (((t : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} =
      τu {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) | ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det (((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} := by
    have h1 := congrArg (fun μ : Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) => μ E) hcoup
    rw [Measure.map_apply hconj hEm, Measure.map_apply htoT hEm] at h1

    have e1 : (fun t : Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) ℝ)) =>
        AutomorphicForm.toTensorGL ℝ ℂ ℝ (t : GL (Fin 2) ℝ)) ⁻¹' E =
        {t : ↥(Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) ℝ))) | Matrix.det (((t : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} := by
      ext t
      simp only [Set.mem_preimage, hE, Set.mem_setOf_eq, det_toTensorGL]
      constructor
      · rintro ⟨d, hd, he⟩
        have := congrArg ρr he
        rw [ρr_one_tmul, ρr_one_tmul, Complex.ofReal_inj] at this
        rw [this]; exact hd
      · intro h; exact ⟨_, h, rfl⟩
    have e2 : (fun t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ) =>
        y₀⁻¹ * (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * y₀) ⁻¹' E =
        {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) | ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
          Matrix.det (((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} := by
      ext t
      simp only [Set.mem_preimage, hE, Set.mem_setOf_eq, Units.val_mul, Matrix.det_mul]
      rw [show Matrix.det (((y₀⁻¹ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) *
          Matrix.det (((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) *
          Matrix.det (((y₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
          Matrix.det (((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) by
        rw [mul_comm, ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
          one_mul]]
    rw [e1, e2] at h1
    exact h1.symm

  have hvalU : Measurable (Subtype.val : twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ) → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
    continuous_subtype_val.measurable
  have hvalS : Measurable (Subtype.val : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
      twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
    continuous_subtype_val.measurable
  have hC : τu {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) | ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det (((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} =
      τS {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) |
        ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} := by
    have h1 := congrArg (fun μ : Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) => μ E) hτuS
    rw [Measure.map_apply hvalU hEm, Measure.map_apply hvalS hEm] at h1
    exact h1

  have hpf : 0 < τT {t : ↥(Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) ℝ))) | Matrix.det (((t : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} ∧
      τT {t : ↥(Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) ℝ))) | Matrix.det (((t : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} < ⊤ := by

    have key : ∀ (r θ' : ℝ) (hr : 0 < r), Real.sin θ' ≠ 0 → ∀ (g : GL (Fin 2) ℝ), ellipticElt r θ' hr = g →
        ∀ (τ : @Measure (Subgroup.centralizer ({g} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ g)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ g) τ →
          0 < τ {t : ↥(Subgroup.centralizer ({g} : Set (GL (Fin 2) ℝ))) | Matrix.det (((t : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} ∧
            τ {t : ↥(Subgroup.centralizer ({g} : Set (GL (Fin 2) ℝ))) | Matrix.det (((t : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} < ⊤ := by
      intro r θ' hr hs g hg τ hτ
      subst hg
      letI : MeasurableSpace (Subgroup.centralizer ({ellipticElt r θ' hr} : Set (GL (Fin 2) ℝ))) :=
        centralizerBorel ℝ (ellipticElt r θ' hr)
      haveI : BorelSpace (Subgroup.centralizer ({ellipticElt r θ' hr} : Set (GL (Fin 2) ℝ))) := ⟨rfl⟩
      haveI : Measure.IsHaarMeasure τ := hτ
      exact ⟨centralizerBox_pos hr hs τ, (isCompact_centralizerBox hr hs).measure_lt_top⟩
    have hsin : Real.sin θ₁ ≠ 0 := by
      intro h0
      rw [isRegularSemisimple_iff_ne_zero, hγ₀] at hreg
      apply hreg
      simp [Matrix.trace_fin_two, Matrix.det_fin_two, h0]
      ring
    rcases lt_or_gt_of_ne c.ne_zero with hneg | hpos
    · have hr : 0 < -(c : ℝ) := neg_pos.2 hneg
      have hs' : Real.sin (Real.pi - θ₁) ≠ 0 := by rwa [Real.sin_pi_sub]
      have e : ellipticElt (-(c : ℝ)) (Real.pi - θ₁) hr = γ₀ := by
        refine Units.ext ?_
        rw [ellipticElt_val, hγ₀, Real.cos_pi_sub, Real.sin_pi_sub]
        ext i j
        fin_cases i <;> fin_cases j <;> simp <;> ring
      exact key _ _ hr hs' γ₀ e τT hτT
    · have hs' : Real.sin (-θ₁) ≠ 0 := by rwa [Real.sin_neg, neg_ne_zero]
      have e : ellipticElt (c : ℝ) (-θ₁) hpos = γ₀ := by
        refine Units.ext ?_
        rw [ellipticElt_val, hγ₀, Real.cos_neg, Real.sin_neg]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      exact key _ _ hpos hs' γ₀ e τT hτT
  refine ⟨by rw [hA, hB, hC], by rw [hA]; exact hpf.1, by rw [hA]; exact hpf.2⟩

end S_AutomorphicForm_detBand_eq_inf_twistedCentralizer_detBand_and_pos_and_lt_top_of_coupled
end P2MW
export P2MW.S_AutomorphicForm_detBand_eq_inf_twistedCentralizer_detBand_and_pos_and_lt_top_of_coupled (solution)
