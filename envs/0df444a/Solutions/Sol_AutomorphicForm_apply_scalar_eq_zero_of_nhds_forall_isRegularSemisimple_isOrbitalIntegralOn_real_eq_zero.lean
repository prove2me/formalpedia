-- Prove2me | solution 1 for AutomorphicForm.apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_real_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/1b0e6afe-42b4-5e5b-b0bb-6a022d29b8be

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Theorems.Thm_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div
import Theorems.Thm_AutomorphicForm_GL2Real_exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_isOrbitalIntegralOn_slice_of_isRegularSemisimple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_real_eq_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Topology AutomorphicForm AutomorphicForm.GL2Real
open scoped ContDiff

noncomputable section

namespace P2mHCScalarR

abbrev Ent : Type := Fin 2 → Fin 2 → ℝ

section FromF

variable {f : GL (Fin 2) ℝ → ℂ} {Φ : Ent → ℂ}
  (hfΦ : ∀ g, f g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) (hfc : HasCompactSupport f)

def entries (g : GL (Fin 2) ℝ) : Ent := fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j

theorem continuous_entries : Continuous entries :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp ((continuous_apply i).comp (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℝ)))

theorem continuous_entry (i j : Fin 2) : Continuous fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j :=
  (continuous_apply j).comp ((continuous_apply i).comp (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℝ)))

def Kf (f : GL (Fin 2) ℝ → ℂ) : Set Ent := entries '' tsupport f

include hfc in
theorem isCompact_Kf : IsCompact (Kf f) := hfc.isCompact.image continuous_entries

omit hfΦ hfc in
theorem det_ne_zero_of_mem_Kf {E : Ent} (hE : E ∈ Kf f) : Matrix.det (Matrix.of E) ≠ 0 := by
  obtain ⟨g, -, rfl⟩ := hE
  show Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero

include hfΦ in
theorem apply_eq_zero_of_det_ne_zero_of_notMem {E : Ent} (hdet : Matrix.det (Matrix.of E) ≠ 0) (hE : E ∉ Kf f) :
    Φ E = 0 := by
  set g : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of E) hdet with hg
  have hval : entries g = E := rfl
  have hfg : f g = Φ E := hfΦ g
  have hg' : g ∉ tsupport f := fun h => hE ⟨g, h, hval⟩
  rw [← hfg]
  exact image_eq_zero_of_notMem_tsupport hg'

include hfΦ hfc in
theorem apply_eq_zero_of_notMem (hΦ : Continuous Φ) {E : Ent} (hE : E ∉ Kf f) : Φ E = 0 := by
  by_cases hdet : Matrix.det (Matrix.of E) ≠ 0
  · exact apply_eq_zero_of_det_ne_zero_of_notMem hfΦ hdet hE
  push Not at hdet

  set Et : ℝ → Ent := fun t => fun i j => E i j + t * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j with hEt
  have hcont : Continuous Et := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [hEt]
    fun_prop
  have h0 : Et 0 = E := by
    funext i j
    simp [hEt]
  set tr : ℝ := E 0 0 + E 1 1 with htr
  have hdet0 : E 0 0 * E 1 1 - E 0 1 * E 1 0 = 0 := by
    rw [Matrix.det_fin_two] at hdet
    simpa using hdet
  have hdetf : ∀ t : ℝ, Matrix.det (Matrix.of (Et t)) = t * (t + tr) := by
    intro t
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, hEt, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), mul_one, mul_zero, add_zero, htr]
    linear_combination hdet0
  set δ : ℝ := if tr = 0 then 1 else |tr| with hδ
  have hδpos : 0 < δ := by
    simp only [hδ]
    split_ifs with h
    · exact one_pos
    · exact abs_pos.2 h
  have hne : ∀ t : ℝ, 0 < t → t < δ → Matrix.det (Matrix.of (Et t)) ≠ 0 := by
    intro t ht htδ
    rw [hdetf]
    refine mul_ne_zero ht.ne' fun h => ?_
    have htr' : tr = -t := by linarith
    by_cases h0 : tr = 0
    · rw [h0] at htr'
      linarith
    · have hn : |tr| = t := by rw [htr', abs_neg, abs_of_pos ht]
      simp only [hδ, if_neg h0] at htδ
      linarith
  have hK : IsClosed (Kf f) := (isCompact_Kf hfc).isClosed
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), Et t ∉ Kf f := by
    have ht : Tendsto Et (𝓝[>] 0) (𝓝 E) := by
      rw [← h0]
      exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    exact ht.eventually (hK.isOpen_compl.mem_nhds hE)
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), Matrix.det (Matrix.of (Et t)) ≠ 0 := by
    filter_upwards [Ioo_mem_nhdsGT hδpos] with t ht using hne t ht.1 ht.2
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), Φ (Et t) = 0 := by
    filter_upwards [hev1, hev2] with t h1 h2 using apply_eq_zero_of_det_ne_zero_of_notMem hfΦ h2 h1
  have hlim : Tendsto (fun t => Φ (Et t)) (𝓝[>] 0) (𝓝 (Φ E)) := by
    rw [← h0]
    exact ((hΦ.comp hcont).tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim0 : Tendsto (fun t => Φ (Et t)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm)
  exact tendsto_nhds_unique hlim hlim0

include hfΦ hfc in
theorem hasCompactSupport_of_entries (hΦ : Continuous Φ) : HasCompactSupport Φ :=
  HasCompactSupport.intro (isCompact_Kf hfc) fun E hE => apply_eq_zero_of_notMem hfΦ hfc hΦ hE

include hfΦ hfc in
theorem tsupport_subset_Kf (hΦ : Continuous Φ) : tsupport Φ ⊆ Kf f :=
  closure_minimal (fun E hE => by_contra fun h => hE (apply_eq_zero_of_notMem hfΦ hfc hΦ h))
    (isCompact_Kf hfc).isClosed

include hfΦ hfc in
theorem tsupport_subset_isUnit (hΦ : Continuous Φ) : tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} :=
  fun E hE => isUnit_iff_ne_zero.2 (det_ne_zero_of_mem_Kf (tsupport_subset_Kf hfΦ hfc hΦ hE))

include hfΦ in
theorem continuous_of_entries (hΦ : Continuous Φ) : Continuous f := by
  have : f = Φ ∘ entries := funext fun g => hfΦ g
  rw [this]
  exact hΦ.comp continuous_entries

end FromF

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

section BoxS

def boxS : Set (GL (Fin 2) ℝ) :=
  {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)}

def paramBox : Set ((ℝ × ℝ × ℝ) × ℝ) :=
  (Set.Icc 1 (Real.exp 1) ×ˢ Set.Icc 1 (Real.exp 1) ×ˢ Set.Icc 0 1) ×ˢ Set.Icc (-Real.pi) Real.pi

theorem isCompact_paramBox : IsCompact paramBox :=
  ((isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod isCompact_Icc)

def chart (p : (ℝ × ℝ × ℝ) × ℝ) : GL (Fin 2) ℝ := triU p.1 * rotGL p.2

theorem continuous_chart : Continuous chart :=
  (continuous_triU.comp continuous_fst).mul (continuous_rotGL.comp continuous_snd)

theorem boxS_subset : boxS ⊆ chart '' paramBox := by
  rintro g ⟨b₁, hb₁, b₂, hb₂, x, hx, k, hg⟩
  have hk := entries_of_mem_rowIsometrySubgroup₀ k.2
  obtain ⟨h10, h11, hsq⟩ := hk
  obtain ⟨θ, hθ, hcos, hsin⟩ := exists_angle hsq
  refine ⟨((b₁, b₂, x), θ), ⟨⟨hb₁, hb₂, hx⟩, hθ⟩, ?_⟩
  refine Units.ext ?_
  show (triU (b₁, b₂, x) : Matrix (Fin 2) (Fin 2) ℝ) * (rotGL θ : Matrix (Fin 2) (Fin 2) ℝ) =
    (g : Matrix (Fin 2) (Fin 2) ℝ)
  rw [hg, Matrix.eta_fin_two ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), h10, h11, triU_val, rotGL_val,
    hcos, hsin]
  simp only [max_eq_left hb₁.1, max_eq_left hb₂.1]

theorem isCompact_chart_paramBox : IsCompact (chart '' paramBox) := isCompact_paramBox.image continuous_chart

def nf (g : GL (Fin 2) ℝ) : ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2

theorem nf_pos (g : GL (Fin 2) ℝ) : 0 < nf g := by
  have hdet := det_val_ne_zero g
  rw [Matrix.det_fin_two] at hdet
  by_contra h
  push Not at h
  have ha : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 = 0 := by
    unfold nf at h
    nlinarith [sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0), sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1)]
  have hb : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2 = 0 := by
    unfold nf at h
    nlinarith [sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0), sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1)]
  have ha' := pow_eq_zero_iff two_ne_zero |>.1 ha
  have hb' := pow_eq_zero_iff two_ne_zero |>.1 hb
  apply hdet
  rw [ha', hb']
  ring

theorem continuous_nf : Continuous nf :=
  ((continuous_entry 1 0).pow 2).add ((continuous_entry 1 1).pow 2)

def b2f (g : GL (Fin 2) ℝ) : ℝ := Real.sqrt (nf g)

def b1f (g : GL (Fin 2) ℝ) : ℝ := Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) / b2f g

def xf (g : GL (Fin 2) ℝ) : ℝ :=
  ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 +
      (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) /
    Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ)

theorem b2f_pos (g : GL (Fin 2) ℝ) : 0 < b2f g := Real.sqrt_pos.2 (nf_pos g)

theorem b2f_sq (g : GL (Fin 2) ℝ) : b2f g ^ 2 = nf g := Real.sq_sqrt (nf_pos g).le

theorem continuous_b2f : Continuous b2f := continuous_nf.sqrt

theorem continuous_b1f : Continuous b1f := continuous_det_val.div continuous_b2f fun g => (b2f_pos g).ne'

theorem continuous_xf : Continuous xf :=
  (((continuous_entry 0 0).mul (continuous_entry 1 0)).add ((continuous_entry 0 1).mul (continuous_entry 1 1))).div
    continuous_det_val det_val_ne_zero

def openV : Set (GL (Fin 2) ℝ) :=
  {g | 0 < Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ)} ∩ b2f ⁻¹' Set.Ioo 1 (Real.exp 1) ∩
    b1f ⁻¹' Set.Ioo 1 (Real.exp 1) ∩ xf ⁻¹' Set.Ioo 0 1

theorem isOpen_openV : IsOpen openV :=
  (((isOpen_lt continuous_const continuous_det_val).inter (isOpen_Ioo.preimage continuous_b2f)).inter
    (isOpen_Ioo.preimage continuous_b1f)).inter (isOpen_Ioo.preimage continuous_xf)

theorem two_lt_exp_one : (2 : ℝ) < Real.exp 1 := by
  have := Real.add_one_lt_exp (one_ne_zero)
  linarith

theorem openV_nonempty : openV.Nonempty := by
  refine ⟨triU (2, 2, 1 / 2), ?_⟩
  have hm : max (2 : ℝ) 1 = 2 := max_eq_left (by norm_num)
  have hval : ((triU (2, 2, 1 / 2) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![2, 1; 0, 2] := by
    rw [triU_val]
    simp only [hm]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hdet : Matrix.det ((triU (2, 2, 1 / 2) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 4 := by
    rw [hval, Matrix.det_fin_two_of]; norm_num
  have hnf : nf (triU (2, 2, 1 / 2)) = 4 := by
    unfold nf; rw [hval]; norm_num
  have hb2 : b2f (triU (2, 2, 1 / 2)) = 2 := by
    unfold b2f; rw [hnf, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hb1 : b1f (triU (2, 2, 1 / 2)) = 2 := by
    unfold b1f; rw [hdet, hb2]; norm_num
  have hx : xf (triU (2, 2, 1 / 2)) = 1 / 2 := by
    unfold xf; rw [hdet, hval]; norm_num
  have he := two_lt_exp_one
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · show 0 < Matrix.det ((triU (2, 2, 1 / 2) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    rw [hdet]; norm_num
  · show b2f (triU (2, 2, 1 / 2)) ∈ Set.Ioo 1 (Real.exp 1)
    rw [hb2]; exact ⟨by norm_num, he⟩
  · show b1f (triU (2, 2, 1 / 2)) ∈ Set.Ioo 1 (Real.exp 1)
    rw [hb1]; exact ⟨by norm_num, he⟩
  · show xf (triU (2, 2, 1 / 2)) ∈ Set.Ioo 0 1
    rw [hx]; norm_num

theorem openV_subset_boxS : openV ⊆ boxS := by
  rintro g ⟨⟨⟨hd, hb2⟩, hb1⟩, hx⟩
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hd hb2 hb1 hx

  set g00 : ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with hg00
  set g01 : ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hg01
  set g10 : ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 with hg10
  set g11 : ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 with hg11
  set d : ℝ := Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) with hd_def
  have hdeq : d = g00 * g11 - g01 * g10 := by rw [hd_def, Matrix.det_fin_two]
  set B : ℝ := b2f g with hB_def
  have hBpos : 0 < B := b2f_pos g
  have hBsq : B ^ 2 = g10 ^ 2 + g11 ^ 2 := b2f_sq g
  have hB0 : B ≠ 0 := hBpos.ne'
  have hd0 : d ≠ 0 := hd.ne'
  have hb1eq : b1f g = d / B := rfl
  have hxeq : xf g = (g00 * g10 + g01 * g11) / d := rfl

  set a : ℝ := g11 / B with ha
  set b : ℝ := -g10 / B with hb
  have hab : a ^ 2 + b ^ 2 = 1 := by
    rw [ha, hb, div_pow, div_pow, ← add_div, hBsq, neg_sq]
    rw [add_comm]
    exact div_self (by rw [← hBsq]; positivity)
  refine ⟨b1f g, ⟨hb1.1.le, hb1.2.le⟩, B, ⟨hb2.1.le, hb2.2.le⟩, xf g, ⟨hx.1.le, hx.2.le⟩,
    ⟨rotAB a b hab, rotAB_mem a b hab⟩, ?_⟩
  show (g : Matrix (Fin 2) (Fin 2) ℝ) = !![b1f g, b1f g * xf g; 0, B] * !![a, b; -b, a]
  rw [hb1eq, hxeq]
  ext i j
  fin_cases i <;> fin_cases j
  ·
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [← hg00, ha, hb]
    field_simp
    rw [hdeq]
    linear_combination g00 * hBsq
  ·
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [← hg01, ha, hb]
    field_simp
    rw [hdeq]
    linear_combination g01 * hBsq
  ·
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [← hg10, hb]
    field_simp
  ·
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [← hg11, ha]
    field_simp

variable [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)]
  (μ : Measure (GL (Fin 2) ℝ)) [Measure.IsHaarMeasure μ]

theorem boxS_lt_top : μ boxS < ⊤ :=
  lt_of_le_of_lt (measure_mono boxS_subset) isCompact_chart_paramBox.measure_lt_top

theorem boxS_pos : 0 < μ boxS :=
  (isOpen_openV.measure_pos μ openV_nonempty).trans_le (measure_mono openV_subset_boxS)

theorem toReal_boxS_pos : 0 < (μ boxS).toReal :=
  ENNReal.toReal_pos (boxS_pos μ).ne' (boxS_lt_top μ).ne

end BoxS

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

private theorem _root_.P2mHCScalarR.isClosed_centralizer (γ : GL (Fin 2) ℝ) :
    IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) : Set (GL (Fin 2) ℝ)) := by
  change IsClosed (({γ} : Set (GL (Fin 2) ℝ)).centralizer)
  exact Set.isClosed_centralizer _

p2m_export "P2mHCScalarR" "isClosed_centralizer"
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

section Neg

theorem continuous_neg_GL : Continuous fun u : GL (Fin 2) ℝ => -u := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℝ)).neg.congr fun u => rfl
  · exact (Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) ℝ)).neg.congr fun u => rfl

def negGL : GL (Fin 2) ℝ ≃ₜ GL (Fin 2) ℝ where
  toEquiv := Equiv.neg (GL (Fin 2) ℝ)
  continuous_toFun := continuous_neg_GL
  continuous_invFun := continuous_neg_GL

theorem negGL_apply (g : GL (Fin 2) ℝ) : negGL g = -g := rfl

theorem haar_transport {G : Type} [Group G] [TopologicalSpace G] (H H' : Subgroup G) (h : H = H')
    (τ' : @Measure H (borel H)) (hτ' : @Measure.IsHaarMeasure H _ _ (borel H) τ') :
    ∃ τ : @Measure H' (borel H'), @Measure.IsHaarMeasure H' _ _ (borel H') τ ∧
      ∀ (w : G → ℝ) (x : G),
        @integral H' ℝ _ _ (borel H') τ (fun t => w ((t : G) * x)) =
          @integral H ℝ _ _ (borel H) τ' (fun t => w ((t : G) * x)) := by
  subst h
  exact ⟨τ', hτ', fun _ _ => rfl⟩

theorem neg_scalar_neg (cu : ℝˣ) :
    -(Matrix.GeneralLinearGroup.scalar (Fin 2) (-cu)) = Matrix.GeneralLinearGroup.scalar (Fin 2) cu := by
  refine Units.ext ?_
  rw [Units.val_neg, val_scalar_two, val_scalar_two, Units.val_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem hvan_neg (μ : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ)) (f : GL (Fin 2) ℝ → ℂ) (cu : ℝˣ)
    (hvan : ∃ U ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) cu),
      ∀ γ ∈ U, Matrix.GeneralLinearGroup.det γ = cu ^ 2 → IsRegularSemisimple γ →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
            ∀ I : ℂ, IsOrbitalIntegralOn ℝ μ γ τ f I → I = 0) :
    ∃ U ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) (-cu)),
      ∀ γ ∈ U, Matrix.GeneralLinearGroup.det γ = (-cu) ^ 2 → IsRegularSemisimple γ →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
            ∀ I : ℂ, IsOrbitalIntegralOn ℝ μ γ τ (fun g => f (-g)) I → I = 0 := by
  obtain ⟨U, hU, hvanU⟩ := hvan
  refine ⟨negGL ⁻¹' U, ?_, ?_⟩
  · apply negGL.continuous.continuousAt.preimage_mem_nhds
    rw [negGL_apply, neg_scalar_neg]
    exact hU
  · intro γ' hγ' hdet' hreg' τ' hτ' I hI
    have hγU : -γ' ∈ U := hγ'
    have hdet : Matrix.GeneralLinearGroup.det (-γ') = cu ^ 2 := by
      rw [← neg_sq cu, ← hdet']
      refine Units.ext ?_
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, Units.val_neg,
        Matrix.det_neg, Fintype.card_fin]
      norm_num
    have hreg : IsRegularSemisimple (-γ') := by
      rw [isRegularSemisimple_iff_ne_zero] at hreg' ⊢
      rw [Units.val_neg, Matrix.trace_neg, Matrix.det_neg, Fintype.card_fin, neg_sq]
      norm_num
      exact hreg'
    have hH : Subgroup.centralizer ({γ'} : Set (GL (Fin 2) ℝ)) = Subgroup.centralizer ({-γ'} : Set (GL (Fin 2) ℝ)) := by
      ext g
      simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
      constructor
      · intro h
        rw [neg_mul, mul_neg, h]
      · intro h
        rw [neg_mul, mul_neg] at h
        exact neg_injective h
    obtain ⟨τ, hτ, hτeq⟩ := haar_transport _ _ hH τ' hτ'
    obtain ⟨w, ⟨hw0, hwm, hwc, hw1⟩, hIw⟩ := hI
    have hconj : ∀ x : GL (Fin 2) ℝ, -(x⁻¹ * γ' * x) = x⁻¹ * (-γ') * x := fun x => by
      rw [mul_neg, neg_mul]
    have hOI : IsOrbitalIntegralOn ℝ μ (-γ') τ f I := by
      refine ⟨w, ⟨hw0, hwm, hwc, fun x hx => ?_⟩, ?_⟩
      · rw [hτeq]
        apply hw1 x
        show f (-(x⁻¹ * γ' * x)) ≠ 0
        rw [hconj]
        exact hx
      · rw [hIw]
        congr 1
        funext x
        show f (-(x⁻¹ * γ' * x)) * (w x : ℂ) = f (x⁻¹ * (-γ') * x) * (w x : ℂ)
        rw [hconj]
    exact hvanU (-γ') hγU hdet hreg τ hτ I hOI

end Neg

section Main

theorem main_pos
    (μ : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μ)
    (f : GL (Fin 2) ℝ → ℂ)
    (hf : (∃ Φ : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, f g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
    (cu : ℝˣ) (hcu : 0 < (cu : ℝ))
    (hvan : ∃ U ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) cu),
      ∀ γ ∈ U, Matrix.GeneralLinearGroup.det γ = cu ^ 2 → IsRegularSemisimple γ →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
            ∀ I : ℂ, IsOrbitalIntegralOn ℝ μ γ τ f I → I = 0) :
    f (Matrix.GeneralLinearGroup.scalar (Fin 2) cu) = 0 := by
  obtain ⟨⟨Φ, hΦs, hfΦ⟩, hfc⟩ := hf
  set r : ℝ := (cu : ℝ) with hr_def
  have hr : 0 < r := hcu

  have hΦc : HasCompactSupport Φ := hasCompactSupport_of_entries hfΦ hfc hΦs.continuous
  have hΦU : tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := tsupport_subset_isUnit hfΦ hfc hΦs.continuous
  have hfcont : Continuous f := continuous_of_entries hfΦ hΦs.continuous

  set Φ' : Ent × PUnit → ℂ := fun q => Φ q.1 with hΦ'_def
  have hΦ's : ContDiff ℝ (⊤ : ℕ∞) Φ' := hΦs.comp contDiff_fst
  have hsub : Function.support Φ' ⊆ tsupport Φ ×ˢ (Set.univ : Set PUnit) := fun q hq =>
    ⟨subset_tsupport _ (Function.mem_support.2 hq), Set.mem_univ _⟩
  have hΦ'c : HasCompactSupport Φ' :=
    HasCompactSupport.intro (hΦc.isCompact.prod isCompact_univ) fun q hq =>
      Function.notMem_support.1 fun h => hq (hsub h)
  have hΦ'U : tsupport Φ' ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} := fun q hq =>
    hΦU (closure_minimal hsub (hΦc.isCompact.prod isCompact_univ).isClosed hq).1
  have hfeq : entrySlice Φ' PUnit.unit = f := funext fun g => (hfΦ g).symm

  obtain ⟨C, hC, hjump⟩ :=
    AutomorphicForm.GL2Real.exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi
  obtain ⟨L, hL, hD⟩ := hjump PUnit Φ' hΦ's hΦ'c hΦ'U PUnit.unit r hr

  obtain ⟨U, hU, hvanU⟩ := hvan
  have hpre : (fun θ => ellipticElt r θ hr) ⁻¹' U ∈ 𝓝 (0 : ℝ) := by
    have ht := (continuous_ellipticElt r hr).tendsto 0
    rw [ellipticElt_zero r hr cu rfl] at ht
    exact ht hU

  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  haveI : Measure.IsHaarMeasure μ := hμ
  haveI := locallyCompactSpace_GL
  have hSpos : 0 < (μ boxS).toReal := toReal_boxS_pos μ

  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ellipticTransform f r θ = 0 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hpre, Ioo_mem_nhdsGT Real.pi_pos] with θ hθU hθπ
    have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2).ne'
    set γ : GL (Fin 2) ℝ := ellipticElt r θ hr with hγ_def
    have hγU : γ ∈ U := hθU
    have hγdet : Matrix.GeneralLinearGroup.det γ = cu ^ 2 := det_ellipticElt r θ hr cu rfl
    have hγreg : IsRegularSemisimple γ := isRegularSemisimple_ellipticElt hr hs

    letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) := centralizerBorel ℝ γ
    haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) := ⟨rfl⟩
    haveI : LocallyCompactSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) :=
      (isClosed_centralizer γ).isClosedEmbedding_subtypeVal.locallyCompactSpace
    set τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) := Measure.haar with hτ_def
    have hτ : Measure.IsHaarMeasure τ := by rw [hτ_def]; infer_instance

    obtain ⟨gv, -, -, hg⟩ :=
      AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isOrbitalIntegralOn_slice_of_isRegularSemisimple ℝ PUnit
        μ hμ γ hγreg τ hτ Φ' hΦ's hΦ'c hΦ'U
    have hex : IsOrbitalIntegralOn ℝ μ γ τ f (gv PUnit.unit) := by
      rw [← hfeq]
      exact (hg PUnit.unit).1
    have hI0 : gv PUnit.unit = 0 := hvanU γ hγU hγdet hγreg τ hτ _ hex

    have hb := (AutomorphicForm.GL2Real.orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div f hfcont
      hfc μ hμ).2 r θ hr hs τ hτ _ hex
    rw [hI0] at hb
    have hτpos := toReal_centralizerBox_pos hr hs τ
    have hK : (((μ boxS).toReal /
        (τ {t : Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) |
          Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)}).toReal : ℝ) : ℂ) ≠
        0 := by
      exact_mod_cast (div_pos hSpos hτpos).ne'
    have hden : (4 : ℂ) * (Real.sin θ : ℂ) ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.2 hs))
    rcases div_eq_zero_iff.1 hb.symm with h | h
    · exact (mul_eq_zero.1 h).resolve_left hK
    · exact absurd h hden

  have hev' : ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      ellipticTransform (entrySlice Φ' PUnit.unit) r θ / (2 * Real.sin θ : ℂ) = 0 := by
    filter_upwards [hev] with θ hθ
    rw [hfeq, hθ, zero_div]
  have hL0 : L = 0 :=
    tendsto_nhds_unique hL (tendsto_const_nhds.congr' (hev'.mono fun θ h => h.symm))
  have hD0 : Tendsto (fun θ : ℝ =>
      (ellipticTransform (entrySlice Φ' PUnit.unit) r θ / (2 * Real.sin θ : ℂ) - L) / (θ : ℂ)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (hev'.mono fun θ h => by
      show (0 : ℂ) = (ellipticTransform (entrySlice Φ' PUnit.unit) r θ / (2 * Real.sin θ : ℂ) - L) / (θ : ℂ)
      rw [h, hL0, sub_zero, zero_div])
  have hCΦ : (C : ℂ) * Φ' (Matrix.of.symm (r • (1 : Matrix (Fin 2) (Fin 2) ℝ)), PUnit.unit) = 0 :=
    tendsto_nhds_unique hD hD0
  have hΦ0 : Φ (Matrix.of.symm (r • (1 : Matrix (Fin 2) (Fin 2) ℝ))) = 0 :=
    (mul_eq_zero.1 hCΦ).resolve_left (Complex.ofReal_ne_zero.2 hC)
  have harg : (fun i j => ((Matrix.GeneralLinearGroup.scalar (Fin 2) cu : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j) =
      Matrix.of.symm (r • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
    rw [val_scalar_two]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [hr_def]
  rw [hfΦ, harg]
  exact hΦ0

theorem main
    (μ : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μ)
    (f : GL (Fin 2) ℝ → ℂ)
    (hf : (∃ Φ : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, f g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
    (cu : ℝˣ)
    (hvan : ∃ U ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) cu),
      ∀ γ ∈ U, Matrix.GeneralLinearGroup.det γ = cu ^ 2 → IsRegularSemisimple γ →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
            ∀ I : ℂ, IsOrbitalIntegralOn ℝ μ γ τ f I → I = 0) :
    f (Matrix.GeneralLinearGroup.scalar (Fin 2) cu) = 0 := by
  rcases lt_or_gt_of_ne cu.ne_zero with hneg | hpos
  ·
    obtain ⟨⟨Φ, hΦs, hfΦ⟩, hfc⟩ := hf
    have hf' : (∃ Φ' : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ' ∧
        ∀ g, (fun g : GL (Fin 2) ℝ => f (-g)) g = Φ' (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
        HasCompactSupport (fun g : GL (Fin 2) ℝ => f (-g)) := by
      refine ⟨⟨fun E => Φ (-E), hΦs.comp contDiff_neg, fun g => ?_⟩, ?_⟩
      · show f (-g) = Φ (-(fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j))
        rw [hfΦ]
        rfl
      · exact hfc.comp_homeomorph negGL
    have hcu' : 0 < ((-cu : ℝˣ) : ℝ) := by
      rw [Units.val_neg]
      exact neg_pos.2 hneg
    have h := main_pos μ hμ (fun g => f (-g)) hf' (-cu) hcu' (hvan_neg μ f cu hvan)

    have h' : f (-(Matrix.GeneralLinearGroup.scalar (Fin 2) (-cu))) = 0 := h
    rwa [neg_scalar_neg] at h'
  · exact main_pos μ hμ f hf cu hpos hvan

end Main

end P2mHCScalarR
p2m_reactivate "P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_real_eq_zero.P2mHCScalarR"

end
p2m_reactivate "P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_real_eq_zero.P2mHCScalarR"

open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (μ : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μ)
    (f : GL (Fin 2) ℝ → ℂ)
    (hf : (∃ Φ : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, f g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
    (c : ℝˣ)
    (hvan : ∃ U ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ γ ∈ U, Matrix.GeneralLinearGroup.det γ = c ^ 2 → IsRegularSemisimple γ →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
            ∀ I : ℂ, IsOrbitalIntegralOn ℝ μ γ τ f I → I = 0) :
    f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0 :=
  P2mHCScalarR.main μ hμ f hf c hvan

end S_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_real_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_real_eq_zero (solution)
