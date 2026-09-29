-- Prove2me | solution 1 for AutomorphicForm.exists_smooth_hasCompactSupport_forall_nhds_one_apply_conj_eq_apply_conj_mul_scalar_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ba614997-0ffc-5bba-81c2-bcc58b73221f

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_smooth_hasCompactSupport_forall_nhds_one_apply_conj_eq_apply_conj_mul_scalar_sq

set_option autoImplicit false

open MeasureTheory AutomorphicForm Topology Filter Set

noncomputable section

namespace SqCutoff

local notation "M2" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G2" => GL (Fin 2) ℝ

def bump2 : ContDiffBump (2 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
def bump1 : ContDiffBump (1 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩

def cut (m : M2) : ℝ := (bump2 : ℝ → ℝ) (Matrix.trace m) * (bump1 : ℝ → ℝ) m.det

theorem cut_conj (h t : G2) : cut ((h⁻¹ * t * h : G2) : M2) = cut (t : M2) := by
  simp only [cut, Units.val_mul]
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel, one_mul]
  congr 1
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det _) (Matrix.det (t : M2)), mul_assoc,
    ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, mul_one]

theorem cut_eq_one {t : G2} (h1 : dist (Matrix.trace (t : M2)) 2 ≤ 1/4) (h2 : dist ((t : M2).det) 1 ≤ 1/4) :
    cut (t : M2) = 1 := by
  simp only [cut]
  rw [bump2.one_of_mem_closedBall (Metric.mem_closedBall.mpr h1),
    bump1.one_of_mem_closedBall (Metric.mem_closedBall.mpr h2), one_mul]

theorem cut_ne_zero {m : M2} (h : cut m ≠ 0) :
    dist (Matrix.trace m) 2 < 1/2 ∧ dist m.det 1 < 1/2 := by
  simp only [cut] at h
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp h
  have ha' : Matrix.trace m ∈ Function.support (bump2 : ℝ → ℝ) := ha
  have hb' : m.det ∈ Function.support (bump1 : ℝ → ℝ) := hb
  rw [ContDiffBump.support_eq, Metric.mem_ball] at ha' hb'
  exact ⟨ha', hb'⟩

theorem contDiff_entry (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) fun m : Fin 2 → Fin 2 → ℝ => m i j :=
  (contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 2 → ℝ) i)

theorem contDiff_cut : ContDiff ℝ (⊤ : ℕ∞) fun m : Fin 2 → Fin 2 → ℝ => cut m := by
  have htr : ContDiff ℝ (⊤ : ℕ∞) fun m : Fin 2 → Fin 2 → ℝ => Matrix.trace (Matrix.of.symm.symm m) := by
    have : (fun m : Fin 2 → Fin 2 → ℝ => Matrix.trace (Matrix.of.symm.symm m)) = fun m => m 0 0 + m 1 1 := by
      funext m; exact Matrix.trace_fin_two _
    rw [this]; exact (contDiff_entry 0 0).add (contDiff_entry 1 1)
  have hdet : ContDiff ℝ (⊤ : ℕ∞) fun m : Fin 2 → Fin 2 → ℝ => Matrix.det (Matrix.of.symm.symm m) := by
    have : (fun m : Fin 2 → Fin 2 → ℝ => Matrix.det (Matrix.of.symm.symm m)) = fun m => m 0 0 * m 1 1 - m 0 1 * m 1 0 := by
      funext m; exact Matrix.det_fin_two _
    rw [this]; exact ((contDiff_entry 0 0).mul (contDiff_entry 1 1)).sub ((contDiff_entry 0 1).mul (contDiff_entry 1 0))
  exact (bump2.contDiff.comp htr).mul (bump1.contDiff.comp hdet)

variable (d : ℝˣ)

local notation "D" => Matrix.GeneralLinearGroup.scalar (Fin 2) d

theorem val_scalar : ((D : G2) : M2) = (d : ℝ) • (1 : M2) := by
  show Matrix.scalar (Fin 2) (d : ℝ) = (d : ℝ) • (1 : M2)
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem scalar_comm (x : G2) : x * D = D * x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_scalar, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem val_sq (s : G2) : ((s * D * (s * D) : G2) : M2) = ((d : ℝ) * d) • ((s : M2) * (s : M2)) := by
  rw [Units.val_mul, Units.val_mul, val_scalar, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]

theorem val_sq_apply (s : G2) (i j : Fin 2) :
    ((s * D * (s * D) : G2) : M2) i j = (d : ℝ) * d * ∑ k, (s : M2) i k * (s : M2) k j := by
  rw [val_sq, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]

theorem conj_sq (h t : G2) :
    h⁻¹ * t * h * D * (h⁻¹ * t * h * D) = h⁻¹ * (t * D * (t * D)) * h := by
  have hc := scalar_comm d
  calc h⁻¹ * t * h * D * (h⁻¹ * t * h * D)
      = h⁻¹ * t * (h * D) * h⁻¹ * t * (h * D) := by simp only [mul_assoc]
    _ = h⁻¹ * t * (D * h) * h⁻¹ * t * (D * h) := by rw [hc h]
    _ = h⁻¹ * (t * D * (t * D)) * h := by
        simp only [mul_assoc, mul_inv_cancel_left]

theorem cayley_hamilton_two (m : M2) : m * m = Matrix.trace m • m - m.det • (1 : M2) := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem val_eq_recover (s : G2) (htr : Matrix.trace (s : M2) ≠ 0) :
    (s : M2) = (Matrix.trace (s : M2))⁻¹ •
      ((((d : ℝ) * d)⁻¹ • ((s * D * (s * D) : G2) : M2)) + (s : M2).det • (1 : M2)) := by
  rw [val_sq, smul_smul, inv_mul_cancel₀ (mul_ne_zero d.ne_zero d.ne_zero), one_smul, cayley_hamilton_two,
    sub_add_cancel, smul_smul, inv_mul_cancel₀ htr, one_smul]

theorem val_inv_eq (s : G2) : ((s⁻¹ : G2) : M2) = ((s : M2).det)⁻¹ • (s : M2).adjugate := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv]

end SqCutoff

open SqCutoff

theorem solution
    (f : GL (Fin 2) ℝ → ℂ)
    (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
    (d : ℝˣ) :
    ∃ g : GL (Fin 2) ℝ → ℂ,
      ((∃ G : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧
        ∀ s, g s = G (fun i j => (s : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport g) ∧
      ∃ U ∈ nhds (1 : GL (Fin 2) ℝ), ∀ t ∈ U, ∀ h : GL (Fin 2) ℝ,
        g (h⁻¹ * t * h) =
          f (h⁻¹ * (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d * (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) * h) := by
  obtain ⟨⟨F, hF, hfF⟩, hfc⟩ := hf
  set Dd : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.scalar (Fin 2) d with hDd

  let g : GL (Fin 2) ℝ → ℂ := fun s => (cut (s : Matrix (Fin 2) (Fin 2) ℝ) : ℂ) * f (s * Dd * (s * Dd))
  refine ⟨g, ⟨?_, ?_⟩, ?_⟩
  ·
    refine ⟨fun m => (cut m : ℂ) * F (fun i j => (d : ℝ) * d * ∑ k, m i k * m k j), ?_, fun s => ?_⟩
    · refine (Complex.ofRealCLM.contDiff.comp contDiff_cut).mul (hF.comp ?_)
      refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
      exact contDiff_const.mul (ContDiff.sum fun k _ => (contDiff_entry i k).mul (contDiff_entry k j))
    · show (cut (s : Matrix (Fin 2) (Fin 2) ℝ) : ℂ) * f (s * Dd * (s * Dd)) = _
      rw [hfF]
      congr 2
      funext i j
      exact val_sq_apply d s i j
  ·
    set Kf := tsupport f with hKf
    have hKfc : IsCompact Kf := hfc

    set P : Set (GL (Fin 2) ℝ × ℝ × ℝ) := Kf ×ˢ (Icc (1/2 : ℝ) (3/2) ×ˢ Icc (3/2 : ℝ) (5/2)) with hP
    have hPc : IsCompact P := hKfc.prod (isCompact_Icc.prod isCompact_Icc)
    set Φ₁ : GL (Fin 2) ℝ × ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun x =>
      x.2.2⁻¹ • ((((d : ℝ) * d)⁻¹ • ((x.1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) + x.2.1 • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      with hΦ₁
    have hΦ₁c : ContinuousOn Φ₁ P := by
      refine ContinuousOn.fun_smul ?_ ?_
      · refine ((continuous_snd.comp continuous_snd).continuousOn).inv₀ (fun x hx => ?_)
        have := (hx.2).2; intro h0; simp only [Function.comp] at h0; rw [h0] at this; norm_num at this
      · exact ((continuous_const.fun_smul (Units.continuous_val.comp continuous_fst)).fun_add
          ((continuous_fst.comp continuous_snd).fun_smul continuous_const)).continuousOn
    set C₁ := Φ₁ '' P with hC₁
    have hC₁c : IsCompact C₁ := hPc.image_of_continuousOn hΦ₁c
    set Q : Set (Matrix (Fin 2) (Fin 2) ℝ × ℝ) := C₁ ×ˢ Icc (1/2 : ℝ) (3/2) with hQ
    have hQc : IsCompact Q := hC₁c.prod isCompact_Icc
    set Φ₂ : Matrix (Fin 2) (Fin 2) ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun x => x.2⁻¹ • x.1.adjugate with hΦ₂
    have hadj : Continuous fun m : Matrix (Fin 2) (Fin 2) ℝ => m.adjugate := by
      have : (fun m : Matrix (Fin 2) (Fin 2) ℝ => m.adjugate) = fun m => !![m 1 1, -m 0 1; -m 1 0, m 0 0] := by
        funext m; exact Matrix.adjugate_fin_two m
      rw [this]
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop
    have hΦ₂c : ContinuousOn Φ₂ Q := by
      refine ContinuousOn.fun_smul ?_ (hadj.comp continuous_fst).continuousOn
      refine (continuous_snd.continuousOn).inv₀ (fun x hx => ?_)
      have := hx.2; intro h0; rw [h0] at this; norm_num at this
    set C₂ := Φ₂ '' Q with hC₂
    have hC₂c : IsCompact C₂ := hQc.image_of_continuousOn hΦ₂c

    set Kc : Set (GL (Fin 2) ℝ) := (Units.embedProduct (Matrix (Fin 2) (Fin 2) ℝ)) ⁻¹' (C₁ ×ˢ (MulOpposite.op '' C₂)) with hKc
    have hKcc : IsCompact Kc :=
      Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC₁c.prod (hC₂c.image MulOpposite.continuous_op))

    have hsupp : Function.support g ⊆ Kc := by
      intro s hs
      have hs' : (cut (s : Matrix (Fin 2) (Fin 2) ℝ) : ℂ) * f (s * Dd * (s * Dd)) ≠ 0 := hs
      obtain ⟨hcut, hfs⟩ := mul_ne_zero_iff.mp hs'
      have hcut' : cut (s : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := fun h => hcut (by rw [h, Complex.ofReal_zero])
      obtain ⟨htr, hdet⟩ := cut_ne_zero hcut'
      rw [Real.dist_eq] at htr hdet
      have htr' : Matrix.trace (s : Matrix (Fin 2) (Fin 2) ℝ) ∈ Icc (3/2 : ℝ) (5/2) := by
        constructor <;> [linarith [(abs_lt.mp htr).1]; linarith [(abs_lt.mp htr).2]]
      have hdet' : (s : Matrix (Fin 2) (Fin 2) ℝ).det ∈ Icc (1/2 : ℝ) (3/2) := by
        constructor <;> [linarith [(abs_lt.mp hdet).1]; linarith [(abs_lt.mp hdet).2]]
      have htr0 : Matrix.trace (s : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by intro h0; rw [h0] at htr'; norm_num at htr'
      have hmemK : s * Dd * (s * Dd) ∈ Kf := subset_tsupport _ hfs
      have h1 : ((s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈ C₁ := by
        refine ⟨(s * Dd * (s * Dd), (s : Matrix (Fin 2) (Fin 2) ℝ).det, Matrix.trace (s : Matrix (Fin 2) (Fin 2) ℝ)),
          ⟨hmemK, hdet', htr'⟩, ?_⟩
        simp only [hΦ₁]
        exact (val_eq_recover d s htr0).symm
      have h2 : (((s⁻¹ : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) ∈ C₂ := by
        refine ⟨((s : Matrix (Fin 2) (Fin 2) ℝ), (s : Matrix (Fin 2) (Fin 2) ℝ).det), ⟨h1, hdet'⟩, ?_⟩
        simp only [hΦ₂]
        exact (val_inv_eq s).symm
      show Units.embedProduct _ s ∈ C₁ ×ˢ (MulOpposite.op '' C₂)
      exact ⟨h1, ⟨_, h2, rfl⟩⟩
    exact HasCompactSupport.of_support_subset_isCompact hKcc hsupp
  ·
    refine ⟨{t : GL (Fin 2) ℝ | dist (Matrix.trace (t : Matrix (Fin 2) (Fin 2) ℝ)) 2 < 1/4 ∧
        dist ((t : Matrix (Fin 2) (Fin 2) ℝ).det) 1 < 1/4}, ?_, ?_⟩
    · have hc1 : Continuous fun t : GL (Fin 2) ℝ => Matrix.trace (t : Matrix (Fin 2) (Fin 2) ℝ) :=
        Units.continuous_val.matrix_trace
      have hc2 : Continuous fun t : GL (Fin 2) ℝ => (t : Matrix (Fin 2) (Fin 2) ℝ).det :=
        Units.continuous_val.matrix_det
      refine (IsOpen.inter ?_ ?_).mem_nhds ?_
      · exact isOpen_lt (hc1.dist continuous_const) continuous_const
      · exact isOpen_lt (hc2.dist continuous_const) continuous_const
      · refine ⟨?_, ?_⟩
        · show dist (Matrix.trace ((1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) 2 < 1/4
          rw [Units.val_one, Matrix.trace_one]; simp
        · show dist (((1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)).det 1 < 1/4
          rw [Units.val_one, Matrix.det_one]; simp
    · intro t ht h
      show (cut ((h⁻¹ * t * h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) : ℂ) * f (h⁻¹ * t * h * Dd * (h⁻¹ * t * h * Dd)) = _
      rw [cut_conj, cut_eq_one ht.1.le ht.2.le, Complex.ofReal_one, one_mul, hDd, conj_sq]

end
end S_AutomorphicForm_exists_smooth_hasCompactSupport_forall_nhds_one_apply_conj_eq_apply_conj_mul_scalar_sq
end P2MW
export P2MW.S_AutomorphicForm_exists_smooth_hasCompactSupport_forall_nhds_one_apply_conj_eq_apply_conj_mul_scalar_sq (solution)
