-- Prove2me | solution 1 for AdamDyn.ODEConv.lemma_7_5_Vinf
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:44:31.478019+00:00
-- url     : https://prove2.me/submissions/e66afe94-660e-4e25-8efd-0d5e00352bef

import Mathlib
import Definitions.Def_AdamDyn_ODEConv_AdamField
import Definitions.Def_AdamDyn_ODEConv_LyapunovW

namespace Aux_AdamDyn_ODEConv_lemma_7_5_Vinf

lemma term_le (a b ε g m v S : ℝ) (ha : 0 < a) (hba : b ≤ 4 * a) (hb : 0 < b) (hε : 0 < ε)
    (hv : 0 < v) (hS : 0 ≤ S) :
    g * (-(m / (ε + Real.sqrt |v|))) +
      (1 / 2) * ((((2 : ℕ) * m ^ (2 - 1) * (a * (g - m))) * (a * (ε + Real.sqrt v)) -
        m ^ 2 * (a * ((b * (S - |v|)) / (2 * Real.sqrt v)))) / (a * (ε + Real.sqrt v)) ^ 2)
      ≤ -ε * (a * m / (a * (ε + Real.sqrt v))) ^ 2 := by
  rw [abs_of_pos hv]
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  set s := Real.sqrt v with hsdef
  have hvs : v = s ^ 2 := (Real.sq_sqrt hv.le).symm
  rw [hvs]
  have hp : 0 < ε + s := by linarith
  have key : g * (-(m / (ε + s))) +
      (1 / 2) * ((((2 : ℕ) * m ^ (2 - 1) * (a * (g - m))) * (a * (ε + s)) -
        m ^ 2 * (a * ((b * (S - s ^ 2)) / (2 * s)))) / (a * (ε + s)) ^ 2)
      - (-ε * (a * m / (a * (ε + s))) ^ 2)
      = -(m ^ 2 / (ε + s) ^ 2) * (s * (1 - b / (4 * a)) + b * S / (4 * s * a)) := by
    field_simp
    ring_nf
  have h1 : 0 ≤ m ^ 2 / (ε + s) ^ 2 := by positivity
  have h2 : 0 ≤ s * (1 - b / (4 * a)) := by
    apply mul_nonneg hs.le
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hba
  have h3 : 0 ≤ b * S / (4 * s * a) := by positivity
  have : -(m ^ 2 / (ε + s) ^ 2) * (s * (1 - b / (4 * a)) + b * S / (4 * s * a)) ≤ 0 := by
    nlinarith
  linarith

end Aux_AdamDyn_ODEConv_lemma_7_5_Vinf

open Aux_AdamDyn_ODEConv_lemma_7_5_Vinf in
open AdamDyn.ODEConv in
theorem solution {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSnn : ∀ x i, 0 ≤ S x i)
    (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (z : AdamDyn.WellPosed.State d) (hz : InZplusStar z) :
    DifferentiableAt ℝ (Vinf a ε F) z ∧
      fderiv ℝ (Vinf a ε F) z (adamFieldInf a b ε F S z) ≤
        -ε * ∑ i, (a * z.2.1 i / Uinf a ε z.2.2 i) ^ 2 := by
  have ha : 0 < a := by linarith
  have hv : ∀ i, 0 < z.2.2 i := hz
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hVfun : Vinf a ε F = fun w : AdamDyn.WellPosed.State d =>
      F w.1 + (1 / 2) * ∑ i, (w.2.1 i) ^ 2 / (a * (ε + Real.sqrt (w.2.2 i))) := rfl
  have hterm : ∀ i, DifferentiableAt ℝ (fun w : AdamDyn.WellPosed.State d =>
      (w.2.1 i) ^ 2 / (a * (ε + Real.sqrt (w.2.2 i)))) z := by
    intro i
    have h1 : DifferentiableAt ℝ (fun w : AdamDyn.WellPosed.State d => w.2.2 i) z := by fun_prop
    have h2 := h1.sqrt (hv i).ne'
    have h3 : DifferentiableAt ℝ (fun w : AdamDyn.WellPosed.State d => (w.2.1 i) ^ 2) z := by
      fun_prop
    have h4 : DifferentiableAt ℝ (fun w : AdamDyn.WellPosed.State d =>
        a * (ε + Real.sqrt (w.2.2 i))) z := (h2.const_add ε).const_mul a
    have h5 : DifferentiableAt ℝ (fun w : AdamDyn.WellPosed.State d =>
        (w.2.1 i) ^ 2 * (a * (ε + Real.sqrt (w.2.2 i)))⁻¹) z :=
      h3.fun_mul (h4.fun_inv (by positivity))
    simpa only [div_eq_mul_inv] using h5
  have hdiff : DifferentiableAt ℝ (Vinf a ε F) z := by
    rw [hVfun]
    apply DifferentiableAt.add
    · exact (hFd z.1).comp z differentiableAt_fst
    · apply DifferentiableAt.const_mul
      exact DifferentiableAt.fun_sum (fun i _ => hterm i)
  refine ⟨hdiff, ?_⟩
  set h := adamFieldInf a b ε F S z with hh
  -- derivative along the line
  have hline : HasDerivAt (fun t : ℝ => z + t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add z
  have hφ1 : HasDerivAt (fun t : ℝ => Vinf a ε F (z + t • h)) (fderiv ℝ (Vinf a ε F) z h) 0 :=
    hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  -- explicit derivative
  have hlin1 : HasDerivAt (fun t : ℝ => z.1 + t • h.1) h.1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h.1).const_add z.1
  have hFpart : HasDerivAt (fun t : ℝ => F (z.1 + t • h.1)) (fderiv ℝ F z.1 h.1) 0 :=
    (hFd z.1).hasFDerivAt.comp_hasDerivAt_of_eq 0 hlin1 (by simp)
  have hcoord : ∀ (c e : ℝ), HasDerivAt (fun t : ℝ => c + t * e) e 0 := by
    intro c e
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const e).const_add c
  have hsum : ∀ i ∈ Finset.univ, HasDerivAt (fun t : ℝ =>
      (z.2.1 i + t * h.2.1 i) ^ 2 / (a * (ε + Real.sqrt (z.2.2 i + t * h.2.2 i))))
      ((((2 : ℕ) * (z.2.1 i) ^ (2 - 1) * h.2.1 i) * (a * (ε + Real.sqrt (z.2.2 i))) -
        (z.2.1 i) ^ 2 * (a * (h.2.2 i / (2 * Real.sqrt (z.2.2 i))))) /
          (a * (ε + Real.sqrt (z.2.2 i))) ^ 2) 0 := by
    intro i _
    have hn := (hcoord (z.2.1 i) (h.2.1 i)).pow 2
    have hs := (hcoord (z.2.2 i) (h.2.2 i)).sqrt (by simp; exact (hv i).ne')
    have hd := (hs.const_add ε).const_mul a
    have := hn.fun_div hd (by simp only [zero_mul, add_zero]; positivity)
    simpa using this
  have hψ := hFpart.add ((HasDerivAt.fun_sum hsum).const_mul (1 / 2 : ℝ))
  have hφeq : (fun t : ℝ => Vinf a ε F (z + t • h)) = fun t : ℝ =>
      F (z.1 + t • h.1) + (1 / 2) * ∑ i, (z.2.1 i + t * h.2.1 i) ^ 2 /
        (a * (ε + Real.sqrt (z.2.2 i + t * h.2.2 i))) := by
    funext t
    rw [hVfun]
    simp
  rw [hφeq] at hφ1
  rw [hφ1.unique hψ]
  -- gradient pairing
  have hgrad : fderiv ℝ F z.1 h.1 = ∑ i, gradient F z.1 i * h.1 i := by
    have : fderiv ℝ F z.1 h.1 = inner ℝ (gradient F z.1) h.1 :=
      (InnerProductSpace.toDual_symm_apply).symm
    rw [this, PiLp.inner_apply]
    simp [mul_comm]
  rw [hgrad, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have e1 : h.1 i = -(z.2.1 i / (ε + Real.sqrt |z.2.2 i|)) := by simp [hh, adamFieldInf]
  have e2 : h.2.1 i = a * (gradient F z.1 i - z.2.1 i) := by simp [hh, adamFieldInf]
  have e3 : h.2.2 i = b * (S z.1 i - |z.2.2 i|) := by simp [hh, adamFieldInf]
  have eU : Uinf a ε z.2.2 i = a * (ε + Real.sqrt (z.2.2 i)) := rfl
  rw [e1, e2, e3, eU]
  exact term_le a b ε _ _ _ _ ha hba hb hε (hv i) (hSnn _ _)
