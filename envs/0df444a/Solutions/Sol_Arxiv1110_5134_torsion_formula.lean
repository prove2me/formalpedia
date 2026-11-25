-- Prove2me | solution 1 for Arxiv1110_5134.torsion_formula
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:37:07.378103+00:00
-- url     : https://prove2.me/submissions/ccbb5d54-df4d-40eb-813e-da09c842c192

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

private lemma cartGrad_eq_fderiv (n : Vec3 → ℝ) (x : Vec3) (hn : DifferentiableAt ℝ n x) (i : Fin 3) :
    cartGrad n x i = fderiv ℝ n x (Pi.single i 1) := by
  have hupd : Function.update x i (x i) = x := Function.update_eq_self i x
  have hn' : HasFDerivAt n (fderiv ℝ n x) (Function.update x i (x i)) := by
    rw [hupd]
    exact hn.hasFDerivAt
  have hcomp := hn'.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
  have hd : deriv (fun r => n (Function.update x i r)) (x i) = fderiv ℝ n x (Pi.single i 1) :=
    hcomp.deriv
  exact hd

private lemma cross_sub_smul_self (v w : Vec3) (c : ℝ) :
    v ⨯₃ (w - c • v) = v ⨯₃ w := by
  ext i
  fin_cases i <;> simp [crossProduct, Fin.sum_univ_three] <;> ring

private lemma vlen_proj_eq_vlen_cross (v w : Vec3) (hv : v ⬝ᵥ v = 1) :
    vlen (w - (v ⬝ᵥ w) • v) = vlen (v ⨯₃ w) := by
  unfold vlen
  congr 1
  simp [crossProduct, dotProduct, Fin.sum_univ_three] at hv ⊢
  linear_combination ((v 0 * w 0 + v 1 * w 1 + v 2 * w 2) ^ 2 - (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2)) * hv

private lemma vlen_pos_of_ne_zero (v : Vec3) (hv : v ≠ 0) : 0 < vlen v := by
  unfold vlen
  apply Real.sqrt_pos.mpr
  have hnn : 0 ≤ v ⬝ᵥ v := by
    simp only [dotProduct, Fin.sum_univ_three]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  apply lt_of_le_of_ne hnn
  intro h0
  apply hv
  simp only [dotProduct, Fin.sum_univ_three] at h0
  ext i
  fin_cases i
  · change v 0 = 0; nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  · change v 1 = 0; nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  · change v 2 = 0; nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

theorem solution (n : Vec3 → ℝ) (hn : ContDiff ℝ 2 n) (hpos : ∀ x, 0 < n x)
    (γ Ω : ℝ → Vec3) (hγ : ∀ t, HasDerivAt γ (Ω t) t) (hunit : ∀ t, Ω t ⬝ᵥ Ω t = 1)
    (hray : ∀ t, HasDerivAt (fun u => n (γ u) • Ω u) (cartGrad n (γ t)) t)
    (s : ℝ) (hK : Ω s ⨯₃ cartGrad n (γ s) ≠ 0) :
    rayCurvature Ω s = vlen (Ω s ⨯₃ cartGrad n (γ s)) / n (γ s) ∧
    frenetNormal Ω s = (vlen (Ω s ⨯₃ cartGrad n (γ s)))⁻¹ •
      (cartGrad n (γ s) - (Ω s ⬝ᵥ cartGrad n (γ s)) • Ω s) ∧
    frenetBinormal Ω s = (vlen (Ω s ⨯₃ cartGrad n (γ s)))⁻¹ • (Ω s ⨯₃ cartGrad n (γ s)) ∧
    rayTorsion Ω s =
      ((vlen (Ω s ⨯₃ cartGrad n (γ s)))⁻¹ • (Ω s ⨯₃ cartGrad n (γ s))) ⬝ᵥ
        deriv (fun u => (vlen (Ω u ⨯₃ cartGrad n (γ u)))⁻¹ •
          ((Ω u ⬝ᵥ cartGrad n (γ u)) • Ω u - cartGrad n (γ u))) s := by
  have hn_diff : ∀ x, DifferentiableAt ℝ n x :=
    fun x => (hn.differentiable (by norm_num)).differentiableAt
  have hng_diff : ∀ t, DifferentiableAt ℝ (fun u => n (γ u)) t :=
    fun t => (hn_diff (γ t)).comp t (hγ t).differentiableAt
  have hΩ_diff : ∀ t, DifferentiableAt ℝ Ω t := by
    intro t
    have hfun : Ω = fun u => (n (γ u))⁻¹ • (n (γ u) • Ω u) := by
      ext u i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (hpos (γ u)).ne', one_mul]
    rw [hfun]
    exact ((hng_diff t).inv (hpos (γ t)).ne').smul (hray t).differentiableAt
  have hΩ_deriv : ∀ t, deriv Ω t =
      (n (γ t))⁻¹ • (cartGrad n (γ t) - (Ω t ⬝ᵥ cartGrad n (γ t)) • Ω t) := by
    intro t
    have hprod := (hng_diff t).hasDerivAt.smul (hΩ_diff t).hasDerivAt
    have huniq : n (γ t) • deriv Ω t + deriv (fun u => n (γ u)) t • Ω t = cartGrad n (γ t) :=
      hprod.unique (hray t)
    have hdot_zero : Ω t ⬝ᵥ deriv Ω t = 0 := by
      have hΩi : ∀ i : Fin 3, HasDerivAt (fun u => Ω u i) (deriv Ω t i) t :=
        fun i => hasDerivAt_pi.mp (hΩ_diff t).hasDerivAt i
      have hsq : HasDerivAt (fun u => Ω u ⬝ᵥ Ω u)
          (∑ i : Fin 3, (deriv Ω t i * Ω t i + Ω t i * deriv Ω t i)) t := by
        have hs := HasDerivAt.sum (u := (Finset.univ : Finset (Fin 3)))
          fun i _ => (hΩi i).mul (hΩi i)
        have hfn : (fun u => Ω u ⬝ᵥ Ω u) =
            ∑ i ∈ (Finset.univ : Finset (Fin 3)), (fun u => Ω u i) * fun u => Ω u i := by
          ext u
          simp [dotProduct, Finset.sum_apply, Pi.mul_apply]
        rw [hfn]
        exact hs
      have hconst : HasDerivAt (fun u => Ω u ⬝ᵥ Ω u) 0 t := by
        simpa [hunit] using hasDerivAt_const t (1 : ℝ)
      have h0 := hsq.unique hconst
      simp only [dotProduct, Fin.sum_univ_three] at h0 ⊢
      linarith
    have hnd_eq : deriv (fun u => n (γ u)) t = Ω t ⬝ᵥ cartGrad n (γ t) := by
      have hdot := congrArg (fun v => Ω t ⬝ᵥ v) huniq
      simp only [dotProduct_add, dotProduct_smul, hunit t, hdot_zero, smul_eq_mul,
        mul_one, mul_zero, zero_add] at hdot
      exact hdot
    rw [hnd_eq] at huniq
    have hne : n (γ t) ≠ 0 := (hpos (γ t)).ne'
    ext i
    have hi := congr_fun huniq i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    field_simp [hne]
    linarith
  have hcurv : ∀ t, rayCurvature Ω t = vlen (Ω t ⨯₃ cartGrad n (γ t)) / n (γ t) := by
    intro t
    unfold rayCurvature
    rw [hΩ_deriv t]
    have hpos_t : 0 < n (γ t) := hpos (γ t)
    have hsc : vlen ((n (γ t))⁻¹ • (cartGrad n (γ t) - (Ω t ⬝ᵥ cartGrad n (γ t)) • Ω t)) =
        (n (γ t))⁻¹ * vlen (cartGrad n (γ t) - (Ω t ⬝ᵥ cartGrad n (γ t)) • Ω t) := by
      unfold vlen
      have hdot : ((n (γ t))⁻¹ • (cartGrad n (γ t) - (Ω t ⬝ᵥ cartGrad n (γ t)) • Ω t)) ⬝ᵥ
          ((n (γ t))⁻¹ • (cartGrad n (γ t) - (Ω t ⬝ᵥ cartGrad n (γ t)) • Ω t)) =
          ((n (γ t))⁻¹) ^ 2 * ((cartGrad n (γ t) - (Ω t ⬝ᵥ cartGrad n (γ t)) • Ω t) ⬝ᵥ
            (cartGrad n (γ t) - (Ω t ⬝ᵥ cartGrad n (γ t)) • Ω t)) := by
        simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
        ring
      rw [hdot, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr hpos_t.le)]
    rw [hsc, vlen_proj_eq_vlen_cross (Ω t) (cartGrad n (γ t)) (hunit t), inv_mul_eq_div]
  have hnorm : ∀ t, Ω t ⨯₃ cartGrad n (γ t) ≠ 0 →
      frenetNormal Ω t = (vlen (Ω t ⨯₃ cartGrad n (γ t)))⁻¹ •
        (cartGrad n (γ t) - (Ω t ⬝ᵥ cartGrad n (γ t)) • Ω t) := by
    intro t hKt
    unfold frenetNormal
    rw [hcurv t, hΩ_deriv t]
    have hne : n (γ t) ≠ 0 := (hpos (γ t)).ne'
    have hvl : vlen (Ω t ⨯₃ cartGrad n (γ t)) ≠ 0 := (vlen_pos_of_ne_zero _ hKt).ne'
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp [hne, hvl]
  have hbin : frenetBinormal Ω s =
      (vlen (Ω s ⨯₃ cartGrad n (γ s)))⁻¹ • (Ω s ⨯₃ cartGrad n (γ s)) := by
    unfold frenetBinormal
    rw [hnorm s hK]
    have hcr : Ω s ⨯₃ ((vlen (Ω s ⨯₃ cartGrad n (γ s)))⁻¹ •
        (cartGrad n (γ s) - (Ω s ⬝ᵥ cartGrad n (γ s)) • Ω s)) =
        (vlen (Ω s ⨯₃ cartGrad n (γ s)))⁻¹ •
          (Ω s ⨯₃ (cartGrad n (γ s) - (Ω s ⬝ᵥ cartGrad n (γ s)) • Ω s)) := by
      ext i
      fin_cases i <;> simp [crossProduct, Fin.sum_univ_three] <;> ring
    rw [hcr, cross_sub_smul_self]
  refine ⟨hcurv s, hnorm s hK, hbin, ?_⟩
  have hcont_g : ContinuousAt (fun u => cartGrad n (γ u)) s := by
    rw [continuousAt_pi]
    intro i
    have hfeq : (fun u => cartGrad n (γ u) i) = fun u => fderiv ℝ n (γ u) (Pi.single i 1) := by
      ext u
      exact cartGrad_eq_fderiv n (γ u) (hn_diff (γ u)) i
    rw [hfeq]
    have hcf : Continuous (fun x => fderiv ℝ n x (Pi.single i (1 : ℝ))) :=
      (hn.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hcf.continuousAt.comp (hγ s).continuousAt
  have hcont_cross : ContinuousAt (fun u => Ω u ⨯₃ cartGrad n (γ u)) s := by
    rw [continuousAt_pi]
    intro i
    have hΩc : ∀ j : Fin 3, ContinuousAt (fun u => Ω u j) s :=
      fun j => (continuous_apply j).continuousAt.comp (hΩ_diff s).continuousAt
    have hgc : ∀ j : Fin 3, ContinuousAt (fun u => cartGrad n (γ u) j) s :=
      fun j => (continuous_apply j).continuousAt.comp hcont_g
    fin_cases i <;>
      simp only [crossProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
        Matrix.head_cons, Fin.isValue] <;>
      exact ((hΩc _).mul (hgc _)).sub ((hΩc _).mul (hgc _))
  have hev_ne : ∀ᶠ u in 𝓝 s, Ω u ⨯₃ cartGrad n (γ u) ≠ 0 :=
    hcont_cross.eventually_ne hK
  have hev_eq : (fun u => -frenetNormal Ω u) =ᶠ[𝓝 s]
      (fun u => (vlen (Ω u ⨯₃ cartGrad n (γ u)))⁻¹ •
        ((Ω u ⬝ᵥ cartGrad n (γ u)) • Ω u - cartGrad n (γ u))) := by
    filter_upwards [hev_ne] with u hu
    rw [hnorm u hu]
    ext i
    simp only [Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  unfold rayTorsion
  have hneg : -deriv (frenetNormal Ω) s = deriv (fun u => -frenetNormal Ω u) s := by
    simp
  rw [hbin, ← dotProduct_neg, hneg, hev_eq.deriv_eq]
