-- Prove2me | solution 1 for Arxiv1810_02867.scalar_wave_equation
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-27T03:12:33.402982+00:00
-- url     : https://prove2.me/submissions/9c802960-abd4-4147-b58e-39fba94c30fd

import Definitions.Def_Arxiv1810_02867_Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open Matrix
open scoped BigOperators
namespace Arxiv1810_02867.ScalarWaveProof

abbrev ST := Plane × ℝ

def et : ST := (0, 1)
def ex (r : Fin 2) : ST := (Pi.single r 1, 0)

theorem pdt_eq_df (f : Plane → ℝ → ℝ)
    (hf : Differentiable ℝ (fun z : ST => f z.1 z.2)) (x : Plane) (t : ℝ) :
    pdt f x t = fderiv ℝ (fun z : ST => f z.1 z.2) (x,t) et := by
  have h := (hf (x,t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  exact h.deriv

theorem pdx_eq_df (f : Plane → ℝ → ℝ)
    (hf : Differentiable ℝ (fun z : ST => f z.1 z.2)) (r : Fin 2) (x : Plane) (t : ℝ) :
    pdx r f x t = fderiv ℝ (fun z : ST => f z.1 z.2) (x,t) (ex r) := by
  have h := (hf (Function.update x r (x r),t)).hasFDerivAt.comp_hasDerivAt (x r)
    ((hasDerivAt_update x r (x r)).prodMk (hasDerivAt_const (x r) t))
  simpa only [pdx, pd, Function.comp_def, ex, Function.update_eq_self] using h.deriv

theorem time_regular (f : Plane → ℝ → ℝ) (hf : ContDiff ℝ 2 (fun z : ST => f z.1 z.2)) :
    ContDiff ℝ 1 (fun z : ST => pdt f z.1 z.2) := by
  have heq : (fun z : ST => pdt f z.1 z.2) =
      fun z => fderiv ℝ (fun z : ST => f z.1 z.2) z et := by
    funext z
    exact pdt_eq_df f (hf.differentiable (by norm_num)) z.1 z.2
  rw [heq]
  exact (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

theorem space_regular (f : Plane → ℝ → ℝ) (hf : ContDiff ℝ 2 (fun z : ST => f z.1 z.2))
    (r : Fin 2) : ContDiff ℝ 1 (fun z : ST => pdx r f z.1 z.2) := by
  have heq : (fun z : ST => pdx r f z.1 z.2) =
      fun z => fderiv ℝ (fun z : ST => f z.1 z.2) z (ex r) := by
    funext z
    exact pdx_eq_df f (hf.differentiable (by norm_num)) r z.1 z.2
  rw [heq]
  exact (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

theorem df_apply_deriv (F : ST → ℝ) (hF : ContDiff ℝ 2 F) (v w z : ST) :
    fderiv ℝ (fun y => fderiv ℝ F y v) z w = fderiv ℝ (fderiv ℝ F) z w v := by
  have hd : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  rw [fderiv_clm_apply (hd.differentiable (by norm_num) z) (differentiableAt_const (c := v))]
  simp

/-- Schwarz's theorem applies to the actual coordinate-line partial derivatives. -/
theorem mixed_partials (f : Plane → ℝ → ℝ) (hf : ContDiff ℝ 2 (fun z : ST => f z.1 z.2))
    (r : Fin 2) (x : Plane) (t : ℝ) :
    pdt (pdx r f) x t = pdx r (pdt f) x t := by
  have hdx := space_regular f hf r
  have hdt := time_regular f hf
  rw [pdt_eq_df _ (hdx.differentiable (by norm_num)), pdx_eq_df _ (hdt.differentiable (by norm_num))]
  have hx : (fun z : ST => pdx r f z.1 z.2) =
      fun z => fderiv ℝ (fun z : ST => f z.1 z.2) z (ex r) := by
    funext z
    exact pdx_eq_df f (hf.differentiable (by norm_num)) r z.1 z.2
  have ht : (fun z : ST => pdt f z.1 z.2) =
      fun z => fderiv ℝ (fun z : ST => f z.1 z.2) z et := by
    funext z
    exact pdt_eq_df f (hf.differentiable (by norm_num)) z.1 z.2
  rw [hx, ht, df_apply_deriv _ hf, df_apply_deriv _ hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq et (ex r)


theorem time_diff (f : Plane → ℝ → ℝ) (hf : ContDiff ℝ 1 (fun z : ST => f z.1 z.2))
    (x : Plane) (t : ℝ) : DifferentiableAt ℝ (fun s => f x s) t :=
  ((hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)) t

theorem space_diff (f : Plane → ℝ → ℝ) (hf : ContDiff ℝ 1 (fun z : ST => f z.1 z.2))
    (r : Fin 2) (x : Plane) (t : ℝ) :
    DifferentiableAt ℝ (fun y => f (Function.update x r y) t) (x r) :=
  ((hf.comp ((contDiff_update 1 x r).prodMk contDiff_const)).differentiable (by norm_num)) (x r)

theorem Dg_regular (gamma : Plane → Fin 2 → ℝ) (hg : ContDiff ℝ 1 gamma)
    (f : Plane → ℝ → ℝ) (hf : ContDiff ℝ 2 (fun z : ST => f z.1 z.2)) (r : Fin 2) :
    ContDiff ℝ 1 (fun z : ST => Dg gamma r f z.1 z.2) := by
  exact (space_regular f hf r).add
    (((contDiff_apply ℝ ℝ r).comp (hg.comp contDiff_fst)).mul (time_regular f hf))

theorem Dg_add (gamma : Plane → Fin 2 → ℝ) (r : Fin 2)
    (f g : Plane → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (fun z : ST => f z.1 z.2))
    (hg : ContDiff ℝ 1 (fun z : ST => g z.1 z.2)) (x : Plane) (t : ℝ) :
    Dg gamma r (fun y s => f y s + g y s) x t = Dg gamma r f x t + Dg gamma r g x t := by
  have hx : pdx r (fun y s => f y s + g y s) x t = pdx r f x t + pdx r g x t := by
    exact ((space_diff f hf r x t).hasDerivAt.add (space_diff g hg r x t).hasDerivAt).deriv
  have ht : pdt (fun y s => f y s + g y s) x t = pdt f x t + pdt g x t := by
    exact ((time_diff f hf x t).hasDerivAt.add (time_diff g hg x t).hasDerivAt).deriv
  unfold Dg
  rw [hx, ht]
  ring

theorem Dg_time (gamma : Plane → Fin 2 → ℝ) (f : Plane → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (fun z : ST => f z.1 z.2)) (r : Fin 2) (x : Plane) (t : ℝ) :
    pdt (Dg gamma r f) x t = Dg gamma r (pdt f) x t := by
  have h1 := (time_diff (pdx r f) (space_regular f hf r) x t).hasDerivAt
  have h2 := (time_diff (pdt f) (time_regular f hf) x t).hasDerivAt
  have h := (h1.add (h2.const_mul (gamma x r))).deriv
  change pdt (Dg gamma r f) x t = pdt (pdx r f) x t + gamma x r * pdt (pdt f) x t at h
  rw [mixed_partials f hf] at h
  exact h

/-- The inverse medium tensor is C¹ because its determinant never vanishes. -/
theorem theta_regular (beta : Plane → Fin 2 → Fin 2 → ℝ)
    (hb : ContDiff ℝ 1 beta) (hdet : ∀ x, (Matrix.of (beta x)).det ≠ 0) :
    ∀ i j : Fin 2, ContDiff ℝ 1 (fun x => thetaOf (beta x) i j) := by
  have hc (i j : Fin 2) : ContDiff ℝ 1 (fun x => beta x i j) :=
    (contDiff_apply_apply ℝ ℝ i j).comp hb
  have hd : ContDiff ℝ 1 (fun x => (Matrix.of (beta x)).det) := by
    simpa only [Matrix.det_fin_two, Matrix.of_apply] using
      ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
  intro i j
  fin_cases i <;> fin_cases j
  · convert (hc 1 1).div hd hdet using 1 <;> try rfl
    funext x
    simp [thetaOf, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two,
        smul_eq_mul, div_eq_mul_inv, mul_comm]
  · convert (hc 0 1).neg.div hd hdet using 1 <;> try rfl
    funext x
    simp [thetaOf, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two,
        smul_eq_mul, div_eq_mul_inv, mul_comm]
  · convert (hc 1 0).neg.div hd hdet using 1 <;> try rfl
    funext x
    simp [thetaOf, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two,
        smul_eq_mul, div_eq_mul_inv, mul_comm]
  · convert (hc 0 0).div hd hdet using 1 <;> try rfl
    funext x
    simp [thetaOf, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two,
        smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Left multiplication by theta cancels the beta-weighted time derivative. -/
theorem eliminate_Q (beta : Plane → Fin 2 → Fin 2 → ℝ)
    (gamma : Plane → Fin 2 → ℝ) (P : Plane → ℝ → ℝ) (Q : Plane → ℝ → Fin 2 → ℝ)
    (C : Plane → ℝ → Fin 2 → ℝ) (hdet : ∀ x, (Matrix.of (beta x)).det ≠ 0)
    (h : ∀ x t s, Dg gamma s P x t + ∑ u, beta x s u * pdt (cmp Q u) x t = C x t s)
    (r : Fin 2) (x : Plane) (t : ℝ) :
    (∑ u, thetaOf (beta x) r u * C x t u) =
      (∑ u, thetaOf (beta x) r u * Dg gamma u P x t) + pdt (cmp Q r) x t := by
  have hm := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ =>
      m.mulVec (fun u => pdt (cmp Q u) x t) r)
    (Matrix.nonsing_inv_mul (Matrix.of (beta x)) (isUnit_iff_ne_zero.mpr (hdet x)))
  simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at hm
  change (∑ u, thetaOf (beta x) r u * (∑ j, beta x u j * pdt (cmp Q j) x t)) =
    pdt (cmp Q r) x t at hm
  simp_rw [← h x t, mul_add, Finset.sum_add_distrib]
  rw [hm]


theorem weighted_gradient_regular (beta : Plane → Fin 2 → Fin 2 → ℝ)
    (hb : ContDiff ℝ 1 beta) (hdet : ∀ x, (Matrix.of (beta x)).det ≠ 0)
    (gamma : Plane → Fin 2 → ℝ) (hg : ContDiff ℝ 1 gamma)
    (P : Plane → ℝ → ℝ) (hP : ContDiff ℝ 2 (fun z : ST => P z.1 z.2)) (r : Fin 2) :
    ContDiff ℝ 1 (fun z : ST => ∑ u, thetaOf (beta z.1) r u * Dg gamma u P z.1 z.2) := by
  apply ContDiff.sum
  intro u _
  exact ((theta_regular beta hb hdet r u).comp contDiff_fst).mul (Dg_regular gamma hg P hP u)

theorem first_time_equation (alpha : Plane → ℝ) (gamma : Plane → Fin 2 → ℝ)
    (hg : ContDiff ℝ 1 gamma) (P : Plane → ℝ → ℝ) (Q : Plane → ℝ → Fin 2 → ℝ)
    (B : Plane → ℝ → ℝ)
    (hP : ContDiff ℝ 2 (fun z : ST => P z.1 z.2))
    (hQ : ContDiff ℝ 2 (fun z : ST => Q z.1 z.2))
    (h : ∀ x t, alpha x * pdt P x t + ∑ r, Dg gamma r (cmp Q r) x t = B x t)
    (x : Plane) (t : ℝ) :
    pdt B x t = alpha x * pdt (pdt P) x t + ∑ r, Dg gamma r (pdt (cmp Q r)) x t := by
  have hQr (r : Fin 2) : ContDiff ℝ 2 (fun z : ST => cmp Q r z.1 z.2) :=
    (contDiff_apply ℝ ℝ r).comp hQ
  have hp := (time_diff (pdt P) (time_regular P hP) x t).hasDerivAt
  have hq (r : Fin 2) : HasDerivAt (fun s => Dg gamma r (cmp Q r) x s)
      (Dg gamma r (pdt (cmp Q r)) x t) t := by
    have hd := (time_diff (Dg gamma r (cmp Q r))
      (Dg_regular gamma hg (cmp Q r) (hQr r) r) x t).hasDerivAt
    change HasDerivAt (fun s => Dg gamma r (cmp Q r) x s) (pdt (Dg gamma r (cmp Q r)) x t) t at hd
    rw [Dg_time gamma _ (hQr r)] at hd
    exact hd
  have hsum : HasDerivAt (fun s => ∑ r, Dg gamma r (cmp Q r) x s)
      (∑ r, Dg gamma r (pdt (cmp Q r)) x t) t := HasDerivAt.fun_sum (fun r _ => hq r)
  have hfun : (fun s => B x s) = fun s => alpha x * pdt P x s + ∑ r, Dg gamma r (cmp Q r) x s :=
    funext (fun s => (h x s).symm)
  change deriv (fun s => B x s) t = _
  rw [hfun]
  exact ((hp.const_mul (alpha x)).add hsum).deriv

end Arxiv1810_02867.ScalarWaveProof

open Arxiv1810_02867 Arxiv1810_02867.ScalarWaveProof

theorem solution (alpha : Plane → ℝ) (beta : Plane → Fin 2 → Fin 2 → ℝ)
    (gamma : Plane → Fin 2 → ℝ) (P : Plane → ℝ → ℝ) (Q : Plane → ℝ → Fin 2 → ℝ)
    (B : Plane → ℝ → ℝ) (C : Plane → ℝ → Fin 2 → ℝ)
    (hsym : ∀ x r s, beta x r s = beta x s r) (hdet : ∀ x, (Matrix.of (beta x)).det ≠ 0)
    (hP : ContDiff ℝ 2 (fun z : Plane × ℝ => P z.1 z.2))
    (hQ : ContDiff ℝ 2 (fun z : Plane × ℝ => Q z.1 z.2))
    (hbeta : ContDiff ℝ 1 beta) (hgamma : ContDiff ℝ 1 gamma)
    (h : UnifiedEqs alpha beta gamma P Q B C) :
    ∀ x t, ∑ r, Dg gamma r (fun y s => ∑ u, thetaOf (beta y) r u * Dg gamma u P y s) x t -
        alpha x * pdt (pdt P) x t =
      ∑ r, Dg gamma r (fun y s => ∑ u, thetaOf (beta y) r u * C y s u) x t - pdt B x t := by
  let V : Fin 2 → Plane → ℝ → ℝ := fun r y s => ∑ u, thetaOf (beta y) r u * Dg gamma u P y s
  let W : Fin 2 → Plane → ℝ → ℝ := fun r y s => ∑ u, thetaOf (beta y) r u * C y s u
  have hV (r : Fin 2) : ContDiff ℝ 1 (fun z : ST => V r z.1 z.2) :=
    weighted_gradient_regular beta hbeta hdet gamma hgamma P hP r
  have hQr (r : Fin 2) : ContDiff ℝ 2 (fun z : ST => cmp Q r z.1 z.2) :=
    (contDiff_apply ℝ ℝ r).comp hQ
  have hW (r : Fin 2) : W r = fun y s => V r y s + pdt (cmp Q r) y s := by
    funext y s
    exact eliminate_Q beta gamma P Q C hdet (fun x t s => (h x t).2 s) r y s
  intro x t
  change (∑ r, Dg gamma r (V r) x t) - alpha x * pdt (pdt P) x t =
    (∑ r, Dg gamma r (W r) x t) - pdt B x t
  have hB := first_time_equation alpha gamma hgamma P Q B hP hQ (fun x t => (h x t).1) x t
  have hD (r : Fin 2) : Dg gamma r (W r) x t =
      Dg gamma r (V r) x t + Dg gamma r (pdt (cmp Q r)) x t := by
    rw [hW r, Dg_add gamma r _ _ (hV r) (time_regular _ (hQr r))]
  simp_rw [hD]
  rw [Finset.sum_add_distrib, hB]
  ring

end
