-- Prove2me | solution 1 for AutomorphicForm.archCasimirAt_comp_mul_archRealGLAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/991c70c7-aea7-5df4-9630-6164e5597782

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archCasimirAt_comp_mul_archRealGLAt

set_option autoImplicit false

noncomputable section

open scoped Real
open AutomorphicForm Matrix
open NumberField IsDedekindDomain NumberField.InfinitePlace NumberField.InfinitePlace.Completion

section

variable {K : Type} [Field K] [NumberField K]

private theorem det_of_symm_one : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
  rw [Equiv.apply_symm_apply, Matrix.det_one]
  exact one_ne_zero

private theorem det_coe_ne_zero (m : GL (Fin 2) ℝ) : ((m : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero

private theorem archRealGLAt_eq_archRealLiftAt {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m = archRealLiftAt hw (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have h := archRealLiftAt_mul_archRealGLAt hw det_of_symm_one m
  rw [archRealLiftAt_of_symm_one, one_mul, Equiv.apply_symm_apply, one_mul] at h
  exact h

private theorem isArchSmoothAt_translate {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ) :
    IsArchSmoothAt hw (fun x => φ (x * archRealGLAt hw k)) := by
  intro g
  have hmaps : Set.MapsTo
      (fun e : Fin 2 → Fin 2 → ℝ =>
        (Matrix.of.symm (Matrix.of e * (k : Matrix (Fin 2) (Fin 2) ℝ)) : Fin 2 → Fin 2 → ℝ))
      {e | (Matrix.of e).det ≠ 0} {e | (Matrix.of e).det ≠ 0} := by
    intro e he
    show (Matrix.of (Matrix.of.symm (Matrix.of e * (k : Matrix (Fin 2) (Fin 2) ℝ)))).det ≠ 0
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero he (det_coe_ne_zero k)
  refine ((hφ g).comp (contDiff_of_symm_mul_const (k : Matrix (Fin 2) (Fin 2) ℝ)).contDiffOn hmaps).congr
    fun e he => ?_
  show φ (g * archRealLiftAt hw e * archRealGLAt hw k)
    = φ (g * archRealLiftAt hw (Matrix.of.symm (Matrix.of e * (k : Matrix (Fin 2) (Fin 2) ℝ))))
  rw [mul_assoc, archRealLiftAt_mul_archRealGLAt hw he]

private theorem hasDerivAt_conj_flow (k : GL (Fin 2) ℝ) (d : ArchDir) :
    HasDerivAt
      (fun t : ℝ =>
        (Matrix.of.symm (((k⁻¹ * archFlowMatrix d t * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) :
          Fin 2 → Fin 2 → ℝ))
      (Matrix.of.symm
        (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (k : Matrix (Fin 2) (Fin 2) ℝ)))
      0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  exact ((((hasDerivAt_archFlowMatrix_apply d 0 0).const_mul _).fun_add
      ((hasDerivAt_archFlowMatrix_apply d 1 0).const_mul _)).mul_const _).fun_add
    ((((hasDerivAt_archFlowMatrix_apply d 0 1).const_mul _).fun_add
      ((hasDerivAt_archFlowMatrix_apply d 1 1).const_mul _)).mul_const _)

private theorem archDerivAt_translate_eq_fderiv {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d (fun x => φ (x * archRealGLAt hw k)) g
      = fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e)) (Matrix.of.symm 1)
          (Matrix.of.symm
            (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d
              * (k : Matrix (Fin 2) (Fin 2) ℝ))) := by
  have hopen := isOpen_setOf_det_ne_zero
  have hfun : (fun t : ℝ => (fun x => φ (x * archRealGLAt hw k)) (g * archFlowAt hw d t))
      = fun t : ℝ => (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e))
          (Matrix.of.symm (((k⁻¹ * archFlowMatrix d t * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) := by
    funext t
    show φ (g * archFlowAt hw d t * archRealGLAt hw k) = φ (g * archRealGLAt hw k * archRealLiftAt hw
      (Matrix.of.symm (((k⁻¹ * archFlowMatrix d t * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))))
    rw [← archRealGLAt_eq_archRealLiftAt hw, map_mul, map_mul, map_inv, archFlowAt]
    congr 1
    group
  have hdiff : HasFDerivAt (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e))
      (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealGLAt hw k * archRealLiftAt hw e)) (Matrix.of.symm 1))
      (Matrix.of.symm (((k⁻¹ * archFlowMatrix d 0 * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [archFlowMatrix_zero, mul_one, inv_mul_cancel, Units.val_one]
    exact (((hφ (g * archRealGLAt hw k)).contDiffAt (hopen.mem_nhds det_of_symm_one)).differentiableAt
      (by simp)).hasFDerivAt
  show deriv (fun t : ℝ => (fun x => φ (x * archRealGLAt hw k)) (g * archFlowAt hw d t)) 0 = _
  rw [hfun]
  exact (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_conj_flow k d)).deriv

private theorem archDerivAt_eq_fderiv {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (x : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d φ x
      = fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e)) (Matrix.of.symm 1)
          (Matrix.of.symm (archDirMatrix d)) := by
  have h := archDerivAt_translate_eq_fderiv hφ 1 d x
  simp only [map_one, mul_one, inv_one, Units.val_one, one_mul] at h
  exact h

private def dirEntry (A : Matrix (Fin 2) (Fin 2) ℝ) : ArchDir → ℝ
  | .H => A 0 0
  | .E => A 0 1
  | .Fm => A 1 0

private def adCoeff (k : GL (Fin 2) ℝ) (d : ArchDir) : ArchDir → ℝ :=
  dirEntry (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (k : Matrix (Fin 2) (Fin 2) ℝ))

private def lin3 (c : ArchDir → ℝ) (v : ArchDir → ℂ) : ℂ :=
  (c .H : ℂ) * v .H + (c .E : ℂ) * v .E + (c .Fm : ℂ) * v .Fm

private theorem trace_conj_archDirMatrix (k : GL (Fin 2) ℝ) (d : ArchDir) :
    (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (k : Matrix (Fin 2) (Fin 2) ℝ)) 1 1
      = -(((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d
          * (k : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 := by
  have h0 : Matrix.trace
      (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (k : Matrix (Fin 2) (Fin 2) ℝ)) = 0 := by
    rw [Matrix.trace_mul_cycle, Units.mul_inv, one_mul]
    cases d <;> simp [archDirMatrix, Matrix.trace_fin_two]
  rw [Matrix.trace_fin_two] at h0
  linarith

private theorem of_symm_conj_eq (k : GL (Fin 2) ℝ) (d : ArchDir) :
    (Matrix.of.symm
        (((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (k : Matrix (Fin 2) (Fin 2) ℝ)) :
      Fin 2 → Fin 2 → ℝ)
      = adCoeff k d .H • (Matrix.of.symm (archDirMatrix .H) : Fin 2 → Fin 2 → ℝ)
        + adCoeff k d .E • (Matrix.of.symm (archDirMatrix .E) : Fin 2 → Fin 2 → ℝ)
        + adCoeff k d .Fm • (Matrix.of.symm (archDirMatrix .Fm) : Fin 2 → Fin 2 → ℝ) := by
  have htr := trace_conj_archDirMatrix k d
  simp only [adCoeff, dirEntry]
  set A : Matrix (Fin 2) (Fin 2) ℝ :=
    ((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (k : Matrix (Fin 2) (Fin 2) ℝ)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [archDirMatrix, htr]

private theorem archDerivAt_translate {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d (fun x => φ (x * archRealGLAt hw k)) g
      = lin3 (adCoeff k d) (fun d' => archDerivAt hw d' φ (g * archRealGLAt hw k)) := by
  rw [archDerivAt_translate_eq_fderiv hφ k d g, of_symm_conj_eq, map_add, map_add, map_smul, map_smul, map_smul,
    lin3, archDerivAt_eq_fderiv hφ .H, archDerivAt_eq_fderiv hφ .E, archDerivAt_eq_fderiv hφ .Fm,
    Complex.real_smul, Complex.real_smul, Complex.real_smul]

private theorem archDerivAt_translate_fun {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ) (d : ArchDir) :
    archDerivAt hw d (fun x => φ (x * archRealGLAt hw k))
      = (adCoeff k d .H : ℂ) • (fun x => archDerivAt hw .H φ (x * archRealGLAt hw k))
        + (adCoeff k d .E : ℂ) • (fun x => archDerivAt hw .E φ (x * archRealGLAt hw k))
        + (adCoeff k d .Fm : ℂ) • (fun x => archDerivAt hw .Fm φ (x * archRealGLAt hw k)) := by
  funext g
  rw [archDerivAt_translate hφ k d g]
  simp only [lin3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem archDerivAt_archDerivAt_translate {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ) (d d' : ArchDir)
    (g : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d (archDerivAt hw d' (fun x => φ (x * archRealGLAt hw k))) g
      = lin3 (adCoeff k d') (fun j => lin3 (adCoeff k d)
          (fun i => archDerivAt hw i (archDerivAt hw j φ) (g * archRealGLAt hw k))) := by
  have hs : ∀ j : ArchDir, IsArchSmoothAt hw (fun x => archDerivAt hw j φ (x * archRealGLAt hw k)) :=
    fun j => isArchSmoothAt_translate (hφ.archDerivAt j) k
  rw [archDerivAt_translate_fun hφ k d',
    archDerivAt_add (((hs .H).smul _).add ((hs .E).smul _)) ((hs .Fm).smul _),
    archDerivAt_add ((hs .H).smul _) ((hs .E).smul _),
    archDerivAt_smul, archDerivAt_smul, archDerivAt_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [archDerivAt_translate (hφ.archDerivAt .H) k d g, archDerivAt_translate (hφ.archDerivAt .E) k d g,
    archDerivAt_translate (hφ.archDerivAt .Fm) k d g]
  simp only [lin3]

private theorem coe_inv_eq (k : GL (Fin 2) ℝ) :
    (k : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
      = ((k : Matrix (Fin 2) (Fin 2) ℝ).det)⁻¹ •
          !![(k : Matrix (Fin 2) (Fin 2) ℝ) 1 1, -(k : Matrix (Fin 2) (Fin 2) ℝ) 0 1;
             -(k : Matrix (Fin 2) (Fin 2) ℝ) 1 0, (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0] := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two]

private def tForm : ArchDir → ArchDir → ℝ
  | .H, .H => 1 / 2
  | .E, .Fm => 1
  | .Fm, .E => 1
  | _, _ => 0

private theorem adCoeff_quad (k : GL (Fin 2) ℝ) (i j : ArchDir) :
    1 / 2 * adCoeff k .H i * adCoeff k .H j + adCoeff k .E i * adCoeff k .Fm j + adCoeff k .Fm i * adCoeff k .E j
      = tForm i j := by
  have hd : (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1
      - (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ≠ 0 := by
    rw [← Matrix.det_fin_two]
    exact det_coe_ne_zero k
  cases i <;> cases j <;>
    simp only [adCoeff, dirEntry, tForm, Matrix.coe_units_inv, coe_inv_eq] <;>
    simp [archDirMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;>
    field_simp <;> ring

private def casSym {w : InfinitePlace K} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 K) K → ℂ) (x : AdelicGL2 (𝓞 K) K) : ℂ :=
  (1 / 2 : ℂ) * archDerivAt hw .H (archDerivAt hw .H φ) x + archDerivAt hw .E (archDerivAt hw .Fm φ) x
    + archDerivAt hw .Fm (archDerivAt hw .E φ) x

private theorem casSym_translate {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ) (g : AdelicGL2 (𝓞 K) K) :
    casSym hw (fun x => φ (x * archRealGLAt hw k)) g = casSym hw φ (g * archRealGLAt hw k) := by
  simp only [casSym, archDerivAt_archDerivAt_translate hφ k, lin3]
  have q : ∀ i j : ArchDir, (1 / 2 : ℂ) * (adCoeff k .H i : ℂ) * (adCoeff k .H j : ℂ)
      + (adCoeff k .E i : ℂ) * (adCoeff k .Fm j : ℂ) + (adCoeff k .Fm i : ℂ) * (adCoeff k .E j : ℂ)
      = (tForm i j : ℂ) := fun i j => by
    have h := congrArg (fun r : ℝ => (r : ℂ)) (adCoeff_quad k i j)
    push_cast at h ⊢
    linear_combination h
  have qHH := q .H .H
  have qHE := q .H .E
  have qHF := q .H .Fm
  have qEH := q .E .H
  have qEE := q .E .E
  have qEF := q .E .Fm
  have qFH := q .Fm .H
  have qFE := q .Fm .E
  have qFF := q .Fm .Fm
  simp only [tForm] at qHH qHE qHF qEH qEE qEF qFH qFE qFF
  push_cast at qHH qHE qHF qEH qEE qEF qFH qFE qFF
  linear_combination
    archDerivAt hw .H (archDerivAt hw .H φ) (g * archRealGLAt hw k) * qHH
      + archDerivAt hw .H (archDerivAt hw .E φ) (g * archRealGLAt hw k) * qHE
      + archDerivAt hw .H (archDerivAt hw .Fm φ) (g * archRealGLAt hw k) * qHF
      + archDerivAt hw .E (archDerivAt hw .H φ) (g * archRealGLAt hw k) * qEH
      + archDerivAt hw .E (archDerivAt hw .E φ) (g * archRealGLAt hw k) * qEE
      + archDerivAt hw .E (archDerivAt hw .Fm φ) (g * archRealGLAt hw k) * qEF
      + archDerivAt hw .Fm (archDerivAt hw .H φ) (g * archRealGLAt hw k) * qFH
      + archDerivAt hw .Fm (archDerivAt hw .E φ) (g * archRealGLAt hw k) * qFE
      + archDerivAt hw .Fm (archDerivAt hw .Fm φ) (g * archRealGLAt hw k) * qFF

private theorem archDerivAt_mul_archRealGLAt_eq_fderiv {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (x : AdelicGL2 (𝓞 K) K)
    (m : GL (Fin 2) ℝ) :
    archDerivAt hw d φ (x * archRealGLAt hw m)
      = fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e))
          (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ))
          (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d)) := by
  have hopen := isOpen_setOf_det_ne_zero
  have hdet : (Matrix.of (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply]
    exact det_coe_ne_zero m
  have hfun : (fun t : ℝ => φ (x * archRealGLAt hw m * archFlowAt hw d t))
      = fun t : ℝ => (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e))
          (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℝ) * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) := by
    funext t
    show φ (x * archRealGLAt hw m * archFlowAt hw d t) = φ (x * archRealLiftAt hw _)
    rw [← Units.val_mul, ← archRealGLAt_eq_archRealLiftAt hw, map_mul, archFlowAt, mul_assoc]
  have hdiff : HasFDerivAt (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e))
      (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e))
        (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℝ) * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [archFlowMatrix_zero, Units.val_one, mul_one]
    exact (((hφ x).contDiffAt (hopen.mem_nhds hdet)).differentiableAt (by simp)).hasFDerivAt
  have hc := hasDerivAt_of_symm_mul_archFlowMatrix (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ)) d
  rw [Equiv.apply_symm_apply] at hc
  show deriv (fun t : ℝ => φ (x * archRealGLAt hw m * archFlowAt hw d t)) 0 = _
  rw [hfun]
  simpa only [Function.comp_def] using (hdiff.comp_hasDerivAt (0 : ℝ) hc).deriv

private theorem hasDerivAt_of_symm_archFlowMatrix_mul (d : ArchDir) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    HasDerivAt
      (fun t : ℝ => (Matrix.of.symm ((archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) * A) : Fin 2 → Fin 2 → ℝ))
      (Matrix.of.symm (archDirMatrix d * A)) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hasDerivAt_archFlowMatrix_apply d i 0).mul_const _).fun_add
    ((hasDerivAt_archFlowMatrix_apply d i 1).mul_const _)

private theorem archDerivAt_archDerivAt_eq {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (d d' : ArchDir) (x : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d (archDerivAt hw d' φ) x
      = fderiv ℝ (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e))) (Matrix.of.symm 1)
            (Matrix.of.symm (archDirMatrix d)) (Matrix.of.symm (archDirMatrix d'))
        + fderiv ℝ (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e)) (Matrix.of.symm 1)
            (Matrix.of.symm (archDirMatrix d * archDirMatrix d')) := by
  have hopen := isOpen_setOf_det_ne_zero
  set ψ : (Fin 2 → Fin 2 → ℝ) → ℂ := fun e => φ (x * archRealLiftAt hw e)
  have h2 : ContDiffOn ℝ 2 ψ {e | (Matrix.of e).det ≠ 0} := by
    simpa using contDiffOn_infty.mp (hφ x) 2
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ ψ) {e | (Matrix.of e).det ≠ 0} :=
    h2.fderiv_of_isOpen hopen (le_of_eq one_add_one_eq_two)

  have hfun : (fun t : ℝ => archDerivAt hw d' φ (x * archFlowAt hw d t))
      = fun t : ℝ => fderiv ℝ ψ (Matrix.of.symm ((archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) * 1))
          (Matrix.of.symm ((archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d')) := by
    funext t
    rw [archFlowAt, archDerivAt_mul_archRealGLAt_eq_fderiv hφ d' x, mul_one]

  have hc : HasDerivAt (fun t : ℝ => fderiv ℝ ψ (Matrix.of.symm ((archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) * 1)))
      (fderiv ℝ (fderiv ℝ ψ) (Matrix.of.symm 1) (Matrix.of.symm (archDirMatrix d * 1))) 0 := by
    have hd1 : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) (Matrix.of.symm 1))
        (Matrix.of.symm ((archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ) * 1)) := by
      rw [archFlowMatrix_zero, Units.val_one, mul_one]
      exact ((h1.contDiffAt (hopen.mem_nhds det_of_symm_one)).differentiableAt one_ne_zero).hasFDerivAt
    simpa only [Function.comp_def] using hd1.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_archFlowMatrix_mul d 1)
  have hu := hasDerivAt_of_symm_archFlowMatrix_mul d (archDirMatrix d')
  have h := (hc.clm_apply hu).deriv
  show deriv (fun t : ℝ => archDerivAt hw d' φ (x * archFlowAt hw d t)) 0 = _
  rw [hfun, h]
  simp only [archFlowMatrix_zero, Units.val_one, mul_one, one_mul]

private theorem of_symm_sub (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    (Matrix.of.symm (A - B) : Fin 2 → Fin 2 → ℝ) = Matrix.of.symm A - Matrix.of.symm B := rfl

private theorem archDirMatrix_E_mul_Fm_sub :
    archDirMatrix .E * archDirMatrix .Fm - archDirMatrix .Fm * archDirMatrix .E = archDirMatrix .H := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [archDirMatrix]

private theorem archDerivAt_comm_E_Fm {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (x : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw .E (archDerivAt hw .Fm φ) x - archDerivAt hw .Fm (archDerivAt hw .E φ) x
      = archDerivAt hw .H φ x := by
  have hopen := isOpen_setOf_det_ne_zero
  have h2 : ContDiffOn ℝ 2 (fun e : Fin 2 → Fin 2 → ℝ => φ (x * archRealLiftAt hw e)) {e | (Matrix.of e).det ≠ 0} := by
    simpa using contDiffOn_infty.mp (hφ x) 2
  have hsymm := (h2.contDiffAt (hopen.mem_nhds det_of_symm_one)).isSymmSndFDerivAt (by simp)
  rw [archDerivAt_archDerivAt_eq hφ .E .Fm x, archDerivAt_archDerivAt_eq hφ .Fm .E x,
    hsymm (Matrix.of.symm (archDirMatrix .Fm)) (Matrix.of.symm (archDirMatrix .E)), add_sub_add_left_eq_sub,
    ← map_sub, ← of_symm_sub, archDirMatrix_E_mul_Fm_sub, archDerivAt_eq_fderiv hφ .H x]

private theorem archCasimirAt_eq_casSym {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (x : AdelicGL2 (𝓞 K) K) :
    archCasimirAt hw φ x = -(1 / 2 : ℂ) * casSym hw φ x := by
  have h := archDerivAt_comm_E_Fm hφ x
  simp only [archCasimirAt, casSym, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-1 / 2 : ℂ) * h

end

theorem solution
    {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ) :
    archCasimirAt hw (fun x => φ (x * archRealGLAt hw k)) = fun x => archCasimirAt hw φ (x * archRealGLAt hw k) := by
  funext g
  rw [archCasimirAt_eq_casSym (isArchSmoothAt_translate hφ k) g, archCasimirAt_eq_casSym hφ,
    casSym_translate hφ k g]

end

end S_AutomorphicForm_archCasimirAt_comp_mul_archRealGLAt
end P2MW
export P2MW.S_AutomorphicForm_archCasimirAt_comp_mul_archRealGLAt (solution)
