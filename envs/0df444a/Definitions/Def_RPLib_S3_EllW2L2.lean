-- Prove2me | Definitions.Def_RPLib_S3_EllW2L2
-- name    : RPLib_S3_EllW2L2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:32:25.780668+00:00
-- url     : https://prove2.me/theorems/837c9a71-3c75-4fc4-9c31-ed488f2b8296
-- title:
--   The Eichler-Selberg trace formula in weight two: Stokes for the `s`-primitive
-- statement:
--   Stokes for the `s`-primitive.
--
--   * `Rc_eq_normSq`, `Rc_mob`: `R = |C/Y|²` is a conjugation invariant.
--   * `VsF_T`, `VsF_S`: equivariance of `V_s` (as `VG_T`, `VG_S`).
--   * `topIs`, `arcIs`, `sideAs`, `sideBs`; `sideAs_T`, `arcIs_S`.
--   * `stokes_gs`: `∫_{regY} (φ_g R^(-s) + s/(1+s) R^(-s-1)) / y² = -(top - arc + i (sideA - sideB))`.
--   * `phiGS_eq`: `phiGS k s g z = φ_g(z) · (det^s R^(-s))`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2L
import Definitions.Def_RPLib_S3_EllW2B

/-!
# S3-ES-Wt2 (O6, file L2): Stokes for the `s`-primitive

* `Rc_eq_normSq`, `Rc_mob`: `R = |C/Y|²` is a conjugation invariant.
* `VsF_T`, `VsF_S`: equivariance of `V_s` (as `VG_T`, `VG_S`).
* `topIs`, `arcIs`, `sideAs`, `sideBs`; `sideAs_T`, `arcIs_S`.
* `stokes_gs`: `∫_{regY} (φ_g R^(-s) + s/(1+s) R^(-s-1)) / y² = -(top - arc + i (sideA - sideB))`.
* `phiGS_eq`: `phiGS k s g z = φ_g(z) · (det^s R^(-s))`.
-/

open Complex MeasureTheory Set
open scoped ComplexConjugate MatrixGroups

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm RamanujanPetersson.HypPar

section Inv

variable (g : Matrix (Fin 2) (Fin 2) ℤ)

lemma Rc_eq_normSq {z : ℂ} (hy : z.im ≠ 0) :
    Rc g z.re z.im = normSq (Cf g z (conj z) / Yf z (conj z)) := by
  have h := Rc_mul g hy
  rw [Complex.normSq_div, Yf_conj, normSq_ofReal, ← h, eq_div_iff (mul_ne_zero hy hy)]
  ring

lemma Rc_mob (h : Matrix (Fin 2) (Fin 2) ℤ) (hdet : h.det = 1) {z : ℂ} (hy : z.im ≠ 0)
    (hz : (h 1 0 : ℂ) * z + h 1 1 ≠ 0) (hw : (h 1 0 : ℂ) * conj z + h 1 1 ≠ 0) :
    Rc (h * g * h.adjugate) (mob h z).re (mob h z).im = Rc g z.re z.im := by
  have hd : ((h 0 0 : ℂ) * h 1 1 - h 0 1 * h 1 0) = 1 := by
    have := congrArg (fun t : ℤ => (t : ℂ)) hdet
    simp only [Matrix.det_fin_two] at this
    push_cast at this
    exact this
  have hC := Cf_mob_aux g h z (conj z) hz hw
  have hY := Yf_mob_aux h z (conj z) hz hw
  rw [hd, one_pow, one_mul] at hC
  rw [hd, one_mul] at hY
  have hY0 : Yf z (conj z) ≠ 0 := by rw [Yf_conj]; exact_mod_cast hy
  have hY' : Yf (mob h z) (mob h (conj z)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hY
    exact hY0 hY.symm
  have hy' : (mob h z).im ≠ 0 := by
    have h2 := hY'
    rw [mob_conj h z, Yf_conj] at h2
    exact_mod_cast h2
  rw [Rc_eq_normSq _ hy', Rc_eq_normSq _ hy, ← mob_conj h z]
  congr 1
  rw [div_eq_div_iff hY' hY0, ← hC, ← hY]
  ring

end Inv

section Mob

variable {g : Matrix (Fin 2) (Fin 2) ℤ}

theorem VsF_T (hdet : 0 < g.det) (hq : GoodQ g) (s : ℝ) {z : ℂ} (hz : 0 < z.im) :
    VsF (S3.Conj.conj ModularGroup.T g) s (z + 1) = VsF g s z := by
  have hR : Rc (S3.Conj.conj ModularGroup.T g) (z + 1).re (z + 1).im = Rc g z.re z.im := by
    have h := Rc_mob g _ (Matrix.SpecialLinearGroup.det_coe ModularGroup.T) hz.ne'
      (by simp [ModularGroup.coe_T]) (by simp [ModularGroup.coe_T])
    rwa [mob_T, ← conj_coe] at h
  simp only [VsF, Hs, hR, VG_T hdet hq 1 hz]

theorem VsF_S (hdet : 0 < g.det) (hq : GoodQ g) (s : ℝ) {z : ℂ} (hz : 0 < z.im) :
    VsF (S3.Conj.conj ModularGroup.S g) s (-1 / z) = VsF g s z * conj z ^ 2 := by
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  have hz0' : conj z ≠ 0 := (map_ne_zero _).2 hz0
  have hR : Rc (S3.Conj.conj ModularGroup.S g) (-1 / z).re (-1 / z).im = Rc g z.re z.im := by
    have h := Rc_mob g _ (Matrix.SpecialLinearGroup.det_coe ModularGroup.S) hz.ne'
      (by simpa [ModularGroup.coe_S] using hz0) (by simpa [ModularGroup.coe_S] using hz0')
    rwa [mob_S, ← conj_coe] at h
  simp only [VsF, Hs, hR, VG_S hdet hq 1 hz]
  ring

end Mob

/-! ## Boundary integrals of `V_s` -/

def topIs (g : Matrix (Fin 2) (Fin 2) ℤ) (s Y : ℝ) : ℂ :=
  ∫ x in (-(1 / 2 : ℝ))..(1 / 2), VsF g s (x + Y * I)

def arcIs (g : Matrix (Fin 2) (Fin 2) ℤ) (s : ℝ) : ℂ :=
  ∫ x in (-(1 / 2 : ℝ))..(1 / 2), (1 - I * arcH' x) * VsF g s (x + arcH x * I)

def sideAs (g : Matrix (Fin 2) (Fin 2) ℤ) (s Y : ℝ) : ℂ :=
  ∫ y in arcH (1 / 2)..Y, VsF g s (1 / 2 + y * I)

def sideBs (g : Matrix (Fin 2) (Fin 2) ℤ) (s Y : ℝ) : ℂ :=
  ∫ y in arcH (1 / 2)..Y, VsF g s (-(1 / 2) + y * I)

section Bdry

variable {g : Matrix (Fin 2) (Fin 2) ℤ}

theorem sideAs_T (hdet : 0 < g.det) (hq : GoodQ g) (s : ℝ) {Y : ℝ} (hY : 0 < Y) :
    sideAs (S3.Conj.conj ModularGroup.T g) s Y = sideBs g s Y := by
  unfold sideAs sideBs
  refine intervalIntegral.integral_congr fun y hy => ?_
  have hy0 : 0 < y := by
    rcases Set.mem_uIcc.1 hy with h | h
    · exact lt_of_lt_of_le arcH_half_pos h.1
    · exact lt_of_lt_of_le hY h.1
  have e : (1 / 2 : ℂ) + y * I = (-(1 / 2) + y * I) + 1 := by ring
  rw [e, VsF_T hdet hq s (by simpa using hy0)]

theorem arcIs_S (hdet : 0 < g.det) (hq : GoodQ g) (s : ℝ) :
    arcIs (S3.Conj.conj ModularGroup.S g) s = -arcIs g s := by
  unfold arcIs
  set F : ℝ → ℂ := fun t => (1 + I * (arcH' t : ℂ)) * conj ((t : ℂ) + (arcH t : ℂ) * I) ^ 2 *
    VsF g s ((t : ℂ) + (arcH t : ℂ) * I) with hF
  have hle : (-(1 / 2 : ℝ)) ≤ 1 / 2 := by norm_num
  have h1 : ∀ x ∈ Set.uIcc (-(1 / 2 : ℝ)) (1 / 2),
      (1 - I * (arcH' x : ℂ)) * VsF (S3.Conj.conj ModularGroup.S g) s ((x : ℂ) + (arcH x : ℂ) * I) =
        F (-x) := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hx2 : x ^ 2 < 1 := sq_lt_one_of_mem hx
    have hx2' : (-x) ^ 2 < 1 := by rwa [neg_sq]
    have hpos : 0 < arcH (-x) := Real.sqrt_pos.2 (by linarith)
    have him : 0 < (((-x : ℝ) : ℂ) + (arcH (-x) : ℂ) * I).im := by simpa using hpos
    rw [← mob_S_arc hx2, VsF_S hdet hq s him]
    simp only [hF, arcH'_neg]
    push_cast
    ring
  have h2 : ∀ x ∈ Set.uIcc (-(1 / 2 : ℝ)) (1 / 2),
      F x = -((1 - I * (arcH' x : ℂ)) * VsF g s ((x : ℂ) + (arcH x : ℂ) * I)) := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    simp only [hF]
    rw [arc_factor (sq_lt_one_of_mem hx)]
    ring
  rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_comp_neg (fun x => F x), neg_neg,
    intervalIntegral.integral_congr h2, intervalIntegral.integral_neg]

lemma iiSides (hdet : 0 < g.det) (hq : GoodQ g) (s : ℝ) (c : ℂ) (hc : c.im = 0) {Y : ℝ} (hY : 0 < Y) :
    IntervalIntegrable (fun y : ℝ => VsF g s (c + y * I)) volume (arcH (1 / 2)) Y := by
  apply ContinuousOn.intervalIntegrable
  refine (contOn_VsF hdet hq s).comp (by fun_prop : Continuous fun y : ℝ => c + y * I).continuousOn ?_
  intro y hy
  have hy0 : 0 < y := by
    rcases Set.mem_uIcc.1 hy with h | h
    · exact lt_of_lt_of_le arcH_half_pos h.1
    · exact lt_of_lt_of_le hY h.1
  simp [hc, hy0]

/-- **Stokes for one matrix at `s ≥ 0`.** -/
theorem stokes_gs (hdet : 0 < g.det) (hq : GoodQ g) {s : ℝ} (hs : 0 ≤ s) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ p in regY Y, (phiG 2 g (UpperHalfPlane.ofComplex ((p.1 : ℂ) + p.2 * I)) *
        ((Rc g p.1 p.2 ^ (-s) : ℝ) : ℂ) + ((s / (1 + s) * Rc g p.1 p.2 ^ (-s - 1) : ℝ) : ℂ)) /
        ((p.2 : ℂ) ^ 2) =
      -(topIs g s Y - arcIs g s + I * (sideAs g s Y - sideBs g s Y)) := by
  have hcongr : ∀ p ∈ regY Y,
      (phiG 2 g (UpperHalfPlane.ofComplex ((p.1 : ℂ) + p.2 * I)) *
        ((Rc g p.1 p.2 ^ (-s) : ℝ) : ℂ) + ((s / (1 + s) * Rc g p.1 p.2 ^ (-s - 1) : ℝ) : ℂ)) /
        ((p.2 : ℂ) ^ 2) =
        -(VsY g s ((p.1 : ℂ) + p.2 * I) + I * VsX g s ((p.1 : ℂ) + p.2 * I)) := by
    intro p hp
    exact (Vs_identity hdet hq s hs p.1 p.2 (im_pos_of_mem_regY hp)).symm
  rw [setIntegral_congr_fun (isClosed_regY Y).measurableSet hcongr, integral_neg,
    stokes_regY (V := VsF g s) (Vx := VsX g s) (Vy := VsY g s)
      (fun x y hy => hasDerivAt_Vs_x hdet hq s x y hy)
      (fun x y hy => hasDerivAt_Vs_y hdet hq s x y hy)
      (contOn_VsF hdet hq s) (contOn_VsX hdet hq s) (contOn_VsY hdet hq s) hY]
  unfold topIs arcIs sideAs sideBs
  rw [intervalIntegral.integral_sub (iiSides hdet hq s (1 / 2) (by simp) (by linarith))
    (iiSides hdet hq s (-(1 / 2)) (by simp) (by linarith))]

end Bdry

/-! ## `phiGS` in terms of `R` -/

lemma ratQ_eq {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) (z : UpperHalfPlane) :
    KernelS.ratQ g z (-conj (z : ℂ)) = (g.det : ℝ) / Rc g (z : ℂ).re (z : ℂ).im := by
  have hy : 0 < (z : ℂ).im := z.im_pos
  have hR := Rc_pos hdet hy
  have h1 := Rc_mul g hy.ne'
  rw [Cf_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq] at h1
  unfold KernelS.ratQ
  rw [← h1, neg_im, conj_im, neg_neg, div_eq_div_iff (mul_ne_zero hR.ne' (pow_ne_zero 2 hy.ne')) hR.ne']
  ring

lemma phiGS_eq (k : ℕ) {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) (s : ℝ) (z : UpperHalfPlane) :
    phiGS k s g z = phiG k g z * (((g.det : ℝ) ^ s * Rc g (z : ℂ).re (z : ℂ).im ^ (-s) : ℝ) : ℂ) := by
  have hR := Rc_pos hdet (z := (z : ℂ)) z.im_pos
  have hd : (0 : ℝ) ≤ (g.det : ℝ) := by exact_mod_cast hdet.le
  rw [phiGS, ratQ_eq hdet z, Real.div_rpow hd hR.le, Real.rpow_neg hR.le, div_eq_mul_inv]

end RamanujanPetersson.EllW2


