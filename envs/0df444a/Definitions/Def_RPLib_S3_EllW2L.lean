-- Prove2me | Definitions.Def_RPLib_S3_EllW2L
-- name    : RPLib_S3_EllW2L
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:26:09.688203+00:00
-- url     : https://prove2.me/theorems/d10eb2ff-aada-467c-b778-5ac76b9da01a
-- title:
--   The Eichler-Selberg trace formula in weight two: the `s`-regularised primitive at weight 2
-- statement:
--   The `s`-regularised primitive at weight 2.
--
--   `R = (P/y)² + t²` (`P = c(x²+y²) + (d-a)x - b`), `H_s = R^(-s)/(1+s)`, `V_s = VG g 1 · H_s`.
--   * `Rc_mul`, `Rc_pos`: `R y² = |C(z, z̄)|² > 0`.
--   * `hasDerivAt_Vs_x`, `hasDerivAt_Vs_y`, `contOn_VsF/VsX/VsY`.
--   * `Vs_identity`: `-(∂_y V_s + i ∂_x V_s) = (φ_g R^(-s) + (s/(1+s)) R^(-s-1)) / y²`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_HypParS

/-!
# S3-ES-Wt2 (O6, file L): the `s`-regularised primitive at weight 2

`R = (P/y)² + t²` (`P = c(x²+y²) + (d-a)x - b`), `H_s = R^(-s)/(1+s)`, `V_s = VG g 1 · H_s`.
* `Rc_mul`, `Rc_pos`: `R y² = |C(z, z̄)|² > 0`.
* `hasDerivAt_Vs_x`, `hasDerivAt_Vs_y`, `contOn_VsF/VsX/VsY`.
* `Vs_identity`: `-(∂_y V_s + i ∂_x V_s) = (φ_g R^(-s) + (s/(1+s)) R^(-s-1)) / y²`.
-/

open Complex MeasureTheory Set
open scoped ComplexConjugate MatrixGroups

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm RamanujanPetersson.HypPar

section Defs

variable (g : Matrix (Fin 2) (Fin 2) ℤ)

/-- `P(x, y) = c (x² + y²) + (d - a) x - b`. -/
def Pc (x y : ℝ) : ℝ := g 1 0 * (x ^ 2 + y ^ 2) + (g 1 1 - g 0 0) * x - g 0 1

/-- The trace as a real number. -/
def trR : ℝ := (g 0 0 : ℝ) + g 1 1

/-- `R = (P / y)² + t²`. -/
def Rc (x y : ℝ) : ℝ := (Pc g x y / y) ^ 2 + trR g ^ 2

def Rcx (x y : ℝ) : ℝ := 2 * Pc g x y * (2 * g 1 0 * x + (g 1 1 - g 0 0)) / y ^ 2

def Rcy (x y : ℝ) : ℝ := 2 * Pc g x y * (2 * g 1 0 * y ^ 2 - Pc g x y) / y ^ 3

/-- `H_s = R^(-s) / (1 + s)` and its partial derivatives. -/
def Hs (s x y : ℝ) : ℝ := Rc g x y ^ (-s) / (1 + s)

def Hsx (s x y : ℝ) : ℝ := -s * Rc g x y ^ (-s - 1) * Rcx g x y / (1 + s)

def Hsy (s x y : ℝ) : ℝ := -s * Rc g x y ^ (-s - 1) * Rcy g x y / (1 + s)

/-- The primitive `V_s = V_g · H_s` and its partial derivatives. -/
def VsF (s : ℝ) (z : ℂ) : ℂ := VG g 1 z * (Hs g s z.re z.im : ℂ)

def VsX (s : ℝ) (z : ℂ) : ℂ := Vx g 1 z * (Hs g s z.re z.im : ℂ) + VG g 1 z * (Hsx g s z.re z.im : ℂ)

def VsY (s : ℝ) (z : ℂ) : ℂ := Vy g 1 z * (Hs g s z.re z.im : ℂ) + VG g 1 z * (Hsy g s z.re z.im : ℂ)

end Defs

section Basic

variable (g : Matrix (Fin 2) (Fin 2) ℤ)

lemma Rc_mul {z : ℂ} (hy : z.im ≠ 0) : Rc g z.re z.im * z.im ^ 2 = normSq (Cf g z (conj z)) := by
  rw [normSq_Cf_conj, show Pf g z = Pc g z.re z.im from rfl]
  unfold Rc trR
  field_simp

lemma Rc_pos {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) {z : ℂ} (hy : 0 < z.im) :
    0 < Rc g z.re z.im := by
  have h := Rc_mul g hy.ne'
  have h2 : 0 < normSq (Cf g z (conj z)) := normSq_pos.2 (Cf_conj_ne_zero hdet hy)
  have h3 : 0 < z.im ^ 2 := by positivity
  nlinarith

lemma hasDerivAt_Pc_x (x y : ℝ) :
    HasDerivAt (fun x => Pc g x y) (2 * g 1 0 * x + (g 1 1 - g 0 0)) x := by
  have h := (((((hasDerivAt_id' x).pow 2).add_const (y ^ 2)).const_mul (g 1 0 : ℝ)).add
    ((hasDerivAt_id' x).const_mul ((g 1 1 : ℝ) - g 0 0))).sub_const (g 0 1 : ℝ)
  exact h.congr_deriv (by norm_num <;> ring)

lemma hasDerivAt_Pc_y (x y : ℝ) : HasDerivAt (fun y => Pc g x y) (2 * g 1 0 * y) y := by
  have h := (((((hasDerivAt_id' y).pow 2).const_add (x ^ 2)).const_mul (g 1 0 : ℝ)).add_const
    (((g 1 1 : ℝ) - g 0 0) * x)).sub_const (g 0 1 : ℝ)
  exact h.congr_deriv (by norm_num <;> ring)

lemma hasDerivAt_Rc_x (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun x => Rc g x y) (Rcx g x y) x := by
  have h := (((hasDerivAt_Pc_x g x y).div_const y).pow 2).add_const (trR g ^ 2)
  exact h.congr_deriv (by simp only [Rcx]; norm_num; field_simp)

lemma hasDerivAt_Rc_y (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y => Rc g x y) (Rcy g x y) y := by
  have h := (((hasDerivAt_Pc_y g x y).div (hasDerivAt_id' y) hy).pow 2).add_const (trR g ^ 2)
  exact h.congr_deriv (by simp only [Rcy, Pi.div_apply]; norm_num; field_simp)

lemma hasDerivAt_Hs_x {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) (s x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x => Hs g s x y) (Hsx g s x y) x := by
  have hR : 0 < Rc g x y := by simpa using Rc_pos hdet (z := (x : ℂ) + y * I) (by simpa using hy)
  have h := ((hasDerivAt_Rc_x g x hy.ne').rpow_const (p := -s) (Or.inl hR.ne')).div_const (1 + s)
  exact h.congr_deriv (by simp only [Hsx]; ring)

lemma hasDerivAt_Hs_y {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) (s x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => Hs g s x y) (Hsy g s x y) y := by
  have hR : 0 < Rc g x y := by simpa using Rc_pos hdet (z := (x : ℂ) + y * I) (by simpa using hy)
  have h := ((hasDerivAt_Rc_y g x hy.ne').rpow_const (p := -s) (Or.inl hR.ne')).div_const (1 + s)
  exact h.congr_deriv (by simp only [Hsy]; ring)

end Basic

section Deriv

variable {g : Matrix (Fin 2) (Fin 2) ℤ}

theorem hasDerivAt_Vs_x (hdet : 0 < g.det) (hq : GoodQ g) (s x y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => VsF g s ((t : ℂ) + y * I)) (VsX g s ((x : ℂ) + y * I)) x := by
  have hz : 0 < ((x : ℂ) + y * I).im := by simpa using hy
  have e : (fun t : ℝ => VsF g s ((t : ℂ) + y * I)) =
      fun t : ℝ => VG g 1 ((t : ℂ) + y * I) * ((Hs g s t y : ℝ) : ℂ) := by
    funext t; simp [VsF]
  rw [e]
  have h := (hasDerivAt_V_x g 1 x y hy (Cf_conj_ne_zero hdet hz) (hq _ hz)).mul
    (hasDerivAt_Hs_x hdet s x hy).ofReal_comp
  exact h.congr_deriv (by simp [VsX])

theorem hasDerivAt_Vs_y (hdet : 0 < g.det) (hq : GoodQ g) (s x y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => VsF g s ((x : ℂ) + t * I)) (VsY g s ((x : ℂ) + y * I)) y := by
  have hz : 0 < ((x : ℂ) + y * I).im := by simpa using hy
  have e : (fun t : ℝ => VsF g s ((x : ℂ) + t * I)) =
      fun t : ℝ => VG g 1 ((x : ℂ) + t * I) * ((Hs g s x t : ℝ) : ℂ) := by
    funext t; simp [VsF]
  rw [e]
  have h := (hasDerivAt_V_y g 1 x y hy (Cf_conj_ne_zero hdet hz) (hq _ hz)).mul
    (hasDerivAt_Hs_y hdet s x hy).ofReal_comp
  exact h.congr_deriv (by simp [VsY])

lemma contOn_Rc (g : Matrix (Fin 2) (Fin 2) ℤ) :
    ContinuousOn (fun z : ℂ => Rc g z.re z.im) {z : ℂ | 0 < z.im} := by
  unfold Rc Pc trR
  refine ContinuousOn.add (ContinuousOn.pow (ContinuousOn.div (by fun_prop) (by fun_prop)
    (fun z hz => (show (0 : ℝ) < z.im from hz).ne')) 2) continuousOn_const

lemma contOn_Rcx (g : Matrix (Fin 2) (Fin 2) ℤ) :
    ContinuousOn (fun z : ℂ => Rcx g z.re z.im) {z : ℂ | 0 < z.im} := by
  unfold Rcx Pc
  exact ContinuousOn.div (by fun_prop) (by fun_prop)
    (fun z hz => pow_ne_zero _ (show (0 : ℝ) < z.im from hz).ne')

lemma contOn_Rcy (g : Matrix (Fin 2) (Fin 2) ℤ) :
    ContinuousOn (fun z : ℂ => Rcy g z.re z.im) {z : ℂ | 0 < z.im} := by
  unfold Rcy Pc
  exact ContinuousOn.div (by fun_prop) (by fun_prop)
    (fun z hz => pow_ne_zero _ (show (0 : ℝ) < z.im from hz).ne')

lemma contOn_rpow (hdet : 0 < g.det) (p : ℝ) :
    ContinuousOn (fun z : ℂ => Rc g z.re z.im ^ p) {z : ℂ | 0 < z.im} :=
  (contOn_Rc g).rpow_const fun z hz => Or.inl (Rc_pos hdet hz).ne'

lemma contOn_Hs (hdet : 0 < g.det) (s : ℝ) :
    ContinuousOn (fun z : ℂ => ((Hs g s z.re z.im : ℝ) : ℂ)) {z : ℂ | 0 < z.im} := by
  unfold Hs
  exact continuous_ofReal.comp_continuousOn ((contOn_rpow hdet (-s)).div_const _)

lemma contOn_Hsx (hdet : 0 < g.det) (s : ℝ) :
    ContinuousOn (fun z : ℂ => ((Hsx g s z.re z.im : ℝ) : ℂ)) {z : ℂ | 0 < z.im} := by
  unfold Hsx
  exact continuous_ofReal.comp_continuousOn
    (((continuousOn_const.mul (contOn_rpow hdet (-s - 1))).mul (contOn_Rcx g)).div_const _)

lemma contOn_Hsy (hdet : 0 < g.det) (s : ℝ) :
    ContinuousOn (fun z : ℂ => ((Hsy g s z.re z.im : ℝ) : ℂ)) {z : ℂ | 0 < z.im} := by
  unfold Hsy
  exact continuous_ofReal.comp_continuousOn
    (((continuousOn_const.mul (contOn_rpow hdet (-s - 1))).mul (contOn_Rcy g)).div_const _)

lemma contOn_VsF (hdet : 0 < g.det) (hq : GoodQ g) (s : ℝ) :
    ContinuousOn (VsF g s) {z : ℂ | 0 < z.im} :=
  (contOn_VG hdet hq 1).mul (contOn_Hs hdet s)

lemma contOn_VsX (hdet : 0 < g.det) (hq : GoodQ g) (s : ℝ) :
    ContinuousOn (VsX g s) {z : ℂ | 0 < z.im} :=
  ((contOn_Vx hdet hq 1).mul (contOn_Hs hdet s)).add ((contOn_VG hdet hq 1).mul (contOn_Hsx hdet s))

lemma contOn_VsY (hdet : 0 < g.det) (hq : GoodQ g) (s : ℝ) :
    ContinuousOn (VsY g s) {z : ℂ | 0 < z.im} :=
  ((contOn_Vy hdet hq 1).mul (contOn_Hs hdet s)).add ((contOn_VG hdet hq 1).mul (contOn_Hsy hdet s))

end Deriv

/-! ## The derivative identity -/

/-- Pure field algebra behind `Vs_identity`. -/
lemma alg_s (V0 VG C q y H R Hm1 s Rx Ry Pc : ℂ) (hC : C ≠ 0) (hq : q ≠ 0) (hy : y ≠ 0)
    (hR : R ≠ 0) (h1 : 1 + s ≠ 0) (hV0 : V0 = 1 / C ^ 2) (hVG : VG = y / (C * q)) (hHm1 : Hm1 = H / R)
    (hk : y ^ 3 * (Ry + I * Rx) = -2 * Pc * q) (hd : R * y ^ 2 + C ^ 2 = -2 * Pc * C) :
    V0 * (H / (1 + s)) - VG * (-s * Hm1 * Ry / (1 + s) + I * (-s * Hm1 * Rx / (1 + s))) =
      ((C ^ 2)⁻¹ * y ^ 2 * H + s / (1 + s) * Hm1) / y ^ 2 := by
  have e : -s * Hm1 * Ry / (1 + s) + I * (-s * Hm1 * Rx / (1 + s)) = -s * Hm1 / (1 + s) * (Ry + I * Rx) := by
    ring
  have hRI : Ry + I * Rx = -2 * Pc * q / y ^ 3 := by
    field_simp; linear_combination hk
  have hP : Pc = -(R * y ^ 2 + C ^ 2) / (2 * C) := by
    field_simp; linear_combination hd
  rw [e, hRI, hV0, hVG, hHm1, hP]
  field_simp
  ring

variable {g : Matrix (Fin 2) (Fin 2) ℤ}

/-- **The `s`-primitive.** `-(∂_y V_s + i ∂_x V_s) = (φ_g R^(-s) + (s/(1+s)) R^(-s-1)) / y²`. -/
theorem Vs_identity (hdet : 0 < g.det) (hq : GoodQ g) (s : ℝ) (hs : 0 ≤ s) (x y : ℝ) (hy : 0 < y) :
    -(VsY g s ((x : ℂ) + y * I) + I * VsX g s ((x : ℂ) + y * I)) =
      (phiG 2 g (UpperHalfPlane.ofComplex ((x : ℂ) + y * I)) * ((Rc g x y ^ (-s) : ℝ) : ℂ) +
        ((s / (1 + s) * Rc g x y ^ (-s - 1) : ℝ) : ℂ)) / (y : ℂ) ^ 2 := by
  set z : ℂ := (x : ℂ) + y * I with hzdef
  have hz : 0 < z.im := by simpa [z] using hy
  have hre : z.re = x := by simp [z]
  have him : z.im = y := by simp [z]
  have hC := Cf_conj_ne_zero hdet hz
  have hqz := hq z hz
  have hR : 0 < Rc g x y := by simpa [hre, him] using Rc_pos hdet hz
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hV := V_identity g 1 le_rfl hz hC hqz
  rw [him] at hV
  have hphi : phiG 2 g (UpperHalfPlane.ofComplex z) = (Cf g z (conj z) ^ 2)⁻¹ * (y : ℂ) ^ 2 := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz, phiG, Cf_conj, map_inv₀, map_pow]
    congr 2
    simp only [Complex.ofReal_inj]
    exact him
  have hCf : Cf g z (conj z) = -(((Pc g x y : ℝ) : ℂ) + I * (trR g : ℂ) * y) := by
    have hc : conj z = (x : ℂ) - y * I := by simp [z]; ring
    rw [hc]; simp only [Cf, Pc, trR]; push_cast
    linear_combination (g 1 0 : ℂ) * (y : ℂ) ^ 2 * I_sq
  have hqf : qf g (conj z) = ((Pc g x y - 2 * g 1 0 * y ^ 2 : ℝ) : ℂ) -
      I * ((y * (2 * g 1 0 * x + (g 1 1 - g 0 0)) : ℝ) : ℂ) := by
    have hc : conj z = (x : ℂ) - y * I := by simp [z]; ring
    rw [hc]; simp only [qf, Pc]; push_cast
    linear_combination (g 1 0 : ℂ) * (y : ℂ) ^ 2 * I_sq
  have hk : (y : ℂ) ^ 3 * ((Rcy g x y : ℂ) + I * (Rcx g x y : ℂ)) = -2 * (Pc g x y : ℂ) * qf g (conj z) := by
    rw [hqf]; simp only [Rcx, Rcy]; push_cast
    field_simp; ring
  have hd : ((Rc g x y : ℝ) : ℂ) * (y : ℂ) ^ 2 + Cf g z (conj z) ^ 2 =
      -2 * (Pc g x y : ℂ) * Cf g z (conj z) := by
    have hR2 : ((Rc g x y : ℝ) : ℂ) * (y : ℂ) ^ 2 = (Pc g x y : ℂ) ^ 2 + (trR g : ℂ) ^ 2 * (y : ℂ) ^ 2 := by
      simp only [Rc]; push_cast; field_simp
    rw [hR2, hCf]
    linear_combination (trR g : ℂ) ^ 2 * (y : ℂ) ^ 2 * I_sq
  have hVG : VG g 1 z = (y : ℂ) / (Cf g z (conj z) * qf g (conj z)) := by
    simp only [VG, uf, Yf_conj, him, pow_one, Nat.cast_one, div_one]
  have hH : ((Rc g x y ^ (-s - 1) : ℝ) : ℂ) = ((Rc g x y ^ (-s) : ℝ) : ℂ) / ((Rc g x y : ℝ) : ℂ) := by
    rw [Real.rpow_sub_one hR.ne']; push_cast; ring
  have h1 : (1 : ℂ) + s ≠ 0 := by exact_mod_cast (show (1 : ℝ) + s ≠ 0 by linarith)
  have key := alg_s (-(Vy g 1 z + I * Vx g 1 z)) (VG g 1 z) (Cf g z (conj z)) (qf g (conj z)) (y : ℂ)
    ((Rc g x y ^ (-s) : ℝ) : ℂ) ((Rc g x y : ℝ) : ℂ) ((Rc g x y ^ (-s - 1) : ℝ) : ℂ) (s : ℂ)
    (Rcx g x y : ℂ) (Rcy g x y : ℂ) (Pc g x y : ℂ) hC hqz hy0 (by exact_mod_cast hR.ne') h1
    (by rw [hV, div_pow]; first | (field_simp; ring) | field_simp) hVG hH hk hd
  rw [hphi]
  simp only [VsY, VsX, Hs, Hsx, Hsy, hre, him]
  push_cast
  linear_combination key

end RamanujanPetersson.EllW2


