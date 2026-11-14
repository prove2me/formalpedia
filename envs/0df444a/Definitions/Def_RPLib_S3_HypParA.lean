-- Prove2me | Definitions.Def_RPLib_S3_HypParA
-- name    : RPLib_S3_HypParA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:56:07.924589+00:00
-- url     : https://prove2.me/theorems/10dd9c76-7dd8-4f0e-845a-ff81d962b698
-- title:
--   The Eichler-Selberg trace formula, hyperbolic part A: an explicit primitive
-- statement:
--   For an integer matrix $g$ the functions $C_g(z,w) = aw + b - z(cw + d)$, $q_g(w) = cw^2 + (d - a)w - b$ and $u_g = Y^m/(C^m q_g)$ with $Y = (z - w)/(2i)$, giving an explicit primitive of $\varphi_g / y^2$ in the sense of Stokes' theorem.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_EllipticTermA

/-!
# S3-HypParTerms, part A: the explicit primitive `u_g` of `φ_g / y²`

For an integer matrix `g = [[a,b],[c,d]]` put (with `z, w` independent complex variables, later `w = conj z`)
* `Cf g z w = a w + b - z (c w + d)` (so `Cf g z (conj z) = conj Q(g; z, -conj z)`),
* `qf g w = c w² + (d - a) w - b` (the fixed-point polynomial, `qf g w = -Cf g w w`),
* `Yf z w = (z - w) / (2i)` (so `Yf z (conj z) = y`),
* `uf g m z w = Yf^m / (Cf^m qf)`, `VG g m z = uf g m z (conj z) / m`.

Main results:
* `hasDerivAt_V_x`, `hasDerivAt_V_y`: the real partial derivatives of `V = VG g m` are `Vx`, `Vy`;
* `V_identity`: `-(Vy + i Vx) = φ_g(z) / y²` (`φ_g = phiG (m+1) g`), the primitive used for Stokes;
* `normSq_qf_conj`, `normSq_Cf_conj`: `|q(z̄)|² = P² + Δ y²`, `|C|² = P² + t² y²`;
* `qf_conj_ne_zero`: `q_g(z̄) ≠ 0` on `ℍ` for non-scalar `g` with `t² ≥ 4 det g`;
* `uf_conj_mat`: equivariance `u_{h g h⁻¹}(h z, h w) = u_g(z, w) (r w + s)²` for `det h = 1`.
-/

open Complex
open scoped ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypPar

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

section Defs

variable (g : Matrix (Fin 2) (Fin 2) ℤ)

/-- `C(g; z, w) = a w + b - z (c w + d)`. -/
def Cf (z w : ℂ) : ℂ := (g 0 0 : ℂ) * w + g 0 1 - z * ((g 1 0 : ℂ) * w + g 1 1)

/-- The fixed-point polynomial `q_g(w) = c w² + (d - a) w - b`. -/
def qf (w : ℂ) : ℂ := (g 1 0 : ℂ) * w ^ 2 + ((g 1 1 : ℂ) - g 0 0) * w - g 0 1

/-- `Y(z, w) = (z - w) / (2i)`. -/
def Yf (z w : ℂ) : ℂ := (z - w) / (2 * I)

/-- `u_g(z, w) = Y^m / (C^m q_g(w))`. -/
def uf (m : ℕ) (z w : ℂ) : ℂ := Yf z w ^ m / (Cf g z w ^ m * qf g w)

/-- Directional derivative of `Cf` along `(z', w')`. -/
def Cd (z w z' w' : ℂ) : ℂ :=
  (g 0 0 : ℂ) * w' - (z' * ((g 1 0 : ℂ) * w + g 1 1) + z * ((g 1 0 : ℂ) * w'))

/-- Directional derivative of `qf` along `w'`. -/
def qd (w w' : ℂ) : ℂ := ((g 1 0 : ℂ) * (2 * w) + ((g 1 1 : ℂ) - g 0 0)) * w'

/-- Directional derivative of `uf` along `(z', w')` (logarithmic-derivative form). -/
def ud (m : ℕ) (z w z' w' : ℂ) : ℂ :=
  uf g m z w * (m * ((z' - w') / (2 * I)) / Yf z w - m * Cd g z w z' w' / Cf g z w - qd g w w' / qf g w)

/-- The primitive `V_g(z) = u_g(z, conj z) / m`. -/
def VG (m : ℕ) (z : ℂ) : ℂ := uf g m z (conj z) / m

/-- `∂_x V_g`. -/
def Vx (m : ℕ) (z : ℂ) : ℂ := ud g m z (conj z) 1 1 / m

/-- `∂_y V_g`. -/
def Vy (m : ℕ) (z : ℂ) : ℂ := ud g m z (conj z) I (-I) / m

/-- The Möbius action of an integer matrix on `ℂ`. -/
def mob (h : Matrix (Fin 2) (Fin 2) ℤ) (z : ℂ) : ℂ :=
  ((h 0 0 : ℂ) * z + h 0 1) / ((h 1 0 : ℂ) * z + h 1 1)

lemma qf_eq (w : ℂ) : qf g w = -Cf g w w := by simp only [qf, Cf]; ring

lemma Cf_conj (z : ℂ) : Cf g z (conj z) = conj (Q g z (-conj z)) := by
  simp only [Cf, Q, map_add, map_mul, map_neg, conj_conj, map_intCast]; ring

lemma Yf_conj (z : ℂ) : Yf z (conj z) = (z.im : ℂ) := by
  rw [Yf, sub_conj]; push_cast; field_simp

end Defs

/-! ## Norm identities and non-vanishing -/

section Norms

variable (g : Matrix (Fin 2) (Fin 2) ℤ)

/-- `P = c |z|² + (d - a) x - b`. -/
def Pf (z : ℂ) : ℝ := g 1 0 * (z.re ^ 2 + z.im ^ 2) + (g 1 1 - g 0 0) * z.re - g 0 1

lemma normSq_qf_conj (z : ℂ) :
    normSq (qf g (conj z)) =
      Pf g z ^ 2 + (((g 0 0 : ℝ) + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) * z.im ^ 2 := by
  rw [normSq_apply]
  simp [qf, Pf, pow_two, mul_re, mul_im]
  ring

lemma normSq_Cf_conj (z : ℂ) :
    normSq (Cf g z (conj z)) = Pf g z ^ 2 + ((g 0 0 : ℝ) + g 1 1) ^ 2 * z.im ^ 2 := by
  rw [normSq_apply]
  simp [Cf, Pf, mul_re, mul_im]
  ring

lemma normSq_qf_conj_eq (z : ℂ) :
    normSq (qf g (conj z)) = normSq (Cf g z (conj z)) - 4 * (g.det : ℝ) * z.im ^ 2 := by
  rw [normSq_qf_conj, normSq_Cf_conj, Matrix.det_fin_two]; push_cast; ring

lemma Cf_conj_ne_zero {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) {z : ℂ} (hy : 0 < z.im) :
    Cf g z (conj z) ≠ 0 := by
  rw [Cf_conj]
  exact (map_ne_zero _).2 (Q_ne_zero hdet hy (by simpa using hy))

lemma qf_conj_ne_zero {g : Matrix (Fin 2) (Fin 2) ℤ} (hns : ¬(g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1))
    (hhyp : 4 * g.det ≤ (g 0 0 + g 1 1) ^ 2) {z : ℂ} (hy : 0 < z.im) : qf g (conj z) ≠ 0 := by
  intro h
  have hn := normSq_qf_conj g z
  rw [h, map_zero] at hn
  have hΔ : (0 : ℝ) ≤ ((g 0 0 : ℝ) + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) := by
    have h1 : (4 * g.det : ℤ) ≤ (g 0 0 + g 1 1) ^ 2 := hhyp
    rw [Matrix.det_fin_two] at h1
    have h2 := (Int.cast_le (R := ℝ)).2 h1
    push_cast at h2
    linarith
  have hy2 : 0 < z.im ^ 2 := by positivity
  have hP0 : Pf g z = 0 := by
    nlinarith [sq_nonneg (Pf g z), mul_nonneg hΔ hy2.le]
  have hΔ0 : ((g 0 0 : ℝ) + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) = 0 := by
    rw [hP0] at hn
    have h3 : (((g 0 0 : ℝ) + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) * z.im ^ 2 = 0 := by
      linarith
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact h4
    · exact absurd h4 hy2.ne'
  have hsq : (2 * g 1 0 * z.re + g 1 1 - g 0 0 : ℝ) ^ 2 + 4 * ((g 1 0 : ℝ) * z.im) ^ 2 = 0 := by
    simp only [Pf] at hP0
    linear_combination (4 * (g 1 0 : ℝ)) * hP0 + hΔ0
  have hcy : (g 1 0 : ℝ) * z.im = 0 := by
    nlinarith [sq_nonneg (2 * g 1 0 * z.re + g 1 1 - g 0 0 : ℝ), sq_nonneg ((g 1 0 : ℝ) * z.im)]
  have hc : (g 1 0 : ℝ) = 0 := by
    rcases mul_eq_zero.1 hcy with h4 | h4
    · exact h4
    · exact absurd h4 hy.ne'
  have had : (g 0 0 : ℝ) = g 1 1 := by
    rw [hc] at hΔ0
    nlinarith [sq_nonneg ((g 0 0 : ℝ) - g 1 1)]
  have hb : (g 0 1 : ℝ) = 0 := by
    simp only [Pf] at hP0
    rw [hc, had] at hP0
    linarith
  exact hns ⟨by exact_mod_cast hc, by exact_mod_cast hb, by exact_mod_cast had⟩

end Norms

/-! ## Derivatives -/

section Deriv

variable (g : Matrix (Fin 2) (Fin 2) ℤ)

lemma hasDerivAt_ratio {Y C q : ℝ → ℂ} {Y' C' q' : ℂ} {s : ℝ} (m : ℕ) (hY : HasDerivAt Y Y' s)
    (hC : HasDerivAt C C' s) (hq : HasDerivAt q q' s) (hY0 : Y s ≠ 0) (hC0 : C s ≠ 0)
    (hq0 : q s ≠ 0) :
    HasDerivAt (fun s => Y s ^ m / (C s ^ m * q s))
      (Y s ^ m / (C s ^ m * q s) * (m * Y' / Y s - m * C' / C s - q' / q s)) s := by
  have h : HasDerivAt (fun s => Y s ^ m / (C s ^ m * q s)) _ s :=
    (hY.pow m).div ((hC.pow m).mul hq) (mul_ne_zero (pow_ne_zero m hC0) hq0)
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  rcases m with _ | m
  · simp
    field_simp
  · simp only [Nat.add_sub_cancel, pow_succ]
    push_cast
    field_simp
    ring

lemma hasDerivAt_Cf {z w : ℝ → ℂ} {z' w' : ℂ} {s : ℝ} (hz : HasDerivAt z z' s)
    (hw : HasDerivAt w w' s) :
    HasDerivAt (fun s => Cf g (z s) (w s)) (Cd g (z s) (w s) z' w') s := by
  have h : HasDerivAt (fun s => Cf g (z s) (w s)) _ s :=
    ((hw.const_mul (g 0 0 : ℂ)).add_const (g 0 1 : ℂ)).sub
      (hz.mul ((hw.const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ)))
  convert h using 1
  simp only [Cd]

lemma hasDerivAt_qf {w : ℝ → ℂ} {w' : ℂ} {s : ℝ} (hw : HasDerivAt w w' s) :
    HasDerivAt (fun s => qf g (w s)) (qd g (w s) w') s := by
  have h : HasDerivAt (fun s => qf g (w s)) _ s :=
    (((hw.pow 2).const_mul (g 1 0 : ℂ)).add (hw.const_mul ((g 1 1 : ℂ) - g 0 0))).sub_const (g 0 1 : ℂ)
  convert h using 1
  simp only [qd]
  norm_num
  ring

theorem hasDerivAt_uf (m : ℕ) {z w : ℝ → ℂ} {z' w' : ℂ} {s : ℝ} (hz : HasDerivAt z z' s)
    (hw : HasDerivAt w w' s) (hY : Yf (z s) (w s) ≠ 0) (hC : Cf g (z s) (w s) ≠ 0)
    (hq : qf g (w s) ≠ 0) :
    HasDerivAt (fun s => uf g m (z s) (w s)) (ud g m (z s) (w s) z' w') s :=
  hasDerivAt_ratio (Y := fun s => Yf (z s) (w s)) (C := fun s => Cf g (z s) (w s))
    (q := fun s => qf g (w s)) m ((hz.sub hw).div_const (2 * I)) (hasDerivAt_Cf g hz hw)
    (hasDerivAt_qf g hw) hY hC hq

lemma hasDerivAt_xline (y s : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ) + y * I) 1 s := by
  simpa using ((hasDerivAt_id s).ofReal_comp).add_const ((y : ℂ) * I)

lemma hasDerivAt_xline_conj (y s : ℝ) : HasDerivAt (fun s : ℝ => conj ((s : ℂ) + y * I)) 1 s := by
  have e : (fun s : ℝ => conj ((s : ℂ) + y * I)) = fun s : ℝ => (s : ℂ) - y * I := by
    funext s; simp only [map_add, map_mul, conj_ofReal, conj_I]; ring
  rw [e]
  simpa using ((hasDerivAt_id s).ofReal_comp).sub_const ((y : ℂ) * I)

lemma hasDerivAt_yline (x s : ℝ) : HasDerivAt (fun s : ℝ => (x : ℂ) + s * I) I s := by
  simpa using (((hasDerivAt_id s).ofReal_comp).mul_const I).const_add (x : ℂ)

lemma hasDerivAt_yline_conj (x s : ℝ) : HasDerivAt (fun s : ℝ => conj ((x : ℂ) + s * I)) (-I) s := by
  have e : (fun s : ℝ => conj ((x : ℂ) + s * I)) = fun s : ℝ => (x : ℂ) + s * (-I) := by
    funext s; simp only [map_add, map_mul, conj_ofReal, conj_I]
  rw [e]
  simpa using (((hasDerivAt_id s).ofReal_comp).mul_const (-I)).const_add (x : ℂ)

lemma Yf_conj_ne_zero {z : ℂ} (hy : 0 < z.im) : Yf z (conj z) ≠ 0 := by
  rw [Yf_conj]; exact_mod_cast hy.ne'

/-- `∂_x V_g = Vx` along horizontal lines. -/
theorem hasDerivAt_V_x (m : ℕ) (x y : ℝ) (hy : 0 < y)
    (hC : Cf g ((x : ℂ) + y * I) (conj ((x : ℂ) + y * I)) ≠ 0)
    (hq : qf g (conj ((x : ℂ) + y * I)) ≠ 0) :
    HasDerivAt (fun s : ℝ => VG g m ((s : ℂ) + y * I)) (Vx g m ((x : ℂ) + y * I)) x := by
  have hY : Yf ((x : ℂ) + y * I) (conj ((x : ℂ) + y * I)) ≠ 0 := Yf_conj_ne_zero (by simpa using hy)
  exact (hasDerivAt_uf g m (hasDerivAt_xline y x) (hasDerivAt_xline_conj y x) hY hC hq).div_const _

/-- `∂_y V_g = Vy` along vertical lines. -/
theorem hasDerivAt_V_y (m : ℕ) (x y : ℝ) (hy : 0 < y)
    (hC : Cf g ((x : ℂ) + y * I) (conj ((x : ℂ) + y * I)) ≠ 0)
    (hq : qf g (conj ((x : ℂ) + y * I)) ≠ 0) :
    HasDerivAt (fun s : ℝ => VG g m ((x : ℂ) + s * I)) (Vy g m ((x : ℂ) + y * I)) y := by
  have hY : Yf ((x : ℂ) + y * I) (conj ((x : ℂ) + y * I)) ≠ 0 := Yf_conj_ne_zero (by simpa using hy)
  exact (hasDerivAt_uf g m (hasDerivAt_yline x y) (hasDerivAt_yline_conj x y) hY hC hq).div_const _

/-- The abstract algebra behind `V_identity`. -/
lemma key_alg (u Y C q Cx Cy qx qy L m : ℂ) (hm : m ≠ 0) (hY : Y ≠ 0) (hC : C ≠ 0) (hq : q ≠ 0)
    (h1 : Cy + I * Cx = -2 * I * L) (h2 : qy + I * qx = 0) (h3 : C + 2 * I * Y * L = -q) :
    -(u * (m * 1 / Y - m * Cy / C - qy / q) / m + I * (u * (m * 0 / Y - m * Cx / C - qx / q) / m)) =
      u * q / (Y * C) := by
  have e1 : Cy = -2 * I * L - I * Cx := by linear_combination h1
  have e2 : qy = -I * qx := by linear_combination h2
  have e3 : q = -(C + 2 * I * Y * L) := by linear_combination h3
  subst e1 e2 e3
  field_simp
  ring

/-- **The primitive.** `-(∂_y V_g + i ∂_x V_g) = (y / conj Q)^(m+1) / y²`. -/
theorem V_identity (m : ℕ) (hm : 1 ≤ m) {z : ℂ} (hy : 0 < z.im) (hC : Cf g z (conj z) ≠ 0)
    (hq : qf g (conj z) ≠ 0) :
    -(Vy g m z + I * Vx g m z) = ((z.im : ℂ) / Cf g z (conj z)) ^ (m + 1) / (z.im : ℂ) ^ 2 := by
  have hY := Yf_conj_ne_zero hy
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have eI : (I - -I) / (2 * I) = 1 := by field_simp; ring
  have e1 : ((1 : ℂ) - 1) / (2 * I) = 0 := by simp
  have h := key_alg (uf g m z (conj z)) (Yf z (conj z)) (Cf g z (conj z)) (qf g (conj z))
    (Cd g z (conj z) 1 1) (Cd g z (conj z) I (-I)) (qd g (conj z) 1) (qd g (conj z) (-I))
    ((g 1 0 : ℂ) * conj z + g 1 1) (m : ℂ) hm0 hY hC hq
    (by simp only [Cd]; ring) (by simp only [qd]; ring)
    (by rw [qf_eq]; simp only [Yf, Cf]; field_simp; ring)
  have hV : -(Vy g m z + I * Vx g m z) = uf g m z (conj z) * qf g (conj z) /
      (Yf z (conj z) * Cf g z (conj z)) := by
    rw [← h, Vy, Vx, ud, ud, eI, e1]
  rw [hV, uf, ← Yf_conj, div_pow]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  field_simp
  ring

/-- `-(∂_y V_g + i ∂_x V_g) = φ_g(z) / y²` on `ℍ`, for `g` with `det g > 0` and `q_g(z̄) ≠ 0`. -/
theorem V_identity_phiG (m : ℕ) (hm : 1 ≤ m) {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det)
    (z : UpperHalfPlane) (hq : qf g (conj (z : ℂ)) ≠ 0) :
    -(Vy g m z + I * Vx g m z) = phiG (m + 1) g z / ((z.im : ℝ) : ℂ) ^ 2 := by
  have hy : 0 < (z : ℂ).im := z.im_pos
  rw [V_identity g m hm hy (Cf_conj_ne_zero hdet hy) hq, phiG, Cf_conj, map_inv₀, map_pow, div_pow]
  simp only [UpperHalfPlane.coe_im]
  ring

end Deriv

/-! ## Equivariance -/

section Equiv

variable (g h : Matrix (Fin 2) (Fin 2) ℤ)

lemma Cf_mob_aux (z w : ℂ) (hz : (h 1 0 : ℂ) * z + h 1 1 ≠ 0) (hw : (h 1 0 : ℂ) * w + h 1 1 ≠ 0) :
    Cf (h * g * h.adjugate) (mob h z) (mob h w) * (((h 1 0 : ℂ) * z + h 1 1) * ((h 1 0 : ℂ) * w + h 1 1)) =
      ((h 0 0 : ℂ) * h 1 1 - h 0 1 * h 1 0) ^ 2 * Cf g z w := by
  simp only [Cf, mob, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  field_simp
  ring

lemma Yf_mob_aux (z w : ℂ) (hz : (h 1 0 : ℂ) * z + h 1 1 ≠ 0) (hw : (h 1 0 : ℂ) * w + h 1 1 ≠ 0) :
    Yf (mob h z) (mob h w) * (((h 1 0 : ℂ) * z + h 1 1) * ((h 1 0 : ℂ) * w + h 1 1)) =
      ((h 0 0 : ℂ) * h 1 1 - h 0 1 * h 1 0) * Yf z w := by
  have e1 : mob h z = ((h 0 0 : ℂ) * z + h 0 1) / ((h 1 0 : ℂ) * z + h 1 1) := rfl
  have e2 : mob h w = ((h 0 0 : ℂ) * w + h 0 1) / ((h 1 0 : ℂ) * w + h 1 1) := rfl
  generalize hjz : (h 1 0 : ℂ) * z + h 1 1 = jz at hz e1 ⊢
  generalize hjw : (h 1 0 : ℂ) * w + h 1 1 = jw at hw e2 ⊢
  rw [e1, e2]
  simp only [Yf]
  field_simp
  rw [← hjz, ← hjw]
  ring

/-- **Equivariance.** For `det h = 1`: `u_{h g h⁻¹}(h z, h w) = u_g(z, w) (r w + s)²`. -/
theorem uf_mob (m : ℕ) (hdet : h.det = 1) (z w : ℂ) (hz : (h 1 0 : ℂ) * z + h 1 1 ≠ 0)
    (hw : (h 1 0 : ℂ) * w + h 1 1 ≠ 0) (hC0 : Cf g z w ≠ 0) (hq0 : qf g w ≠ 0) :
    uf (h * g * h.adjugate) m (mob h z) (mob h w) = uf g m z w * ((h 1 0 : ℂ) * w + h 1 1) ^ 2 := by
  have hd : ((h 0 0 : ℂ) * h 1 1 - h 0 1 * h 1 0) = 1 := by
    have := congrArg (fun t : ℤ => (t : ℂ)) hdet
    simp only [Matrix.det_fin_two] at this
    push_cast at this
    exact this
  have hC := Cf_mob_aux g h z w hz hw
  have hY := Yf_mob_aux h z w hz hw
  have hq := Cf_mob_aux g h w w hw hw
  rw [hd, one_pow, one_mul] at hC hq
  rw [hd, one_mul] at hY
  have hC' : Cf (h * g * h.adjugate) (mob h z) (mob h w) =
      Cf g z w / (((h 1 0 : ℂ) * z + h 1 1) * ((h 1 0 : ℂ) * w + h 1 1)) := by
    rw [← hC]; field_simp
  have hY' : Yf (mob h z) (mob h w) = Yf z w / (((h 1 0 : ℂ) * z + h 1 1) * ((h 1 0 : ℂ) * w + h 1 1)) := by
    rw [← hY]; field_simp
  have hq' : qf (h * g * h.adjugate) (mob h w) = qf g w / (((h 1 0 : ℂ) * w + h 1 1) ^ 2) := by
    rw [qf_eq, qf_eq, pow_two, ← hq]; field_simp
  rw [uf, uf, hC', hY', hq', div_pow, div_pow]
  field_simp

lemma mob_conj (z : ℂ) : mob h (conj z) = conj (mob h z) := by
  simp only [mob, map_div₀, map_add, map_mul, map_intCast]

end Equiv

end RamanujanPetersson.HypPar


