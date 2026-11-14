-- Prove2me | Definitions.Def_RPLib_S3_HypParS
-- name    : RPLib_S3_HypParS
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:16:13.806098+00:00
-- url     : https://prove2.me/theorems/c51769d8-1b06-4585-a611-e8a4e33c2ee0
-- title:
--   The Eichler-Selberg trace formula, hyperbolic part S: Stokes per matrix and reindexing
-- statement:
--   Continuity of the primitives on the upper half plane, their transformation under $SL_2(\mathbb{Z})$, the matching of side integrals under $T$ and arc integrals under $S$, and Stokes' identity for each matrix on the truncated fundamental domain.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_HypParA
import Definitions.Def_RPLib_S3_HypParB
import Definitions.Def_RPLib_S3_HypParC

/-!
# S3-HypParTerms, part S (O4b, first half): per-matrix Stokes and the T/S reindexing identities

* `contAt_ud`, `contOn_VG`, `contOn_Vx`, `contOn_Vy`: continuity on `{im > 0}` (`det g > 0`, `qf g (conj z) ≠ 0`).
* `VG_mob`: `V_{h g h⁻¹}(h z) = V_g(z) (c_h conj z + d_h)²` for `h ∈ SL₂(ℤ)`.
* `sideA_T`: the right side of `T g T⁻¹` is the left side of `g`.
* `arcI_S`: the arc integral of `S g S⁻¹` is minus that of `g`.
* `stokes_g`: `∫_{regY Y} φ_g / y² = -(Top_g(Y) - Arc_g + I (A_g(Y) - B_g(Y)))`.
-/

open Complex MeasureTheory Set
open scoped ComplexConjugate MatrixGroups

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypPar

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

/-- `g` is a rest-part matrix with positive determinant: `qf g (conj z) ≠ 0` on `ℍ`. -/
def GoodQ (g : Matrix (Fin 2) (Fin 2) ℤ) : Prop := ∀ z : ℂ, 0 < z.im → qf g (conj z) ≠ 0

lemma goodQ_of {g : Matrix (Fin 2) (Fin 2) ℤ} (hns : ¬(g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1))
    (hhyp : 4 * g.det ≤ (g 0 0 + g 1 1) ^ 2) : GoodQ g :=
  fun _ hz => qf_conj_ne_zero hns hhyp hz

section Cont

variable {g : Matrix (Fin 2) (Fin 2) ℤ}

lemma contAt_uf (hdet : 0 < g.det) (hq : GoodQ g) (m : ℕ) {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt (fun z => uf g m z (conj z)) z := by
  have hC := Cf_conj_ne_zero hdet hz
  have hQ := hq z hz
  have c1 : Continuous fun z : ℂ => Yf z (conj z) := by unfold Yf; fun_prop
  have c2 : Continuous fun z : ℂ => Cf g z (conj z) := by unfold Cf; fun_prop
  have c3 : Continuous fun z : ℂ => qf g (conj z) := by unfold qf; fun_prop
  exact ((c1.pow m).continuousAt).div ((c2.pow m).mul c3).continuousAt
    (mul_ne_zero (pow_ne_zero _ hC) hQ)

lemma contAt_ud (hdet : 0 < g.det) (hq : GoodQ g) (m : ℕ) (z' w' : ℂ) {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt (fun z => ud g m z (conj z) z' w') z := by
  have hY := Yf_conj_ne_zero hz
  have hC := Cf_conj_ne_zero hdet hz
  have hQ := hq z hz
  have c1 : Continuous fun z : ℂ => Yf z (conj z) := by unfold Yf; fun_prop
  have c2 : Continuous fun z : ℂ => Cf g z (conj z) := by unfold Cf; fun_prop
  have c3 : Continuous fun z : ℂ => qf g (conj z) := by unfold qf; fun_prop
  have c4 : Continuous fun z : ℂ => Cd g z (conj z) z' w' := by unfold Cd; fun_prop
  have c5 : Continuous fun z : ℂ => qd g (conj z) w' := by unfold qd; fun_prop
  unfold ud
  exact (contAt_uf hdet hq m hz).mul (((continuousAt_const.div c1.continuousAt hY).sub
    ((continuousAt_const.mul c4.continuousAt).div c2.continuousAt hC)).sub
    (c5.continuousAt.div c3.continuousAt hQ))

lemma contOn_VG (hdet : 0 < g.det) (hq : GoodQ g) (m : ℕ) :
    ContinuousOn (VG g m) {z : ℂ | 0 < z.im} := fun _ hz =>
  ((contAt_uf hdet hq m hz).div_const _).continuousWithinAt

lemma contOn_Vx (hdet : 0 < g.det) (hq : GoodQ g) (m : ℕ) :
    ContinuousOn (Vx g m) {z : ℂ | 0 < z.im} := fun _ hz =>
  ((contAt_ud hdet hq m 1 1 hz).div_const _).continuousWithinAt

lemma contOn_Vy (hdet : 0 < g.det) (hq : GoodQ g) (m : ℕ) :
    ContinuousOn (Vy g m) {z : ℂ | 0 < z.im} := fun _ hz =>
  ((contAt_ud hdet hq m I (-I) hz).div_const _).continuousWithinAt

end Cont

/-! ## Boundary integrals -/

/-- Top edge `∫_{-1/2}^{1/2} V_g(x + iY) dx`. -/
def topI (g : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) (Y : ℝ) : ℂ :=
  ∫ x in (-(1 / 2 : ℝ))..(1 / 2), VG g m (x + Y * I)

/-- Arc `∫_{-1/2}^{1/2} (1 - i h'(x)) V_g(x + i h(x)) dx`. -/
def arcI (g : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) : ℂ :=
  ∫ x in (-(1 / 2 : ℝ))..(1 / 2), (1 - I * arcH' x) * VG g m (x + arcH x * I)

/-- Right side `∫_{h(1/2)}^{Y} V_g(1/2 + iy) dy`. -/
def sideA (g : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) (Y : ℝ) : ℂ :=
  ∫ y in arcH (1 / 2)..Y, VG g m (1 / 2 + y * I)

/-- Left side `∫_{h(1/2)}^{Y} V_g(-1/2 + iy) dy`. -/
def sideB (g : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) (Y : ℝ) : ℂ :=
  ∫ y in arcH (1 / 2)..Y, VG g m (-(1 / 2) + y * I)

/-! ## Equivariance under `T` and `S` -/

section Mob

variable {g : Matrix (Fin 2) (Fin 2) ℤ}

lemma conj_coe (h : SL(2, ℤ)) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    S3.Conj.conj h g = (h : Matrix (Fin 2) (Fin 2) ℤ) * g * (h : Matrix (Fin 2) (Fin 2) ℤ).adjugate := by
  rw [S3.Conj.conj, Matrix.SpecialLinearGroup.coe_inv]

theorem VG_mob (hdet : 0 < g.det) (hq : GoodQ g) (m : ℕ) (h : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im)
    (hj : ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * z + (h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 ≠ 0)
    (hj' : ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * conj z + (h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 ≠ 0) :
    VG (S3.Conj.conj h g) m (mob (h : Matrix (Fin 2) (Fin 2) ℤ) z) =
      VG g m z * (((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * conj z + (h : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ^ 2 := by
  unfold VG
  rw [conj_coe, ← mob_conj, uf_mob g _ m (Matrix.SpecialLinearGroup.det_coe h) z (conj z) hj hj'
    (Cf_conj_ne_zero hdet hz) (hq z hz)]
  ring

lemma mob_T (w : ℂ) : mob ((ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) w = w + 1 := by
  simp [mob, ModularGroup.coe_T]

lemma mob_S (w : ℂ) : mob ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) w = -1 / w := by
  simp [mob, ModularGroup.coe_S]

theorem VG_T (hdet : 0 < g.det) (hq : GoodQ g) (m : ℕ) {z : ℂ} (hz : 0 < z.im) :
    VG (S3.Conj.conj ModularGroup.T g) m (z + 1) = VG g m z := by
  have h := VG_mob hdet hq m ModularGroup.T hz (by simp [ModularGroup.coe_T])
    (by simp [ModularGroup.coe_T])
  rw [mob_T] at h
  rw [h]
  simp [ModularGroup.coe_T]

theorem VG_S (hdet : 0 < g.det) (hq : GoodQ g) (m : ℕ) {z : ℂ} (hz : 0 < z.im) :
    VG (S3.Conj.conj ModularGroup.S g) m (-1 / z) = VG g m z * conj z ^ 2 := by
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  have hz0' : conj z ≠ 0 := (map_ne_zero _).2 hz0
  have h := VG_mob hdet hq m ModularGroup.S hz (by simpa [ModularGroup.coe_S] using hz0)
    (by simpa [ModularGroup.coe_S] using hz0')
  rw [mob_S] at h
  rw [h]
  simp [ModularGroup.coe_S]

/-- The right side of `T g T⁻¹` equals the left side of `g`. -/
theorem sideA_T (hdet : 0 < g.det) (hq : GoodQ g) (m : ℕ) {Y : ℝ} (hY : 0 < Y) :
    sideA (S3.Conj.conj ModularGroup.T g) m Y = sideB g m Y := by
  unfold sideA sideB
  refine intervalIntegral.integral_congr fun y hy => ?_
  have hy0 : 0 < y := by
    rcases Set.mem_uIcc.1 hy with h | h
    · exact lt_of_lt_of_le arcH_half_pos h.1
    · exact lt_of_lt_of_le hY h.1
  have e : (1 / 2 : ℂ) + y * I = (-(1 / 2) + y * I) + 1 := by ring
  rw [e, VG_T hdet hq m (by simpa using hy0)]

/-- On the unit circle: `S` maps `γ(-x)` to `γ(x)`, `γ(x) = x + i h(x)`. -/
lemma mob_S_arc {x : ℝ} (hx : x ^ 2 < 1) :
    -1 / (((-x : ℝ) : ℂ) + (arcH (-x) : ℂ) * I) = (x : ℂ) + (arcH x : ℂ) * I := by
  rw [arcH_neg]
  set a : ℂ := (x : ℂ)
  set b : ℂ := (arcH x : ℂ)
  have hb2 : b ^ 2 = 1 - a ^ 2 := by
    simp only [b, a, arcH]
    rw [← ofReal_pow, Real.sq_sqrt (by linarith)]
    push_cast; ring
  have hb0 : (arcH x : ℂ) ≠ 0 := by
    have : 0 < arcH x := Real.sqrt_pos.2 (by linarith)
    exact_mod_cast this.ne'
  have hw : ((-x : ℝ) : ℂ) + b * I ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp [b] at this
    exact hb0 (by exact_mod_cast this)
  rw [div_eq_iff hw]
  push_cast
  linear_combination hb2 - b ^ 2 * I_sq

/-- The arc factor: `(1 + i h'(x)) conj(γ(x))² = -(1 - i h'(x))` for `|x| < 1`. -/
lemma arc_factor {x : ℝ} (hx : x ^ 2 < 1) :
    (1 + I * (arcH' x : ℂ)) * conj ((x : ℂ) + (arcH x : ℂ) * I) ^ 2 = -(1 - I * (arcH' x : ℂ)) := by
  have hpos : 0 < arcH x := Real.sqrt_pos.2 (by linarith)
  set a : ℂ := (x : ℂ) with ha
  set b : ℂ := (arcH x : ℂ) with hbdef
  have hb : b ≠ 0 := by simp only [b]; exact_mod_cast hpos.ne'
  have hb2 : b ^ 2 = 1 - a ^ 2 := by
    simp only [b, a, arcH]
    rw [← ofReal_pow, Real.sq_sqrt (by linarith)]
    push_cast; ring
  have hh' : (arcH' x : ℂ) = -a / b := by simp only [arcH', a, b, arcH]; push_cast; ring
  have hc : conj (a + b * I) = a - b * I := by
    simp only [a, b, map_add, map_mul, conj_ofReal, conj_I]; ring
  rw [hh', hc]
  set P : ℂ := b - I * a
  set Q : ℂ := b + I * a
  have hPQ : P * Q = 1 := by simp only [P, Q]; linear_combination hb2 - a ^ 2 * I_sq
  have e3 : (a - b * I) ^ 2 = -Q ^ 2 := by simp only [Q]; linear_combination (a ^ 2 + b ^ 2) * I_sq
  have hPb : (1 + I * (-a / b)) * b = P := by
    rw [add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hb]; simp only [P]; ring
  have hL : (1 + I * (-a / b)) * (a - b * I) ^ 2 * b = -Q := by
    calc (1 + I * (-a / b)) * (a - b * I) ^ 2 * b = ((1 + I * (-a / b)) * b) * (a - b * I) ^ 2 := by ring
      _ = P * (a - b * I) ^ 2 := by rw [hPb]
      _ = -Q := by linear_combination P * e3 - Q * hPQ
  have hR : -(1 - I * (-a / b)) * b = -Q := by
    rw [neg_mul, sub_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hb]; simp only [Q]; ring
  exact mul_right_cancel₀ hb (hL.trans hR.symm)

lemma arcH'_neg (x : ℝ) : arcH' (-x) = -arcH' x := by
  unfold arcH'; rw [neg_sq]; ring

/-- The arc integral of `S g S⁻¹` is minus the arc integral of `g`. -/
theorem arcI_S (hdet : 0 < g.det) (hq : GoodQ g) (m : ℕ) :
    arcI (S3.Conj.conj ModularGroup.S g) m = -arcI g m := by
  unfold arcI
  set F : ℝ → ℂ := fun t => (1 + I * (arcH' t : ℂ)) * conj ((t : ℂ) + (arcH t : ℂ) * I) ^ 2 *
    VG g m ((t : ℂ) + (arcH t : ℂ) * I) with hF
  have hle : (-(1 / 2 : ℝ)) ≤ 1 / 2 := by norm_num
  have h1 : ∀ x ∈ Set.uIcc (-(1 / 2 : ℝ)) (1 / 2),
      (1 - I * (arcH' x : ℂ)) * VG (S3.Conj.conj ModularGroup.S g) m ((x : ℂ) + (arcH x : ℂ) * I) =
        F (-x) := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hx2 : x ^ 2 < 1 := sq_lt_one_of_mem hx
    have hx2' : (-x) ^ 2 < 1 := by rwa [neg_sq]
    have hpos : 0 < arcH (-x) := Real.sqrt_pos.2 (by linarith)
    have him : 0 < (((-x : ℝ) : ℂ) + (arcH (-x) : ℂ) * I).im := by simpa using hpos
    rw [← mob_S_arc hx2, VG_S hdet hq m him]
    simp only [hF, arcH'_neg]
    push_cast
    ring
  have h2 : ∀ x ∈ Set.uIcc (-(1 / 2 : ℝ)) (1 / 2),
      F x = -((1 - I * (arcH' x : ℂ)) * VG g m ((x : ℂ) + (arcH x : ℂ) * I)) := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    simp only [hF]
    rw [arc_factor (sq_lt_one_of_mem hx)]
    ring
  rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_comp_neg (fun x => F x), neg_neg,
    intervalIntegral.integral_congr h2, intervalIntegral.integral_neg]

end Mob

/-! ## Stokes for one matrix -/

lemma iiSide {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) (hq : GoodQ g) (m : ℕ) (c : ℂ)
    (hc : c.im = 0) {Y : ℝ} (hY : 0 < Y) :
    IntervalIntegrable (fun y : ℝ => VG g m (c + y * I)) volume (arcH (1 / 2)) Y := by
  apply ContinuousOn.intervalIntegrable
  refine (contOn_VG hdet hq m).comp (by fun_prop : Continuous fun y : ℝ => c + y * I).continuousOn ?_
  intro y hy
  have hy0 : 0 < y := by
    rcases Set.mem_uIcc.1 hy with h | h
    · exact lt_of_lt_of_le arcH_half_pos h.1
    · exact lt_of_lt_of_le hY h.1
  simp [hc, hy0]

theorem stokes_g {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) (hq : GoodQ g) (m : ℕ) (hm : 1 ≤ m)
    {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ p in regY Y, phiG (m + 1) g (UpperHalfPlane.ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2) =
      -(topI g m Y - arcI g m + I * (sideA g m Y - sideB g m Y)) := by
  have hcongr : ∀ p ∈ regY Y,
      phiG (m + 1) g (UpperHalfPlane.ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2) =
        -(Vy g m ((p.1 : ℂ) + p.2 * I) + I * Vx g m ((p.1 : ℂ) + p.2 * I)) := by
    intro p hp
    have hy : 0 < ((p.1 : ℂ) + p.2 * I).im := by simpa using im_pos_of_mem_regY hp
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hy]
    have := V_identity_phiG m hm hdet ⟨(p.1 : ℂ) + p.2 * I, hy⟩ (hq _ hy)
    have e2 : (⟨(p.1 : ℂ) + p.2 * I, hy⟩ : UpperHalfPlane).im = p.2 := by
      show ((p.1 : ℂ) + p.2 * I).im = p.2
      simp
    rw [e2] at this
    exact this.symm
  rw [setIntegral_congr_fun (isClosed_regY Y).measurableSet hcongr, integral_neg,
    stokes_regY (V := VG g m) (Vx := Vx g m) (Vy := Vy g m)
      (fun x y hy => hasDerivAt_V_x g m x y hy (Cf_conj_ne_zero hdet (by simpa using hy))
        (hq _ (by simpa using hy)))
      (fun x y hy => hasDerivAt_V_y g m x y hy (Cf_conj_ne_zero hdet (by simpa using hy))
        (hq _ (by simpa using hy)))
      (contOn_VG hdet hq m) (contOn_Vx hdet hq m) (contOn_Vy hdet hq m) hY]
  unfold topI arcI sideA sideB
  rw [intervalIntegral.integral_sub (iiSide hdet hq m (1 / 2) (by simp) (by linarith))
    (iiSide hdet hq m (-(1 / 2)) (by simp) (by linarith))]

end RamanujanPetersson.HypPar


