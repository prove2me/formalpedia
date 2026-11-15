-- Prove2me | Definitions.Def_RPLib_S3_EllW2NZ
-- name    : RPLib_S3_EllW2NZ
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:49:44.84542+00:00
-- url     : https://prove2.me/theorems/359c1b5c-6862-4847-810a-4cc56621e98b
-- title:
--   The Eichler-Selberg trace formula in weight two: the zero mode of the non-split hyperbolic part in `(c, t)` form
-- statement:
--   The zero mode of the non-split hyperbolic part in `(c, t)` form.
--
--   * `continuous_VN_u`, `integrable_VN_u`: the profile `VN` (file PN3) in the shifted variable `u`.
--   * `Q_eq_neg_conj_Qp`, `phiG_two_ofC`: at `z = x + y i`, `φ_g(z) = Qp⁻² y²` with `u = x + (d - a)/(2c)`, `t = a + d`.
--   * `VNZ` (`VN`, extended by `0` at `c = 0`); `zmF_NHS`: the `NHS` summand is `zmF wtN VNZ`.
--   * `norm_zmF_NHS`, `integral_norm_zmF_NHS` (`= n^s zA`), `summable_integral_zmF_NHS`, `integrable_VNZ`.
--   * **`zeroMode_NHS`**: `∫_{-1/2}^{1/2} NHS_s(x + y i) dx = Σ'_{(c,t)} Wc(c,t) ∫_u VNZ(c,t,u)` (`y ≥ 1/2`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2PN4
import Definitions.Def_RPLib_S3_EllW2Z4

/-!
# S3-ES-Wt2 (O6, file NZ): the zero mode of the non-split hyperbolic part in `(c, t)` form

* `continuous_VN_u`, `integrable_VN_u`: the profile `VN` (file PN3) in the shifted variable `u`.
* `Q_eq_neg_conj_Qp`, `phiG_two_ofC`: at `z = x + y i`, `φ_g(z) = Qp⁻² y²` with `u = x + (d - a)/(2c)`, `t = a + d`.
* `VNZ` (`VN`, extended by `0` at `c = 0`); `zmF_NHS`: the `NHS` summand is `zmF wtN VNZ`.
* `norm_zmF_NHS`, `integral_norm_zmF_NHS` (`= n^s zA`), `summable_integral_zmF_NHS`, `integrable_VNZ`.
* **`zeroMode_NHS`**: `∫_{-1/2}^{1/2} NHS_s(x + y i) dx = Σ'_{(c,t)} Wc(c,t) ∫_u VNZ(c,t,u)` (`y ≥ 1/2`).
-/

open MeasureTheory Set Filter Complex
open UpperHalfPlane hiding I
open scoped ComplexConjugate MatrixGroups Modular Topology Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-! ## `VN` in the shifted variable `u` -/

lemma continuous_VN_u (s : ℝ) {c n y : ℝ} (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    Continuous fun u => VN s c n u y t := by
  have hQ : Continuous fun u => Qp c n u y t := by unfold Qp Pq; fun_prop
  have hR : Continuous fun u => Rp c n u y t := by unfold Rp RcN; fun_prop
  unfold VN
  refine continuous_const.mul (((hQ.pow 2).inv₀ fun u =>
    pow_ne_zero 2 (Qp_ne_zero (u := u) hc hy hn t)).mul ?_)
  exact Complex.continuous_ofReal.comp
    (hR.rpow_const fun u => Or.inl (Rp_pos (u := u) hc hy hn t).ne')

lemma integrable_VN_u {s : ℝ} (hs : 0 ≤ s) {c n y : ℝ} (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n)
    (t : ℝ) : Integrable fun u => VN s c n u y t :=
  ((integrable_VS_u hs hc hy hn t).const_mul (n ^ s)).mono'
    (continuous_VN_u s hc hy.ne' hn t).aestronglyMeasurable
    (Eventually.of_forall fun u => (norm_VN (u := u) s hc hy.ne' hn t).le)

/-! ## `φ_g` at `x + y i` in terms of `Qp` -/

lemma Pq_eq_g {g : Matrix (Fin 2) (Fin 2) ℤ} (hc : g 1 0 ≠ 0) (x y : ℝ) :
    Pq (g 1 0) g.det (x + ((g 1 1 : ℝ) - g 0 0) / (2 * g 1 0)) y (trR g) =
      (g 1 0 : ℝ) * (x ^ 2 + y ^ 2) - ((g 0 0 : ℝ) - g 1 1) * x - g 0 1 := by
  have hc' : (g 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
  unfold Pq trR
  rw [Matrix.det_fin_two]
  push_cast
  field_simp
  ring

/-- `Q(g; z, -z̄) = -conj Qp` at `z = x + y i`. -/
lemma Q_eq_neg_conj_Qp {g : Matrix (Fin 2) (Fin 2) ℤ} (hc : g 1 0 ≠ 0) (x y : ℝ) :
    Q g ((x : ℂ) + y * I) (-conj ((x : ℂ) + y * I)) =
      -conj (Qp (g 1 0) g.det (x + ((g 1 1 : ℝ) - g 0 0) / (2 * g 1 0)) y (trR g)) := by
  unfold Qp
  rw [Pq_eq_g hc x y]
  unfold Q trR
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  linear_combination ((g 1 0 : ℂ) * (y : ℂ) ^ 2) * I_sq

lemma phiG_two_ofC {g : Matrix (Fin 2) (Fin 2) ℤ} (hc : g 1 0 ≠ 0) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    phiG 2 g (ofComplex ((x : ℂ) + y * I)) =
      (Qp (g 1 0) g.det (x + ((g 1 1 : ℝ) - g 0 0) / (2 * g 1 0)) y (trR g) ^ 2)⁻¹ *
        ((y : ℂ) ^ 2) := by
  have hy' : 0 < ((x : ℂ) + y * I).im := by simpa using hy
  have hz : ((ofComplex ((x : ℂ) + y * I) : ℍ) : ℂ) = (x : ℂ) + y * I := by
    rw [ofComplex_apply_of_im_pos hy']
    try rfl
  have him : ((x : ℂ) + y * I).im = y := by simp
  unfold phiG
  rw [← UpperHalfPlane.coe_im, hz, him, Q_eq_neg_conj_Qp hc x y]
  simp only [map_inv₀, map_pow, Complex.conj_conj, neg_sq]

/-! ## The `NHS` summand as `zmF` -/

/-- The NHS zero-mode profile, extended by `0` at `c = 0`. -/
def VNZ (n : ℤ) (s y : ℝ) (c t : ℤ) (u : ℝ) : ℂ :=
  if c = 0 then 0 else VN s c n u y t

lemma VNZ_of_ne (n : ℤ) (s y : ℝ) {c : ℤ} (hc : c ≠ 0) (t : ℤ) :
    VNZ n s y c t = fun u => VN s c n u y t := by
  funext u; unfold VNZ; rw [if_neg hc]

lemma VNZ_zero (n : ℤ) (s y : ℝ) (t : ℤ) : VNZ n s y 0 t = fun _ => 0 := by
  funext u; unfold VNZ; rw [if_pos rfl]

lemma zmF_NHS (n : ℤ) (δ' : ZMod M) (s : ℝ) {y : ℝ} (hy : 0 < y) (g : S3.Conj.Mat) (x : ℝ) :
    wtN M n δ' g * (phiG 2 g (ofComplex ((x : ℂ) + y * I)) *
      (((n : ℝ) ^ s * Rc g x y ^ (-s) : ℝ) : ℂ)) = zmF (wtN M n δ') (VNZ n s y) g x := by
  by_cases h : g 1 0 ≠ 0 ∧ g.det = n
  · obtain ⟨hc, hd⟩ := h
    unfold zmF VNZ
    rw [if_neg hc, phiG_two_ofC hc x hy, Rc_eq_RcN g hc x y, hd]
    unfold VN Rp
    have ht : ((g 0 0 + g 1 1 : ℤ) : ℝ) = trR g := by unfold trR; push_cast; ring
    rw [ht]
    push_cast
    ring
  · have hw : wtN M n δ' g = 0 := by
      by_cases hc : g 1 0 = 0
      · exact wtN_c0 n δ' g hc
      · exact wtN_det n δ' g fun hd => h ⟨hc, hd⟩
    unfold zmF; rw [hw, zero_mul, zero_mul]

lemma norm_zmF_NHS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (s : ℝ) {y : ℝ} (hy : 0 < y)
    (g : S3.Conj.Mat) (x : ℝ) :
    ‖zmF (wtN M n δ') (VNZ n s y) g x‖ = (n : ℝ) ^ s * (‖wtN M n δ' g‖ * Rc g x y ^ (-s - 1)) := by
  by_cases h : g 1 0 ≠ 0 ∧ g.det = n
  · obtain ⟨hc, hd⟩ := h
    have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
    have hc' : ((g 1 0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hc
    unfold zmF VNZ
    rw [if_neg hc, norm_mul, norm_VN s hc' hy.ne' hn', Rc_eq_RcN g hc x y]
    unfold VS Rp trR
    rw [hd, Int.cast_add]
    ring
  · have hw : wtN M n δ' g = 0 := by
      by_cases hc : g 1 0 = 0
      · exact wtN_c0 n δ' g hc
      · exact wtN_det n δ' g fun hd => h ⟨hc, hd⟩
    unfold zmF; simp [hw]

lemma integral_norm_zmF_NHS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (s : ℝ) {y : ℝ} (hy : 0 < y)
    (g : S3.Conj.Mat) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖zmF (wtN M n δ') (VNZ n s y) g x‖ =
      (n : ℝ) ^ s * zA M n δ' s y g := by
  unfold zA
  simp_rw [norm_zmF_NHS hn δ' s hy g]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

lemma summable_integral_zmF_NHS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ}
    (hy : 1 / 2 ≤ y) :
    Summable fun g => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), zmF (wtN M n δ') (VNZ n s y) g x := by
  have hy0 : 0 < y := by linarith
  refine Summable.of_norm_bounded ((summable_zA hn δ' hs hy).mul_left ((n : ℝ) ^ s)) fun g => ?_
  exact (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans_eq
    (integral_norm_zmF_NHS hn δ' s hy0 g)

lemma integrable_VNZ {n : ℤ} (hn : 0 ≤ n) {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y) (c t : ℤ) :
    Integrable (VNZ n s y c t) := by
  by_cases hc : c = 0
  · subst hc; rw [VNZ_zero]; exact integrable_zero _ _ _
  · rw [VNZ_of_ne n s y hc]
    exact integrable_VN_u hs (by exact_mod_cast hc) hy (by exact_mod_cast hn) (t : ℝ)

/-! ## The zero-mode identity -/

/-- **The zero mode of the non-split hyperbolic part in `(c, t)` form** (`y ≥ 1/2`). -/
theorem zeroMode_NHS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ}
    (hy : 1 / 2 ≤ y) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), NHS M n δ' s (ofComplex ((x : ℂ) + y * I)) =
      ∑' ct : ℤ × ℤ, Wc M n δ' ct.1 ct.2 * ∫ u, VNZ n s y ct.1 ct.2 u := by
  have hy0 : 0 < y := by linarith
  have hab : (-(1 / 2 : ℝ)) ≤ 1 / 2 := by norm_num
  have hpt : ∀ x : ℝ, NHS M n δ' s (ofComplex ((x : ℂ) + y * I)) =
      ∑' g, zmF (wtN M n δ') (VNZ n s y) g x := by
    intro x
    obtain ⟨hre, him⟩ := re_im_ofC (p := (x, y)) hy0
    dsimp only at hre him
    rw [NHS_eq hn δ' s, hre, him]
    exact tsum_congr fun g => zmF_NHS n δ' s hy0 g x
  have hV : ∀ c t, Integrable (VNZ n s y c t) := integrable_VNZ hn.le hs.le hy0
  have hint : ∀ g, Integrable (zmF (wtN M n δ') (VNZ n s y) g) := fun g =>
    ((hV _ _).comp_add_right _).const_mul (wtN M n δ' g)
  have hw : ∀ g, wtN M n δ' (tconj 1 g) = wtN M n δ' g := wtN_tconj n δ'
  have hw0 : ∀ g, g 1 0 = 0 → wtN M n δ' g = 0 := wtN_c0 n δ'
  have hwd : ∀ g, g.det ≠ n → wtN M n δ' g = 0 := wtN_det n δ'
  have hsum := summable_integral_zmF_NHS hn δ' hs hy
  have h0 : ∀ g, g 1 0 = 0 → ∀ x, zmF (wtN M n δ') (VNZ n s y) g x = 0 := by
    intro g hg x; unfold zmF; rw [hw0 g hg, zero_mul]
  have hsumR : Summable fun r : {g // IsRep g} =>
      wtN M n δ' r.1 * ∫ u, VNZ n s y (r.1 1 0) (r.1 0 0 + r.1 1 1) u := by
    refine (summable_unfold_T _ (zmF_tconj _ _ hw hw0) h0 hint hsum).congr fun r => ?_
    unfold zmF; rw [integral_const_mul, integral_add_right_eq_self]
  have hZ := zero_mode_ct n (wtN M n δ') (VNZ n s y) hw hw0 hwd hV hsum hsumR
  have hI : ∀ g, IntegrableOn (zmF (wtN M n δ') (VNZ n s y) g) (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) :=
    fun g => (hint g).integrableOn
  have hsumN : Summable fun g => ∫ x in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
      ‖zmF (wtN M n δ') (VNZ n s y) g x‖ := by
    have e : ∀ g, ∫ x in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2), ‖zmF (wtN M n δ') (VNZ n s y) g x‖ =
        (n : ℝ) ^ s * zA M n δ' s y g := by
      intro g
      rw [← intervalIntegral.integral_of_le hab]
      exact integral_norm_zmF_NHS hn δ' s hy0 g
    simp_rw [e]
    exact (summable_zA hn δ' hs hy).mul_left _
  have : Countable S3.Conj.Mat := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  have hcongr : (∫ x in (-(1 / 2 : ℝ))..(1 / 2), NHS M n δ' s (ofComplex ((x : ℂ) + y * I))) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ∑' g, zmF (wtN M n δ') (VNZ n s y) g x :=
    intervalIntegral.integral_congr fun x _ => hpt x
  have hex : (∑' g, ∫ x in (-(1 / 2 : ℝ))..(1 / 2), zmF (wtN M n δ') (VNZ n s y) g x) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ∑' g, zmF (wtN M n δ') (VNZ n s y) g x := by
    rw [intervalIntegral.integral_of_le hab, ← integral_tsum_of_summable_integral_norm hI hsumN]
    exact tsum_congr fun g => intervalIntegral.integral_of_le hab
  rw [hcongr, ← hex]
  exact hZ.trans (tsum_congr fun ct => rfl)

end RamanujanPetersson.EllW2


