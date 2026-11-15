-- Prove2me | Definitions.Def_RPLib_S3_EllW2J
-- name    : RPLib_S3_EllW2J
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:21:49.233222+00:00
-- url     : https://prove2.me/theorems/c8dbdf07-8d42-4b06-99fc-137a80992e0a
-- title:
--   The Eichler-Selberg trace formula in weight two: the `c ≠ 0` split/parabolic top edges vanish at `m = 1`
-- statement:
--   The `c ≠ 0` split/parabolic top edges vanish at `m = 1`.
--
--   * `norm_VG_one_le`: for `c ≠ 0`, `0 ≤ D ≤ 2y²`, `|x| ≤ 1/2`, `y ≥ 1`: `‖V_g(z)‖ ≤ 32 / (y (c² + e²))`, `e = d - a`.
--   * `disc_facts`, `norm_topI_one_le` (split/parabolic `g` of determinant `n`, `8 n² ≤ Y²`).
--   * `summable_SPc_E`: `Σ_{det n, IsSP, c ≠ 0} (c² + e²)⁻¹ < ∞`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2H

/-!
# S3-ES-Wt2 (O6, part J): the `c ≠ 0` split/parabolic top edges vanish at `m = 1`

* `norm_VG_one_le`: for `c ≠ 0`, `0 ≤ D ≤ 2y²`, `|x| ≤ 1/2`, `y ≥ 1`: `‖V_g(z)‖ ≤ 32 / (y (c² + e²))`, `e = d - a`.
* `disc_facts`, `norm_topI_one_le` (split/parabolic `g` of determinant `n`, `8 n² ≤ Y²`).
* `summable_SPc_E`: `Σ_{det n, IsSP, c ≠ 0} (c² + e²)⁻¹ < ∞`.
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate MatrixGroups Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

/-- Pure-real core of the top-edge bound. -/
lemma key_ineq {c e p y D x : ℝ} (hc2 : 1 ≤ c ^ 2) (hy : 1 ≤ y) (hx2 : x ^ 2 ≤ 1 / 4)
    (hD : D ≤ 2 * y ^ 2) (hid : 4 * c * p = (2 * c * x + e) ^ 2 + 4 * c ^ 2 * y ^ 2 - D) :
    y ^ 2 * (c ^ 2 + e ^ 2) ≤ 32 * p ^ 2 := by
  have hy2 : 1 ≤ y ^ 2 := by nlinarith
  have hcx : (2 * c * x) ^ 2 ≤ c ^ 2 := by
    have := mul_le_mul_of_nonneg_left hx2 (sq_nonneg c); nlinarith
  have hX : e ^ 2 / 2 - c ^ 2 ≤ (2 * c * x + e) ^ 2 := by
    nlinarith [sq_nonneg (2 * (2 * c * x) + e)]
  have hcy : c ^ 2 ≤ c ^ 2 * y ^ 2 := by nlinarith
  have hDc : D ≤ 2 * c ^ 2 * y ^ 2 := by nlinarith
  have hW : e ^ 2 / 2 + c ^ 2 * y ^ 2 ≤ 4 * c * p := by rw [hid]; linarith
  have hc0 : 0 < c ^ 2 := lt_of_lt_of_le one_pos hc2
  have hW0 : 0 ≤ e ^ 2 / 2 + c ^ 2 * y ^ 2 := by positivity
  have h16 : (e ^ 2 / 2 + c ^ 2 * y ^ 2) ^ 2 ≤ 16 * c ^ 2 * p ^ 2 := by
    calc (e ^ 2 / 2 + c ^ 2 * y ^ 2) ^ 2 ≤ (4 * c * p) ^ 2 := pow_le_pow_left₀ hW0 hW 2
      _ = 16 * c ^ 2 * p ^ 2 := by ring
  have hW1 : c ^ 2 * y ^ 2 ≤ e ^ 2 / 2 + c ^ 2 * y ^ 2 := by
    have : 0 ≤ e ^ 2 / 2 := by positivity
    linarith
  have hE0 : 0 ≤ c ^ 2 + e ^ 2 := by positivity
  have hW2 : c ^ 2 + e ^ 2 ≤ 2 * (e ^ 2 / 2 + c ^ 2 * y ^ 2) := by linarith
  have h1 : c ^ 2 * y ^ 2 * (c ^ 2 + e ^ 2) ≤
      (e ^ 2 / 2 + c ^ 2 * y ^ 2) * (2 * (e ^ 2 / 2 + c ^ 2 * y ^ 2)) :=
    mul_le_mul hW1 hW2 hE0 hW0
  have e1 : c ^ 2 * (y ^ 2 * (c ^ 2 + e ^ 2)) = c ^ 2 * y ^ 2 * (c ^ 2 + e ^ 2) := by ring
  have e2 : (e ^ 2 / 2 + c ^ 2 * y ^ 2) * (2 * (e ^ 2 / 2 + c ^ 2 * y ^ 2)) =
      2 * (e ^ 2 / 2 + c ^ 2 * y ^ 2) ^ 2 := by ring
  have e3 : c ^ 2 * (32 * p ^ 2) = 2 * (16 * c ^ 2 * p ^ 2) := by ring
  have h2 : c ^ 2 * (y ^ 2 * (c ^ 2 + e ^ 2)) ≤ c ^ 2 * (32 * p ^ 2) := by
    rw [e1, e3]; rw [e2] at h1; linarith
  exact le_of_mul_le_mul_left h2 hc0

/-- Pure-real final step of the top-edge bound. -/
lemma vg_real {y E p Cn Qn : ℝ} (hy : 0 < y) (hE : 0 < E) (hk : y ^ 2 * E ≤ 32 * p ^ 2)
    (hC : p ^ 2 ≤ Cn) (hq : p ^ 2 ≤ Qn) : y ^ 2 / (Cn * Qn) ≤ (32 / (y * E)) ^ 2 := by
  have hp2 : 0 < p ^ 2 := by
    have : 0 < y ^ 2 * E := by positivity
    linarith
  calc y ^ 2 / (Cn * Qn) ≤ y ^ 2 / (p ^ 2 * p ^ 2) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hp2 hp2)
          (mul_le_mul hC hq hp2.le (hp2.le.trans hC))
    _ ≤ (32 / (y * E)) ^ 2 := by
        rw [div_pow, div_le_div_iff₀ (mul_pos hp2 hp2) (by positivity)]
        have h3 : (y ^ 2 * E) ^ 2 ≤ (32 * p ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hk 2
        have e1 : y ^ 2 * (y * E) ^ 2 = (y ^ 2 * E) ^ 2 := by ring
        have e2 : (32 : ℝ) ^ 2 * (p ^ 2 * p ^ 2) = (32 * p ^ 2) ^ 2 := by ring
        rw [e1, e2]; exact h3

/-- **Top-edge bound at `m = 1`.** -/
lemma norm_VG_one_le {g : Matrix (Fin 2) (Fin 2) ℤ} (hc : g 1 0 ≠ 0)
    (hD0 : 0 ≤ ((g 0 0 : ℝ) + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0))
    {z : ℂ} (hx : |z.re| ≤ 1 / 2) (hy : 1 ≤ z.im)
    (hD : ((g 0 0 : ℝ) + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) ≤ 2 * z.im ^ 2) :
    ‖HypPar.VG g 1 z‖ ≤ 32 / (z.im * ((g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2)) := by
  have hc2 : (1 : ℝ) ≤ (g 1 0 : ℝ) ^ 2 := HypPar.one_le_c_sq hc
  have hy0 : 0 < z.im := by linarith
  have hx2 : z.re ^ 2 ≤ 1 / 4 := by
    have := abs_le.1 hx; nlinarith
  have hid : 4 * (g 1 0 : ℝ) * HypPar.Pf g z = (2 * (g 1 0 : ℝ) * z.re + ((g 1 1 : ℝ) - g 0 0)) ^ 2 +
      4 * (g 1 0 : ℝ) ^ 2 * z.im ^ 2 - (((g 0 0 : ℝ) + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) := by
    unfold HypPar.Pf; ring
  have hk := key_ineq hc2 hy hx2 hD hid
  have hE : 0 < (g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2 :=
    add_pos_of_pos_of_nonneg (lt_of_lt_of_le one_pos hc2) (sq_nonneg _)
  have hC : HypPar.Pf g z ^ 2 ≤ normSq (HypPar.Cf g z (conj z)) := by
    rw [HypPar.normSq_Cf_conj]; exact le_add_of_nonneg_right (by positivity)
  have hq : HypPar.Pf g z ^ 2 ≤ normSq (HypPar.qf g (conj z)) := by
    rw [HypPar.normSq_qf_conj]; exact le_add_of_nonneg_right (mul_nonneg hD0 (sq_nonneg _))
  have hfin : 0 ≤ 32 / (z.im * ((g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2)) :=
    div_nonneg (by norm_num) (mul_pos hy0 hE).le
  have hV : HypPar.VG g 1 z = HypPar.uf g 1 z (conj z) := by
    unfold HypPar.VG; rw [Nat.cast_one, div_one]
  rw [hV]
  apply le_of_pow_le_pow_left₀ (n := 2) two_ne_zero hfin
  rw [HypPar.normSq_uf_conj, pow_one, pow_one]
  exact vg_real hy0 hE hk hC hq

/-- The discriminant of a split/parabolic `g` of determinant `n`. -/
lemma disc_facts {n : ℤ} (hn : 0 < n) {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : g.det = n) (hsp : IsSP g) :
    0 ≤ ((g 0 0 : ℝ) + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) ∧
    ((g 0 0 : ℝ) + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) ≤ 16 * (n : ℝ) ^ 2 := by
  obtain ⟨r, hr⟩ := hsp
  rw [hdet] at hr
  have ht := abs_tr_le hn hr
  have hdet' : g 0 0 * g 1 1 - g 0 1 * g 1 0 = n := by rw [← Matrix.det_fin_two]; exact hdet
  have e1 : ((g 0 0 : ℝ) + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) = ((r ^ 2 : ℤ) : ℝ) := by
    rw [← hr, ← hdet']; push_cast; ring
  have e2 : ((g 0 0 : ℝ) + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) =
      ((g 0 0 : ℝ) + g 1 1) ^ 2 - 4 * n := by
    rw [← hdet']; push_cast; ring
  have ht' : |((g 0 0 : ℝ) + g 1 1)| ≤ 4 * (n : ℝ) := by exact_mod_cast ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht2 : ((g 0 0 : ℝ) + g 1 1) ^ 2 ≤ (4 * (n : ℝ)) ^ 2 :=
    sq_le_sq' (abs_le.1 ht').1 (abs_le.1 ht').2
  constructor
  · rw [e1]; push_cast; positivity
  · rw [e2]; nlinarith

lemma norm_topI_one_le {n : ℤ} (hn : 0 < n) {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : g.det = n)
    (hsp : IsSP g) (hc : g 1 0 ≠ 0) {Y : ℝ} (hY : 1 ≤ Y) (hYn : 8 * (n : ℝ) ^ 2 ≤ Y ^ 2) :
    ‖HypPar.topI g 1 Y‖ ≤ 32 / (Y * ((g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2)) := by
  obtain ⟨hD0, hD1⟩ := disc_facts hn hdet hsp
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    (C := 32 / (Y * ((g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2)))
    (f := fun x : ℝ => HypPar.VG g 1 (x + Y * I)) (fun x hx => by
      rw [uIoc_of_le (by norm_num)] at hx
      have hre : ((x : ℂ) + Y * I).re = x := by simp
      have him : ((x : ℂ) + Y * I).im = Y := by simp
      have := norm_VG_one_le hc hD0 (z := (x : ℂ) + Y * I)
        (by rw [hre]; exact abs_le.2 ⟨hx.1.le, hx.2⟩) (by rw [him]; exact hY) (by rw [him]; linarith)
      rwa [him] at this)
  refine h.trans_eq ?_
  norm_num

/-- `Σ_{det n, IsSP, c ≠ 0} (c² + (d - a)²)⁻¹ < ∞`. -/
lemma summable_SPc_E {n : ℤ} (hn : 0 < n) :
    Summable ({g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g ∧ g 1 0 ≠ 0}.indicator
      (fun g => ((g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2)⁻¹)) := by
  rw [← summable_subtype_iff_indicator]
  set Ψ' : {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g ∧ g 1 0 ≠ 0} →
      (ℤ × Bool) × ((ℕ × ℕ) × ℤ) := fun g => Psi n g.1 with hΨ'
  have hinj : Function.Injective Ψ' := by
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
    simp only [hΨ', Psi, Prod.mk.injEq, decide_eq_decide] at h
    obtain ⟨⟨ht, hs⟩, ⟨hc1, hc2⟩, he⟩ := h
    have hm := c1_mul_c2 n (g := g)
    have hm' := c1_mul_c2 n (g := g')
    have hca : (g 1 0).natAbs = (g' 1 0).natAbs := by rw [← hm, ← hm', hc1, hc2]
    have hc : g 1 0 = g' 1 0 := by
      rcases Int.natAbs_eq_natAbs_iff.1 hca with h | h
      · exact h
      · have h1 : g 1 0 ≠ 0 := hg.2.2
        rcases lt_or_gt_of_ne h1 with hlt | hgt
        · have : ¬ (0 < g' 1 0) := fun hp => absurd (hs.2 hp) (by omega)
          omega
        · have := hs.1 hgt
          omega
    have ha : g 0 0 = g' 0 0 := by omega
    have hd : g 1 1 = g' 1 1 := by omega
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = n := by rw [← Matrix.det_fin_two]; exact hg.1
    have hdet' : g' 0 0 * g' 1 1 - g' 0 1 * g' 1 0 = n := by
      rw [← Matrix.det_fin_two]; exact hg'.1
    rw [← ha, ← hd, ← hc] at hdet'
    have hb : g 0 1 = g' 0 1 := by
      apply mul_right_cancel₀ (show g 1 0 ≠ 0 from hg.2.2)
      linarith
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  refine ((summable_Gfun n).comp_injective hinj).of_nonneg_of_le (fun g => by
      show (0 : ℝ) ≤ ((g.1 1 0 : ℝ) ^ 2 + ((g.1 1 1 : ℝ) - g.1 0 0) ^ 2)⁻¹
      positivity)
    (fun ⟨g, hg⟩ => ?_)
  obtain ⟨hdet, hsp, hc⟩ := hg
  have htr : |g 0 0 + g 1 1| ≤ 4 * n := by
    obtain ⟨r, hr⟩ := hsp
    rw [hdet] at hr
    exact abs_tr_le hn hr
  have h1 := c1_pos n hc
  have h2 := c2_pos n hc
  have hmem : (g 1 1 - g 0 0) ∈ {e : ℤ | ((c1f n g : ℕ) : ℤ) ∣ Rt n (g 0 0 + g 1 1) - e ∧
      ((c2f n g : ℕ) : ℤ) ∣ Rt n (g 0 0 + g 1 1) + e} := ⟨c1_dvd n g, c2_dvd hdet hsp hc⟩
  have hG : Gfun n (Psi n g) =
      2 * Gin (Rt n (g 0 0 + g 1 1)) ((c1f n g, c2f n g), g 1 1 - g 0 0) := if_pos htr
  have hGi : Gin (Rt n (g 0 0 + g 1 1)) ((c1f n g, c2f n g), g 1 1 - g 0 0) =
      (((c1f n g * c2f n g : ℕ) : ℝ) ^ 2 + ((g 1 1 - g 0 0 : ℤ) : ℝ) ^ 2)⁻¹ := by
    show (if 1 ≤ c1f n g ∧ 1 ≤ c2f n g then _ else 0) = _
    rw [if_pos (And.intro h1 h2)]
    exact Set.indicator_of_mem hmem _
  show ((g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2)⁻¹ ≤ Gfun n (Psi n g)
  rw [hG, hGi, c1_mul_c2]
  have hcR : (((g 1 0).natAbs : ℕ) : ℝ) ^ 2 = (g 1 0 : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [hcR]
  push_cast
  have hX : 0 ≤ ((g 1 0 : ℝ) ^ 2 + ((g 1 1 : ℝ) - g 0 0) ^ 2)⁻¹ := by positivity
  linarith

end RamanujanPetersson.EllW2


