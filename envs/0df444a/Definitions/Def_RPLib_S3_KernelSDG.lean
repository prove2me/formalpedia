-- Prove2me | Definitions.Def_RPLib_S3_KernelSDG
-- name    : RPLib_S3_KernelSDG
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:44:59.429246+00:00
-- url     : https://prove2.me/theorems/658082de-7ced-41fe-a01d-8c1d14675c30
-- title:
--   The Eichler-Selberg trace formula in weight two: `K0 M · w` is holomorphic on the upper half-plane
-- statement:
--   `K0 M · w` is holomorphic on the upper half-plane.
--
--   * `differentiableOn_tsum_local`: Weierstrass M-test with local majorants.
--   * `Gs_zero_eq`, `differentiableOn_Gs0`; `KG0_zero`, `differentiableOn_KG0`.
--   * `Eterm_zero`, `differentiableOn_Eterm0`, `maj_le_ball`, `differentiableOn_tsum_Eterm0`.
--   * `differentiableOn_MF0`, `norm_MF0_le`, `differentiableOn_tsum_MF0`.
--   * `differentiableOn_K0 : DifferentiableOn ℂ (fun z => K0 M z w) UHP`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelSDF

/-!
# S3-ES-Wt2, part KS_D (G): `K0 M · w` is holomorphic on the upper half-plane

* `differentiableOn_tsum_local`: Weierstrass M-test with local majorants.
* `Gs_zero_eq`, `differentiableOn_Gs0`; `KG0_zero`, `differentiableOn_KG0`.
* `Eterm_zero`, `differentiableOn_Eterm0`, `maj_le_ball`, `differentiableOn_tsum_Eterm0`.
* `differentiableOn_MF0`, `norm_MF0_le`, `differentiableOn_tsum_MF0`.
* `differentiableOn_K0 : DifferentiableOn ℂ (fun z => K0 M z w) UHP`.
-/

open Complex Filter Topology
open scoped Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelSD

open RamanujanPetersson.Kernel RamanujanPetersson.KernelS RamanujanPetersson.GSA

/-- The upper half-plane as a subset of `ℂ`. -/
def UHP : Set ℂ := {z : ℂ | 0 < z.im}

lemma isOpen_UHP : IsOpen UHP := isOpen_lt continuous_const Complex.continuous_im

theorem differentiableOn_tsum_local {ι : Type*} {F : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hloc : ∀ z0 ∈ U, ∃ V ∈ 𝓝 z0, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ V, ‖F i z‖ ≤ u i) :
    DifferentiableOn ℂ (fun z => ∑' i, F i z) U := by
  intro z0 hz0
  obtain ⟨V, hV, u, hu, hb⟩ := hloc z0 hz0
  obtain ⟨W, hWV, hWo, hz0W⟩ := mem_nhds_iff.1 hV
  have hd := differentiableOn_tsum_of_summable_norm hu
    (fun i => (hF i).mono Set.inter_subset_right) (hWo.inter hU) (fun i z hz => hb i z (hWV hz.1))
  exact (hd.differentiableAt ((hWo.inter hU).mem_nhds ⟨hz0W, hz0⟩)).differentiableWithinAt

/-! ### Elementary ball estimates -/

lemma half_le_norm {X X0 : ℂ} (h : ‖X - X0‖ ≤ ‖X0‖ / 2) : ‖X0‖ / 2 ≤ ‖X‖ := by
  have h1 := norm_sub_norm_le X0 X
  rw [norm_sub_rev] at h1
  linarith

lemma inv_pow_le_of_half {a b : ℝ} (hb : 0 < b) (h : b / 2 ≤ a) (k : ℕ) :
    (a ^ k)⁻¹ ≤ 2 ^ k * (b ^ k)⁻¹ := by
  have hb2 : 0 < b / 2 := by positivity
  calc (a ^ k)⁻¹ ≤ ((b / 2) ^ k)⁻¹ := inv_anti₀ (pow_pos hb2 k) (pow_le_pow_left₀ hb2.le h k)
    _ = 2 ^ k * (b ^ k)⁻¹ := by rw [div_pow, inv_div, div_eq_mul_inv]

lemma im_lt_of_ball {z z0 : ℂ} (hz : ‖z - z0‖ < z0.im / 2) : z0.im / 2 ≤ z.im := by
  have h := (abs_le.1 ((Complex.abs_im_le_norm (z - z0)).trans hz.le)).1
  rw [Complex.sub_im] at h
  linarith

lemma ball_bound {c d : ℤ} {z z0 : ℂ} (hz : ‖z - z0‖ < z0.im / 2) :
    ‖((c : ℂ) * z + d) - ((c : ℂ) * z0 + d)‖ ≤ ‖(c : ℂ) * z0 + d‖ / 2 := by
  have hy0 : 0 < z0.im := by linarith [norm_nonneg (z - z0)]
  have h1 : ((c : ℂ) * z + d) - ((c : ℂ) * z0 + d) = (c : ℂ) * (z - z0) := by ring
  have h2 : |(c : ℝ)| * z0.im ≤ ‖(c : ℂ) * z0 + d‖ := by
    have h := Complex.abs_im_le_norm ((c : ℂ) * z0 + d)
    rwa [im_lin, abs_mul, abs_of_pos hy0] at h
  rw [h1, norm_mul, Complex.norm_intCast]
  have h3 : |(c : ℝ)| * ‖z - z0‖ ≤ |(c : ℝ)| * (z0.im / 2) :=
    mul_le_mul_of_nonneg_left hz.le (abs_nonneg _)
  linarith

/-! ### `G_0` is holomorphic -/

lemma fS_zero_shift (ζ : ℂ) (n : ℤ) : fS 0 ζ.im (ζ.re + n) = ((ζ + n) ^ 2)⁻¹ := by
  rw [fS_shift]; simp

lemma Gs_zero_eq (ζ : ℂ) : Gs 0 ζ = ∑' n : ℤ, ((ζ + n) ^ 2)⁻¹ :=
  tsum_congr fun n => fS_zero_shift ζ n

lemma add_int_ne_zero {ζ : ℂ} (hζ : 0 < ζ.im) (n : ℤ) : ζ + n ≠ 0 := by
  intro h
  have h1 := congrArg Complex.im h
  rw [Complex.add_im, Complex.intCast_im, add_zero, Complex.zero_im] at h1
  linarith

theorem differentiableOn_Gs0 : DifferentiableOn ℂ (Gs 0) UHP := by
  have hsum : DifferentiableOn ℂ (fun ζ : ℂ => ∑' n : ℤ, ((ζ + n) ^ 2)⁻¹) UHP := by
    refine differentiableOn_tsum_local isOpen_UHP (fun n => ?_) fun ζ0 hζ0 => ?_
    · have hd : Differentiable ℂ (fun ζ : ℂ => (ζ + (n : ℂ)) ^ 2) := by fun_prop
      exact hd.differentiableOn.inv fun ζ hζ => pow_ne_zero 2 (add_int_ne_zero hζ n)
    · have hζ0' : 0 < ζ0.im := hζ0
      refine ⟨Metric.ball ζ0 (ζ0.im / 2), Metric.ball_mem_nhds _ (by positivity),
        fun n : ℤ => 2 ^ 2 * ‖fS 0 ζ0.im (ζ0.re + n)‖,
        (summable_norm_fS_shift le_rfl zero_le_one hζ0').mul_left _, fun n ζ hζ => ?_⟩
      have hz : ‖ζ - ζ0‖ < ζ0.im / 2 := by rw [← dist_eq_norm]; exact hζ
      have h2 : ζ0.im ≤ ‖ζ0 + n‖ := by
        have h := Complex.abs_im_le_norm (ζ0 + (n : ℂ))
        rwa [Complex.add_im, Complex.intCast_im, add_zero, abs_of_pos hζ0'] at h
      have h1 : ‖(ζ + n) - (ζ0 + n)‖ ≤ ‖ζ0 + n‖ / 2 := by
        rw [show (ζ + n) - (ζ0 + n) = ζ - ζ0 by ring]; linarith
      show ‖((ζ + n) ^ 2)⁻¹‖ ≤ 2 ^ 2 * ‖fS 0 ζ0.im (ζ0.re + n)‖
      rw [fS_zero_shift, norm_inv, norm_pow, norm_inv, norm_pow]
      exact inv_pow_le_of_half (norm_pos_iff.2 (add_int_ne_zero hζ0' n)) (half_le_norm h1) 2
  exact hsum.congr fun ζ _ => Gs_zero_eq ζ

/-! ### The three pieces at `s = 0` -/

lemma KG0_zero (M : ℕ) (z w : ℂ) : KG0 M 0 z w = ((M : ℂ) ^ 2)⁻¹ * Gs 0 ((z + w) / M) := by
  simp [KG0]

theorem differentiableOn_KG0 (M : ℕ) [NeZero M] {w : ℂ} (hv : 0 < w.im) :
    DifferentiableOn ℂ (fun z => KG0 M 0 z w) UHP := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hmaps : Set.MapsTo (fun z : ℂ => (z + w) / (M : ℂ)) UHP UHP := fun z hz => by
    show 0 < ((z + w) / (M : ℂ)).im
    rw [Complex.div_natCast_im, Complex.add_im]
    exact div_pos (add_pos hz hv) hMr
  have hd : DifferentiableOn ℂ (fun z : ℂ => (z + w) / (M : ℂ)) UHP := by fun_prop
  exact ((differentiableOn_Gs0.comp hd hmaps).const_mul (((M : ℂ) ^ 2)⁻¹)).congr
    fun z _ => KG0_zero M z w

lemma Eterm_zero (z w : ℂ) (p : ℤ × ℤ × ℤ) :
    Eterm 0 z w p = (p.1 : ℂ) ^ 2 * (((AC z w p - 1) ^ 2)⁻¹ - (AC z w p ^ 2)⁻¹) := by
  simp [Eterm, Ferr]

theorem differentiableOn_Eterm0 {M : ℕ} {w : ℂ} (hv : 0 < w.im) (p : Tset M) :
    DifferentiableOn ℂ (fun z => Eterm 0 z w p.1) UHP := by
  obtain ⟨⟨c, a, d⟩, hp⟩ := p
  have hc : c ≠ 0 := hp.1
  have hA : Differentiable ℂ (fun z => AC z w (c, a, d)) := by unfold AC; fun_prop
  have hne : ∀ z ∈ UHP, AC z w (c, a, d) ≠ 0 ∧ AC z w (c, a, d) - 1 ≠ 0 := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := AC_facts (a := a) (d := d) hc hz hv
    have hη : 0 < etaC z w c := (mul_pos hz hv).trans_le h1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, norm_zero] at h2; linarith
    · rw [h, norm_zero] at h3; norm_num at h3; linarith
  have hd : DifferentiableOn ℂ (fun z => ((c, a, d).1 : ℂ) ^ 2 *
      (((AC z w (c, a, d) - 1) ^ 2)⁻¹ - (AC z w (c, a, d) ^ 2)⁻¹)) UHP :=
    ((((hA.sub_const 1).pow 2).differentiableOn.inv fun z hz => pow_ne_zero 2 (hne z hz).2).sub
      ((hA.pow 2).differentiableOn.inv fun z hz => pow_ne_zero 2 (hne z hz).1)).const_mul _
  exact hd.congr fun z _ => Eterm_zero z w (c, a, d)

lemma maj_le_ball {c d a : ℤ} (hc : c ≠ 0) {z z0 w : ℂ} (hz : ‖z - z0‖ < z0.im / 2) :
    maj z w ((c, d), a) ≤ 2 ^ 3 * maj z0 w ((c, d), a) := by
  have hy0 : 0 < z0.im := by linarith [norm_nonneg (z - z0)]
  have hX0 : 0 < ‖(c : ℂ) * z0 + d‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have h1 := congrArg Complex.im h
    rw [im_lin, Complex.zero_im] at h1
    exact hc (Int.cast_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right hy0.ne'))
  have hb := inv_pow_le_of_half hX0 (half_le_norm (ball_bound (c := c) (d := d) hz)) 3
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (sq_nonneg (c : ℝ)))
    (inv_nonneg.2 (pow_nonneg (norm_nonneg ((c : ℂ) * w + a)) 3))
  unfold maj
  exact h.trans (le_of_eq (by ring))

theorem differentiableOn_tsum_Eterm0 (M : ℕ) {w : ℂ} (hv : 0 < w.im) :
    DifferentiableOn ℂ (fun z => ∑' p : Tset M, Eterm 0 z w p.1) UHP := by
  refine differentiableOn_tsum_local isOpen_UHP (fun p => differentiableOn_Eterm0 hv p)
    fun z0 hz0 => ?_
  have hz0' : 0 < z0.im := hz0
  have ht : 0 < z0.im / 2 * w.im := by positivity
  obtain ⟨hS, -⟩ := summable_maj hz0' le_rfl hv
  have hm := (hS.comp_injective iota_injective).comp_injective
    (Subtype.val_injective (p := fun p => p ∈ Tset M))
  refine ⟨Metric.ball z0 (z0.im / 2), Metric.ball_mem_nhds _ (by positivity), _,
    hm.mul_left (Kerr (z0.im / 2 * w.im) * 2 ^ 3), fun p z hz => ?_⟩
  have hz' : ‖z - z0‖ < z0.im / 2 := by rw [← dist_eq_norm]; exact hz
  have hyz := im_lt_of_ball hz'
  have hyz' : 0 < z.im := by linarith
  have hb := norm_Eterm_le' p le_rfl zero_le_one hyz' hv ht (mul_le_mul_of_nonneg_right hyz hv.le)
  obtain ⟨⟨c, a, d⟩, hp⟩ := p
  calc ‖Eterm 0 z w (c, a, d)‖ ≤ Kerr (z0.im / 2 * w.im) * maj z w (iota (c, a, d)) := hb
    _ ≤ Kerr (z0.im / 2 * w.im) * (2 ^ 3 * maj z0 w (iota (c, a, d))) :=
        mul_le_mul_of_nonneg_left (maj_le_ball (c := c) (d := d) (a := a) hp.1 hz') (Kerr_nonneg ht)
    _ = Kerr (z0.im / 2 * w.im) * 2 ^ 3 * maj z0 w (iota (c, a, d)) := by ring

lemma WtR_zero (M : ℕ) (t : ℝ) (c' : ℕ) : WtR M 0 t c' = WtR M 0 1 c' := by simp [WtR]

theorem differentiableOn_MF0 (M : ℕ) [NeZero M] (w : ℂ) (c' : ℕ) :
    DifferentiableOn ℂ (fun z => MF M 0 z w c') UHP := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hz : ∀ n : ℕ, DifferentiableOn ℂ (fun z => Gs 0 (zeta M c' z n)) UHP := fun n => by
    have hmaps : Set.MapsTo (fun z => zeta M c' z n) UHP UHP := fun z hz => by
      show 0 < (zeta M c' z n).im
      rw [im_zeta]; exact div_pos hz hMr
    have hdz : DifferentiableOn ℂ (fun z => zeta M c' z n) UHP := by unfold zeta; fun_prop
    exact differentiableOn_Gs0.comp hdz hmaps
  have hd : DifferentiableOn ℂ (fun z => ((WtR M 0 1 c' : ℝ) : ℂ) *
      ∑ x : (ZMod (Lm M c'))ˣ, chiU M c' x *
        (Gs 0 (zeta M c' z ((x⁻¹ : (ZMod (Lm M c'))ˣ) : ZMod (Lm M c')).val) *
          Gs 0 (zeta M c' w ((x : ZMod (Lm M c')).val)))) UHP := by
    refine DifferentiableOn.const_mul ?_ _
    apply DifferentiableOn.fun_sum
    intro x _
    exact ((hz _).mul_const _).const_mul _
  refine hd.congr fun z _ => ?_
  show MF M 0 z w c' = _
  unfold MF
  rw [WtR_zero M (z.im * w.im) c']

theorem norm_MF0_le {M : ℕ} [NeZero M] {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) (c' : ℕ) :
    ‖MF M 0 z w c'‖ ≤ Bnd (z.im / M) * Bnd (w.im / M) * ∑' mr, majF M (mr, c') := by
  have hT : (z.im * w.im) ^ (0 : ℝ) ≤ 1 := by rw [Real.rpow_zero]
  have hs : Summable (fun mr : ℤ × ℤ => majF M (mr, c')) :=
    (summable_majF M).comp_injective (Prod.mk_left_injective c')
  refine (hasSum_MF (M := M) le_rfl zero_le_one hy hv c').norm_le_of_bounded
    (hs.hasSum.mul_left (Bnd (z.im / M) * Bnd (w.im / M))) fun mr => ?_
  by_cases hmr : mr = 0
  · subst hmr
    rw [MFm_zero_s_zero hy, norm_zero]
    simp [majF]
  · have h := norm_MFm_le_T (M := M) le_rfl zero_le_one hy hv hT c' mr hmr
    rwa [one_mul] at h

theorem differentiableOn_tsum_MF0 (M : ℕ) [NeZero M] {w : ℂ} (hv : 0 < w.im) :
    DifferentiableOn ℂ (fun z => ∑' c' : ℕ, MF M 0 z w c') UHP := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  refine differentiableOn_tsum_local isOpen_UHP (fun c' => differentiableOn_MF0 M w c')
    fun z0 hz0 => ?_
  have hz0' : 0 < z0.im := hz0
  have hy1 : 0 < z0.im / 2 := by positivity
  refine ⟨Metric.ball z0 (z0.im / 2), Metric.ball_mem_nhds _ hy1,
    fun c' => π * rho (z0.im / 2 / M) ^ 2 / (z0.im / 2 / M) * Bnd (w.im / M) *
      ∑' mr, majS M (c', mr),
    (summable_majS M).prod.mul_left _, fun c' z hz => ?_⟩
  have hz' : ‖z - z0‖ < z0.im / 2 := by rw [← dist_eq_norm]; exact hz
  have hyz := im_lt_of_ball hz'
  have hyz' : 0 < z.im := by linarith
  have hB : Bnd (z.im / M) ≤ π * rho (z0.im / 2 / M) ^ 2 / (z0.im / 2 / M) :=
    Bnd_le (div_pos hy1 hMr) (div_le_div_of_nonneg_right hyz hMr.le) (div_pos hy1 hMr)
      (div_le_div_of_nonneg_right hyz hMr.le)
  have hBv : 0 ≤ Bnd (w.im / M) := (Bnd_pos (div_pos hv hMr)).le
  have hS : 0 ≤ ∑' mr, majF M (mr, c') := tsum_nonneg fun _ => majF_nonneg M _
  calc ‖MF M 0 z w c'‖ ≤ Bnd (z.im / M) * Bnd (w.im / M) * ∑' mr, majF M (mr, c') :=
        norm_MF0_le hyz' hv c'
    _ ≤ π * rho (z0.im / 2 / M) ^ 2 / (z0.im / 2 / M) * Bnd (w.im / M) * ∑' mr, majF M (mr, c') :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hBv) hS

/-- **(iii)** `K0 M · w` is holomorphic on the upper half-plane. -/
theorem differentiableOn_K0 (M : ℕ) [NeZero M] {w : ℂ} (hv : 0 < w.im) :
    DifferentiableOn ℂ (fun z => K0 M z w) UHP :=
  ((differentiableOn_KG0 M hv).add (differentiableOn_tsum_Eterm0 M hv)).add
    (differentiableOn_tsum_MF0 M hv)

end RamanujanPetersson.KernelSD


