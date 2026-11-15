-- Prove2me | Definitions.Def_RPLib_S3_EllW2N
-- name    : RPLib_S3_EllW2N
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:26:31.368135+00:00
-- url     : https://prove2.me/theorems/8838b45e-e703-4a0c-9a1f-b58759fa9269
-- title:
--   The Eichler-Selberg trace formula in weight two: the non-split hyperbolic boundary terms at `s > 0`
-- statement:
--   The non-split hyperbolic boundary terms at `s > 0`.
--
--   * `wtN`: the weight `[¬ IsSP] wt`; `wtN_conj`.
--   * `norm_VsF_le_N`: for `t² - 4 det ≥ 1`, `‖V_s‖ ≤ (1 + 4 det) / y · R^(-s-1)`.
--   * `norm_VsF_le_K`: on `InK Y`, `‖V_s‖ ≤ 2 (1 + 4 det) (N / (144 Y⁶))^(-s-1)`; `summable_ENs` (`s > 0`).
--   * the weighted `topIs/arcIs/sideAs/sideBs` are summable; arcs cancel under `S`, sides under `T`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2L2
import Definitions.Def_RPLib_S3_EllW2I

/-!
# S3-ES-Wt2 (O6, file N): the non-split hyperbolic boundary terms at `s > 0`

* `wtN`: the weight `[¬ IsSP] wt`; `wtN_conj`.
* `norm_VsF_le_N`: for `t² - 4 det ≥ 1`, `‖V_s‖ ≤ (1 + 4 det) / y · R^(-s-1)`.
* `norm_VsF_le_K`: on `InK Y`, `‖V_s‖ ≤ 2 (1 + 4 det) (N / (144 Y⁶))^(-s-1)`; `summable_ENs` (`s > 0`).
* the weighted `topIs/arcIs/sideAs/sideBs` are summable; arcs cancel under `S`, sides under `T`.
-/

open MeasureTheory Set Filter Complex
open UpperHalfPlane hiding I
open scoped ComplexConjugate MatrixGroups Modular Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

open Classical in
/-- The non-split hyperbolic rest weight `[¬ IsSP g] wt g`. -/
def wtN (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (g : S3.Conj.Mat) : ℂ :=
  if IsSP g then 0 else HypPar.wt M n δ' g

lemma wtN_of_not {n : ℤ} {δ' : ZMod M} {g : S3.Conj.Mat}
    (h : ¬(g.det = n ∧ HypPar.IsRest g ∧ ¬IsSP g)) : wtN M n δ' g = 0 := by
  unfold wtN
  split_ifs with hs
  · rfl
  · exact HypPar.wt_of_not (fun h' => h ⟨h'.1, h'.2, hs⟩)

lemma norm_wtN_le (n : ℤ) (δ' : ZMod M) (g : S3.Conj.Mat) :
    ‖wtN M n δ' g‖ ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) := by
  unfold wtN
  split_ifs
  · rw [norm_zero]; positivity
  · exact HypPar.norm_wt_le n δ' g

lemma wtN_conj (n : ℤ) (δ' : ZMod M) (h : SL(2, ℤ)) (g : S3.Conj.Mat) :
    wtN M n δ' (S3.Conj.conj h g) = wtN M n δ' g := by
  unfold wtN
  rw [HypPar.wt_conj]
  by_cases hs : IsSP g
  · rw [if_pos ((isSP_conj h g).2 hs), if_pos hs]
  · rw [if_neg (fun h' => hs ((isSP_conj h g).1 h')), if_neg hs]

lemma disc_ge_one {g : S3.Conj.Mat} (hr : HypPar.IsRest g) (hs : ¬IsSP g) :
    (1 : ℤ) ≤ (g 0 0 + g 1 1) ^ 2 - 4 * g.det := by
  have h1 : ¬ (g 0 0 + g 1 1) ^ 2 < 4 * g.det := fun h => hr (Or.inr h)
  have h2 : (g 0 0 + g 1 1) ^ 2 - 4 * g.det ≠ 0 := fun h => hs ⟨0, by rw [h]; ring⟩
  generalize (g 0 0 + g 1 1) ^ 2 = A at h1 h2 ⊢
  omega

/-! ## Pointwise bounds -/

lemma keyN_real (P y t2 d Δ : ℝ) (hd : 0 < d) (hΔ : 1 ≤ Δ) (ht : t2 = Δ + 4 * d) :
    P ^ 2 + t2 * y ^ 2 ≤ (1 + 4 * d) ^ 2 * (P ^ 2 + Δ * y ^ 2) := by
  subst ht
  have h1 : 0 ≤ (8 * d + 16 * d ^ 2) * P ^ 2 := by positivity
  have h2 : 0 ≤ (Δ - 1) * (8 * d + 16 * d ^ 2) * y ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by positivity)) (sq_nonneg y)
  have h3 : 0 ≤ (4 * d + 16 * d ^ 2) * y ^ 2 := by positivity
  nlinarith [h1, h2, h3]

lemma vgN_real {A B y R K : ℝ} (hA : 0 < A) (hB : 0 < B) (hy : 0 < y) (hR : 0 < R)
    (hAB : A ≤ K * B) (hAR : A ^ 2 = R * y ^ 2) : y / (A * B) ≤ K / (y * R) := by
  rw [div_le_div_iff₀ (mul_pos hA hB) (mul_pos hy hR)]
  nlinarith [mul_le_mul_of_nonneg_left hAB hA.le]

variable {g : Matrix (Fin 2) (Fin 2) ℤ}

lemma norm_VG_one_le_N (hdet : 0 < g.det) (hD : (1 : ℤ) ≤ (g 0 0 + g 1 1) ^ 2 - 4 * g.det)
    {z : ℂ} (hy : 0 < z.im) :
    ‖HypPar.VG g 1 z‖ ≤ (1 + 4 * (g.det : ℝ)) / (z.im * Rc g z.re z.im) := by
  have hdR : (g.det : ℝ) = (g 0 0 : ℝ) * g 1 1 - g 0 1 * g 1 0 := by
    rw [Matrix.det_fin_two]; push_cast; ring
  have hd : (0 : ℝ) < (g 0 0 : ℝ) * g 1 1 - g 0 1 * g 1 0 := by rw [← hdR]; exact_mod_cast hdet
  have hΔ : (1 : ℝ) ≤ ((g 0 0 : ℝ) + g 1 1) ^ 2 - 4 * ((g 0 0 : ℝ) * g 1 1 - g 0 1 * g 1 0) := by
    rw [← hdR]; exact_mod_cast hD
  have hC := HypPar.Cf_conj_ne_zero hdet hy
  have hqn : 0 < normSq (HypPar.qf g (conj z)) := by
    rw [HypPar.normSq_qf_conj]
    have : 0 < z.im ^ 2 := by positivity
    nlinarith [sq_nonneg (HypPar.Pf g z)]
  have hq : HypPar.qf g (conj z) ≠ 0 := fun h0 => by rw [h0, map_zero] at hqn; exact lt_irrefl _ hqn
  have hVG : HypPar.VG g 1 z = (z.im : ℂ) / (HypPar.Cf g z (conj z) * HypPar.qf g (conj z)) := by
    simp only [HypPar.VG, HypPar.uf, HypPar.Yf_conj, pow_one, Nat.cast_one, div_one]
  have hK : (0 : ℝ) ≤ 1 + 4 * (g.det : ℝ) := by rw [hdR]; linarith
  have h1 : ‖HypPar.Cf g z (conj z)‖ ^ 2 ≤ ((1 + 4 * (g.det : ℝ)) * ‖HypPar.qf g (conj z)‖) ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm, HypPar.normSq_Cf_conj, HypPar.normSq_qf_conj, hdR]
    exact keyN_real _ _ _ _ _ hd hΔ (by ring)
  have h2 : ‖HypPar.Cf g z (conj z)‖ ≤ (1 + 4 * (g.det : ℝ)) * ‖HypPar.qf g (conj z)‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _)) two_ne_zero).1 h1
  rw [hVG, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hy.le]
  exact vgN_real (norm_pos_iff.2 hC) (norm_pos_iff.2 hq) hy (Rc_pos hdet hy) h2
    (by rw [Complex.sq_norm]; exact (Rc_mul g hy.ne').symm)

lemma norm_VsF_le_N (hdet : 0 < g.det) (hD : (1 : ℤ) ≤ (g 0 0 + g 1 1) ^ 2 - 4 * g.det)
    {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hy : 0 < z.im) :
    ‖VsF g s z‖ ≤ (1 + 4 * (g.det : ℝ)) / z.im * Rc g z.re z.im ^ (-s - 1) := by
  have hR := Rc_pos hdet hy
  have hV := norm_VG_one_le_N hdet hD hy
  have h0 : 0 ≤ Rc g z.re z.im ^ (-s) := Real.rpow_nonneg hR.le _
  have hH : ‖((Hs g s z.re z.im : ℝ) : ℂ)‖ ≤ Rc g z.re z.im ^ (-s) := by
    rw [Complex.norm_real, Hs, Real.norm_of_nonneg (div_nonneg h0 (by linarith))]
    exact div_le_self h0 (by linarith)
  have hdp : (0 : ℝ) < g.det := by exact_mod_cast hdet
  unfold VsF
  rw [norm_mul]
  calc ‖HypPar.VG g 1 z‖ * ‖((Hs g s z.re z.im : ℝ) : ℂ)‖
      ≤ (1 + 4 * (g.det : ℝ)) / (z.im * Rc g z.re z.im) * Rc g z.re z.im ^ (-s) :=
        mul_le_mul hV hH (norm_nonneg _) (div_nonneg (by linarith) (mul_pos hy hR).le)
    _ = _ := by
        rw [Real.rpow_sub_one hR.ne']
        first | (field_simp; ring) | field_simp

lemma Rc_ge_K (hdet : 0 < g.det) {Y : ℝ} (hY : 1 ≤ Y) {z : ℂ} (hz : HypPar.InK Y z) :
    N g / (144 * Y ^ 6) ≤ Rc g z.re z.im := by
  have hy : 0 < z.im := by linarith [hz.2.1]
  have hN := HypPar.N_le_normSq_Q_K hdet hY hz
  have h1 := Rc_mul g hy.ne'
  rw [HypPar.Cf_conj, Complex.normSq_conj] at h1
  have hy2 : z.im ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hy.le hz.2.2 2
  have hR := Rc_pos hdet hy
  rw [div_le_iff₀ (by positivity)]
  have h3 := mul_le_mul_of_nonneg_left hy2 (le_of_lt (mul_pos (by positivity : (0 : ℝ) < 144 * Y ^ 4) hR))
  calc N g ≤ 144 * Y ^ 4 * normSq (Q g z (-conj z)) := hN
    _ = 144 * Y ^ 4 * (Rc g z.re z.im * z.im ^ 2) := by rw [h1]
    _ ≤ Rc g z.re z.im * (144 * Y ^ 6) := by nlinarith [h3]

/-- The summable majorant `(N g / (144 Y⁶))^(-s-1)`. -/
def ENs (s Y : ℝ) (g : Matrix (Fin 2) (Fin 2) ℤ) : ℝ := (N g / (144 * Y ^ 6)) ^ (-s - 1)

lemma ENs_nonneg (s Y : ℝ) (g : Matrix (Fin 2) (Fin 2) ℤ) : 0 ≤ ENs s Y g :=
  Real.rpow_nonneg (div_nonneg (by unfold N; positivity) (by positivity)) _

lemma norm_VsF_le_K (hdet : 0 < g.det) (hD : (1 : ℤ) ≤ (g 0 0 + g 1 1) ^ 2 - 4 * g.det)
    {s : ℝ} (hs : 0 ≤ s) {Y : ℝ} (hY : 1 ≤ Y) {z : ℂ} (hz : HypPar.InK Y z) :
    ‖VsF g s z‖ ≤ 2 * (1 + 4 * (g.det : ℝ)) * ENs s Y g := by
  have hy : 0 < z.im := by linarith [hz.2.1]
  have hdp : (0 : ℝ) < g.det := by exact_mod_cast hdet
  have hNK : 0 < N g / (144 * Y ^ 6) := div_pos (N_pos hdet) (by positivity)
  have hE : Rc g z.re z.im ^ (-s - 1) ≤ ENs s Y g :=
    Real.rpow_le_rpow_of_nonpos hNK (Rc_ge_K hdet hY hz) (by linarith)
  have hy2 : (1 + 4 * (g.det : ℝ)) / z.im ≤ 2 * (1 + 4 * (g.det : ℝ)) := by
    rw [div_le_iff₀ hy]; nlinarith [hz.2.1]
  calc ‖VsF g s z‖ ≤ (1 + 4 * (g.det : ℝ)) / z.im * Rc g z.re z.im ^ (-s - 1) :=
        norm_VsF_le_N hdet hD hs hy
    _ ≤ 2 * (1 + 4 * (g.det : ℝ)) * ENs s Y g :=
        mul_le_mul hy2 hE (Real.rpow_nonneg (Rc_pos hdet hy).le _) (by linarith)

lemma summable_ENs {n : ℤ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) (Y : ℝ) :
    Summable ({g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n}.indicator (ENs s Y)) := by
  rw [← summable_subtype_iff_indicator]
  refine ((summable_N_rpow hn (show (1 : ℝ) < 1 + s by linarith)).div_const
    ((144 * Y ^ 6) ^ (-s - 1))).congr fun g => ?_
  have hg : (g : Matrix (Fin 2) (Fin 2) ℤ).det = n := g.2
  show N g.1 ^ (-(1 + s)) / (144 * Y ^ 6) ^ (-s - 1) = ENs s Y g.1
  rw [ENs, Real.div_rpow (N_pos (by rw [hg]; exact hn)).le (by positivity), show -(1 + s) = -s - 1 by ring]

/-! ## Boundary integrals -/

lemma norm_topIs_le (hdet : 0 < g.det) (hD : (1 : ℤ) ≤ (g 0 0 + g 1 1) ^ 2 - 4 * g.det)
    {s : ℝ} (hs : 0 ≤ s) {Y : ℝ} (hY : 1 ≤ Y) :
    ‖topIs g s Y‖ ≤ 2 * (1 + 4 * (g.det : ℝ)) * ENs s Y g := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    (C := 2 * (1 + 4 * (g.det : ℝ)) * ENs s Y g) (f := fun x : ℝ => VsF g s (x + Y * I)) (fun x hx => by
      rw [uIoc_of_le (by norm_num)] at hx
      exact norm_VsF_le_K hdet hD hs hY (HypPar.inK_of (abs_le.2 ⟨hx.1.le, hx.2⟩) (by linarith) le_rfl))
  refine h.trans_eq ?_
  norm_num

lemma norm_arcIs_le (hdet : 0 < g.det) (hD : (1 : ℤ) ≤ (g 0 0 + g 1 1) ^ 2 - 4 * g.det)
    {s : ℝ} (hs : 0 ≤ s) {Y : ℝ} (hY : 1 ≤ Y) :
    ‖arcIs g s‖ ≤ 2 * (2 * (1 + 4 * (g.det : ℝ))) * ENs s Y g := by
  have hdp : (0 : ℝ) < g.det := by exact_mod_cast hdet
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    (C := 2 * (2 * (1 + 4 * (g.det : ℝ))) * ENs s Y g)
    (f := fun x : ℝ => (1 - I * (HypPar.arcH' x : ℂ)) * VsF g s (x + HypPar.arcH x * I)) (fun x hx => by
      rw [uIoc_of_le (by norm_num)] at hx
      have hx' : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨hx.1.le, hx.2⟩
      have hV := norm_VsF_le_K hdet hD hs hY
        (HypPar.inK_of (abs_le.2 ⟨hx'.1, hx'.2⟩) (HypPar.half_le_arcH_half.trans (HypPar.arcH_ge hx'))
          ((HypPar.arcH_le_one x).trans hY))
      calc ‖(1 - I * (HypPar.arcH' x : ℂ)) * VsF g s (x + HypPar.arcH x * I)‖
          = ‖1 - I * (HypPar.arcH' x : ℂ)‖ * ‖VsF g s (x + HypPar.arcH x * I)‖ := norm_mul _ _
        _ ≤ 2 * (2 * (1 + 4 * (g.det : ℝ)) * ENs s Y g) :=
            mul_le_mul (HypPar.norm_arc_factor_le hx') hV (norm_nonneg _) (by norm_num)
        _ = 2 * (2 * (1 + 4 * (g.det : ℝ))) * ENs s Y g := by ring)
  refine h.trans_eq ?_
  norm_num

lemma norm_sideIs_le (hdet : 0 < g.det) (hD : (1 : ℤ) ≤ (g 0 0 + g 1 1) ^ 2 - 4 * g.det)
    {s : ℝ} (hs : 0 ≤ s) {Y : ℝ} (hY : 1 ≤ Y) {c : ℂ} (hc : c.im = 0) (hcre : |c.re| ≤ 1 / 2) :
    ‖∫ y in HypPar.arcH (1 / 2)..Y, VsF g s (c + y * I)‖ ≤ 2 * (1 + 4 * (g.det : ℝ)) * Y * ENs s Y g := by
  have hdp : (0 : ℝ) < g.det := by exact_mod_cast hdet
  have hB : 0 ≤ 2 * (1 + 4 * (g.det : ℝ)) * ENs s Y g :=
    mul_nonneg (by linarith) (ENs_nonneg s Y g)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := HypPar.arcH (1 / 2)) (b := Y)
    (C := 2 * (1 + 4 * (g.det : ℝ)) * ENs s Y g) (f := fun y : ℝ => VsF g s (c + y * I))
    (fun y hy => norm_VsF_le_K hdet hD hs hY (HypPar.inK_side hc hcre hy hY))
  have hlen : |Y - HypPar.arcH (1 / 2)| ≤ Y := by
    have h1 := HypPar.arcH_half_pos
    have h2 : HypPar.arcH (1 / 2) ≤ Y := (HypPar.arcH_le_one _).trans hY
    rw [abs_of_nonneg (by linarith)]; linarith
  calc _ ≤ _ := h
    _ ≤ 2 * (1 + 4 * (g.det : ℝ)) * ENs s Y g * Y := mul_le_mul_of_nonneg_left hlen hB
    _ = 2 * (1 + 4 * (g.det : ℝ)) * Y * ENs s Y g := by ring

/-! ## Summability and cancellation -/

lemma summable_wtN_mul {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) (Y : ℝ)
    {T : S3.Conj.Mat → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ g : S3.Conj.Mat, g.det = n → HypPar.IsRest g → ¬IsSP g → ‖T g‖ ≤ C * ENs s Y g) :
    Summable fun g => wtN M n δ' g * T g := by
  refine Summable.of_norm_bounded_eventually
    ((summable_ENs hn hs Y).mul_left ((Fintype.card (Fin 2 → ZMod M) : ℝ) * C))
    (Filter.Eventually.of_forall fun g => ?_)
  by_cases h : g.det = n ∧ HypPar.IsRest g ∧ ¬IsSP g
  · rw [norm_mul, indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n} from h.1)]
    calc ‖wtN M n δ' g‖ * ‖T g‖ ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) * (C * ENs s Y g) :=
          mul_le_mul (norm_wtN_le n δ' g) (hT g h.1 h.2.1 h.2.2) (norm_nonneg _) (by positivity)
      _ = (Fintype.card (Fin 2 → ZMod M) : ℝ) * C * ENs s Y g := by ring
  · rw [wtN_of_not h, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hC)
      (indicator_nonneg (fun g _ => ENs_nonneg s Y g) g)

lemma CN_nonneg {n : ℤ} (hn : 0 < n) : (0 : ℝ) ≤ 2 * (1 + 4 * (n : ℝ)) := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  linarith

lemma summable_topN {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => wtN M n δ' g * topIs g s Y :=
  summable_wtN_mul hn δ' hs Y (T := fun g => topIs g s Y) (CN_nonneg hn) fun g hg hr hsp => by
    have h := norm_topIs_le (by rw [hg]; exact hn) (disc_ge_one hr hsp) hs.le hY
    rwa [hg] at h

lemma summable_arcN {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => wtN M n δ' g * arcIs g s :=
  summable_wtN_mul hn δ' hs Y (T := fun g => arcIs g s) (C := 2 * (2 * (1 + 4 * (n : ℝ))))
    (by linarith [CN_nonneg hn]) fun g hg hr hsp => by
    have h := norm_arcIs_le (by rw [hg]; exact hn) (disc_ge_one hr hsp) hs.le hY
    rwa [hg] at h

lemma summable_sideAN {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => wtN M n δ' g * sideAs g s Y :=
  summable_wtN_mul hn δ' hs Y (T := fun g => sideAs g s Y) (C := 2 * (1 + 4 * (n : ℝ)) * Y)
    (mul_nonneg (CN_nonneg hn) (by linarith)) fun g hg hr hsp => by
    have h := norm_sideIs_le (by rw [hg]; exact hn) (disc_ge_one hr hsp) hs.le hY (c := 1 / 2)
      (by simp) (by norm_num [abs_le])
    rw [hg] at h
    exact h

lemma summable_sideBN {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => wtN M n δ' g * sideBs g s Y :=
  summable_wtN_mul hn δ' hs Y (T := fun g => sideBs g s Y) (C := 2 * (1 + 4 * (n : ℝ)) * Y)
    (mul_nonneg (CN_nonneg hn) (by linarith)) fun g hg hr hsp => by
    have h := norm_sideIs_le (by rw [hg]; exact hn) (disc_ge_one hr hsp) hs.le hY (c := -(1 / 2))
      (by simp) (by norm_num [abs_le])
    rw [hg] at h
    exact h

lemma tsum_arc_zeroN {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (s : ℝ) :
    ∑' g : S3.Conj.Mat, wtN M n δ' g * arcIs g s = 0 := by
  have hpt : ∀ g : S3.Conj.Mat, wtN M n δ' (HypPar.conjEquiv ModularGroup.S g) *
      arcIs (HypPar.conjEquiv ModularGroup.S g) s = -(wtN M n δ' g * arcIs g s) := by
    intro g
    show wtN M n δ' (S3.Conj.conj ModularGroup.S g) * arcIs (S3.Conj.conj ModularGroup.S g) s = _
    rw [wtN_conj]
    by_cases h : g.det = n ∧ HypPar.IsRest g ∧ ¬IsSP g
    · rw [arcIs_S (by rw [h.1]; exact hn) (HypPar.goodQ_of_rest h.2.1) s]; ring
    · rw [wtN_of_not h]; ring
  have e : ∑' g : S3.Conj.Mat, wtN M n δ' g * arcIs g s =
      -∑' g : S3.Conj.Mat, wtN M n δ' g * arcIs g s :=
    ((HypPar.conjEquiv ModularGroup.S).tsum_eq (fun g => wtN M n δ' g * arcIs g s)).symm.trans
      ((tsum_congr hpt).trans tsum_neg)
  linear_combination e / 2

lemma tsum_side_eqN {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (s : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ∑' g : S3.Conj.Mat, wtN M n δ' g * sideAs g s Y =
      ∑' g : S3.Conj.Mat, wtN M n δ' g * sideBs g s Y := by
  have hpt : ∀ g : S3.Conj.Mat, wtN M n δ' (HypPar.conjEquiv ModularGroup.T g) *
      sideAs (HypPar.conjEquiv ModularGroup.T g) s Y = wtN M n δ' g * sideBs g s Y := by
    intro g
    show wtN M n δ' (S3.Conj.conj ModularGroup.T g) * sideAs (S3.Conj.conj ModularGroup.T g) s Y = _
    rw [wtN_conj]
    by_cases h : g.det = n ∧ HypPar.IsRest g ∧ ¬IsSP g
    · rw [sideAs_T (by rw [h.1]; exact hn) (HypPar.goodQ_of_rest h.2.1) s hY]
    · rw [wtN_of_not h, zero_mul, zero_mul]
  exact ((HypPar.conjEquiv ModularGroup.T).tsum_eq (fun g => wtN M n δ' g * sideAs g s Y)).symm.trans
    (tsum_congr hpt)

end RamanujanPetersson.EllW2


