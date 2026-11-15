-- Prove2me | Definitions.Def_RPLib_S3_EllW2Z4
-- name    : RPLib_S3_EllW2Z4
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:47:21.773527+00:00
-- url     : https://prove2.me/theorems/eba38063-52cd-4822-b5a6-aca37fd88cd7
-- title:
--   The Eichler-Selberg trace formula in weight two: the full-domain limits for fixed `s > 0`
-- statement:
--   The full-domain limits for fixed `s > 0`.
--
--   * `exists_lim_of_cauchy_bound` (generic): a Cauchy bound `‖f Y₂ - f Y₁‖ ≤ C / Y₁` gives a limit with the same rate.
--   * `pullF F p = F(x + iy)/y²`; `stripR`, `regY_eq_union`; **`integral_trunc_sub`** (generic strip identity):
--     `∫_{𝒟_{Y₂}} F - ∫_{𝒟_{Y₁}} F = ∫_{Y₁}^{Y₂} (∫_{-1/2}^{1/2} F(x+iy) dx) / y² dy` (`1 ≤ Y₁ ≤ Y₂`).
--   * `integrableOn_tsum_wtN` (generic), `measurable_RD`, `integrableOn_SNH`, `SNH_ofC`, `zeroMode_SNH_ofC`.
--   * `CS M n s = KZ(s,1)·2π²·(2 + 1/s)`; `tsum_zA_le_CS`; `mul_CS` (`s·CS` is bounded for `s ≤ 1`).
--   * `IS M n δ' s Y = ∫_{𝒟_Y} SNH_s`, `LS = lim_Y IS`; **`tendsto_IS`** with the rate `‖LS - IS Y‖ ≤ CS/Y`.
--   * **`tendsto_INS`**: `∫_{𝒟_Y} NHS_s → -n^s (s/(1+s)) LS` as `Y → ∞` (the full-domain identity, (F2)(i)).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2Z3

/-!
# S3-ES-Wt2 (O6, file Z4): the full-domain limits for fixed `s > 0`

* `exists_lim_of_cauchy_bound` (generic): a Cauchy bound `‖f Y₂ - f Y₁‖ ≤ C / Y₁` gives a limit with the same rate.
* `pullF F p = F(x + iy)/y²`; `stripR`, `regY_eq_union`; **`integral_trunc_sub`** (generic strip identity):
  `∫_{𝒟_{Y₂}} F - ∫_{𝒟_{Y₁}} F = ∫_{Y₁}^{Y₂} (∫_{-1/2}^{1/2} F(x+iy) dx) / y² dy` (`1 ≤ Y₁ ≤ Y₂`).
* `integrableOn_tsum_wtN` (generic), `measurable_RD`, `integrableOn_SNH`, `SNH_ofC`, `zeroMode_SNH_ofC`.
* `CS M n s = KZ(s,1)·2π²·(2 + 1/s)`; `tsum_zA_le_CS`; `mul_CS` (`s·CS` is bounded for `s ≤ 1`).
* `IS M n δ' s Y = ∫_{𝒟_Y} SNH_s`, `LS = lim_Y IS`; **`tendsto_IS`** with the rate `‖LS - IS Y‖ ≤ CS/Y`.
* **`tendsto_INS`**: `∫_{𝒟_Y} NHS_s → -n^s (s/(1+s)) LS` as `Y → ∞` (the full-domain identity, (F2)(i)).
-/

open MeasureTheory Set Filter Complex
open UpperHalfPlane hiding I
open scoped ComplexConjugate MatrixGroups Modular Topology Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-! ## Generic: limits from a Cauchy bound -/

theorem exists_lim_of_cauchy_bound {f : ℝ → ℂ} {C Y0 : ℝ}
    (h : ∀ Y1 Y2 : ℝ, Y0 ≤ Y1 → Y1 ≤ Y2 → ‖f Y2 - f Y1‖ ≤ C / Y1) :
    ∃ L : ℂ, Tendsto f atTop (𝓝 L) ∧ ∀ Y : ℝ, Y0 ≤ Y → ‖L - f Y‖ ≤ C / Y := by
  have hc : Cauchy (map f atTop) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨Y, hY1, hY2⟩ := ((((tendsto_const_nhds (x := C)).div_atTop tendsto_id).eventually
      (gt_mem_nhds (half_pos hε))).and (eventually_ge_atTop Y0)).exists
    have hY1' : C / Y < ε / 2 := hY1
    refine ⟨f '' Ici Y, image_mem_map (Ici_mem_atTop Y), ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 := h Y a hY2 ha
    have h2 := h Y b hY2 hb
    rw [dist_eq_norm, ← sub_sub_sub_cancel_right (f a) (f b) (f Y)]
    calc ‖f a - f Y - (f b - f Y)‖ ≤ ‖f a - f Y‖ + ‖f b - f Y‖ := norm_sub_le _ _
      _ < ε := by linarith
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 hc
  refine ⟨L, hL, fun Y hY => ?_⟩
  have ht : Tendsto (fun Y2 => ‖f Y2 - f Y‖) atTop (𝓝 ‖L - f Y‖) :=
    (hL.sub tendsto_const_nhds).norm
  exact le_of_tendsto ht ((eventually_ge_atTop Y).mono fun Y2 hY2 => h Y Y2 hY hY2)

/-! ## Generic: the strip between two truncation heights -/

/-- The pull-back `F(x + iy) / y²` of a function on `ℍ` to `ℝ²`. -/
def pullF (F : ℍ → ℂ) (p : ℝ × ℝ) : ℂ := F (ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2)

/-- The rectangle `[-1/2, 1/2] × (Y₁, Y₂]`. -/
def stripR (Y1 Y2 : ℝ) : Set (ℝ × ℝ) := Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioc Y1 Y2

lemma measurableSet_stripR (Y1 Y2 : ℝ) : MeasurableSet (stripR Y1 Y2) :=
  measurableSet_Icc.prod measurableSet_Ioc

lemma regY_eq_union {Y1 Y2 : ℝ} (h1 : 1 ≤ Y1) (h12 : Y1 ≤ Y2) :
    HypPar.regY Y2 = HypPar.regY Y1 ∪ stripR Y1 Y2 := by
  ext p
  simp only [HypPar.regY, stripR, mem_ofPred_eq, mem_union, mem_prod, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨hx, ha, hy⟩
    by_cases hp : p.2 ≤ Y1
    · exact Or.inl ⟨hx, ha, hp⟩
    · exact Or.inr ⟨hx, not_le.1 hp, hy⟩
  · rintro (⟨hx, ha, hy⟩ | ⟨hx, hy1, hy2⟩)
    · exact ⟨hx, ha, hy.trans h12⟩
    · exact ⟨hx, (HypPar.arcH_le_one p.1).trans (h1.trans hy1.le), hy2⟩

lemma disjoint_regY_strip (Y1 Y2 : ℝ) : Disjoint (HypPar.regY Y1) (stripR Y1 Y2) := by
  rw [Set.disjoint_left]
  intro p hp hq
  simp only [HypPar.regY, stripR, mem_ofPred_eq, mem_prod, mem_Icc, mem_Ioc] at hp hq
  linarith [hp.2.2, hq.2.1]

/-- **Strip identity**: the difference of two truncated integrals is the `y`-integral of the zero mode. -/
theorem integral_trunc_sub (F : ℍ → ℂ) {Y1 Y2 : ℝ} (h1 : 1 ≤ Y1) (h12 : Y1 ≤ Y2)
    (hI : IntegrableOn (pullF F) (HypPar.regY Y2)) :
    (∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y2}, F z) - ∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y1}, F z =
      ∫ y in Y1..Y2, (∫ x in (-(1 / 2 : ℝ))..(1 / 2), F (ofComplex ((x : ℂ) + y * I))) / ((y : ℂ) ^ 2) := by
  have e : ∀ Y : ℝ, ∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, F z = ∫ p in HypPar.regY Y, pullF F p := fun Y =>
    HypPar.setIntegral_H_eq _ (HypPar.measurableSet_trunc Y) _ (HypPar.isClosed_regY Y).measurableSet
      (HypPar.coe_image_trunc Y) F
  have hU := regY_eq_union h1 h12
  have hIS : IntegrableOn (pullF F) (stripR Y1 Y2) := hI.mono_set (by rw [hU]; exact subset_union_right)
  have hI1 : IntegrableOn (pullF F) (HypPar.regY Y1) := hI.mono_set (by rw [hU]; exact subset_union_left)
  have hprod : (volume.restrict (stripR Y1 Y2) : Measure (ℝ × ℝ)) =
      (volume.restrict (Icc (-(1 / 2 : ℝ)) (1 / 2))).prod (volume.restrict (Ioc Y1 Y2)) := by
    rw [Measure.prod_restrict]; rfl
  have hIS' : Integrable (pullF F)
      ((volume.restrict (Icc (-(1 / 2 : ℝ)) (1 / 2))).prod (volume.restrict (Ioc Y1 Y2))) := by
    rw [← hprod]; exact hIS
  have hin : ∀ y : ℝ, ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), pullF F (x, y) =
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), F (ofComplex ((x : ℂ) + y * I))) / ((y : ℂ) ^ 2) := by
    intro y
    rw [intervalIntegral.integral_of_le (show (-(1 / 2 : ℝ)) ≤ 1 / 2 by norm_num),
      ← integral_Icc_eq_integral_Ioc, ← integral_div]
    rfl
  rw [e, e, hU, setIntegral_union (disjoint_regY_strip Y1 Y2) (measurableSet_stripR Y1 Y2) hI1 hIS,
    add_sub_cancel_left, hprod, integral_prod_symm _ hIS', intervalIntegral.integral_of_le h12]
  exact integral_congr_ae (Eventually.of_forall hin)

/-! ## Integrability of `wtN`-weighted series on `regY` -/

lemma integrableOn_tsum_wtN {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y C : ℝ}
    (hC : 0 ≤ C) {G : S3.Conj.Mat → ℝ × ℝ → ℂ} (hm : ∀ g, Measurable (G g))
    (hG : ∀ g : S3.Conj.Mat, g.det = n → HypPar.IsRest g → ¬IsSP g →
      ∀ p ∈ HypPar.regY Y, ‖G g p‖ ≤ C * ENs s Y g) :
    IntegrableOn (fun p => ∑' g : S3.Conj.Mat, wtN M n δ' g * G g p) (HypPar.regY Y) := by
  have : Countable S3.Conj.Mat := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  have hR := (HypPar.isClosed_regY Y).measurableSet
  have hbs : Summable fun g : S3.Conj.Mat => (Fintype.card (Fin 2 → ZMod M) : ℝ) * C *
      {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n}.indicator (ENs s Y) g :=
    (summable_ENs hn hs Y).mul_left _
  have hle : ∀ g : S3.Conj.Mat, ∀ p ∈ HypPar.regY Y, ‖wtN M n δ' g * G g p‖ ≤
      (Fintype.card (Fin 2 → ZMod M) : ℝ) * C *
        {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n}.indicator (ENs s Y) g := by
    intro g p hp
    by_cases h : g.det = n ∧ HypPar.IsRest g ∧ ¬IsSP g
    · rw [indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n} from h.1), norm_mul,
        mul_assoc]
      exact mul_le_mul (norm_wtN_le n δ' g) (hG g h.1 h.2.1 h.2.2 p hp) (norm_nonneg _)
        (Nat.cast_nonneg _)
    · rw [wtN_of_not h, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC)
        (indicator_nonneg (fun g _ => ENs_nonneg s Y g) g)
  have hmeas : Measurable fun p => ∑' g : S3.Conj.Mat,
      (HypPar.regY Y).indicator (fun p => wtN M n δ' g * G g p) p := by
    refine measurable_tsum_of_summable (fun g => ((hm g).const_mul _).indicator hR) (fun p => ?_)
    by_cases hp : p ∈ HypPar.regY Y
    · simp only [indicator_of_mem hp]
      exact hbs.of_norm_bounded fun g => hle g p hp
    · simp only [indicator_of_notMem hp]
      exact summable_zero
  have hH : IntegrableOn (fun p => ∑' g : S3.Conj.Mat,
      (HypPar.regY Y).indicator (fun p => wtN M n δ' g * G g p) p) (HypPar.regY Y) := by
    refine Integrable.mono' (integrableOn_const (C := ∑' g : S3.Conj.Mat,
      (Fintype.card (Fin 2 → ZMod M) : ℝ) * C *
        {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n}.indicator (ENs s Y) g)
      (HypPar.isCompact_regY Y).measure_lt_top.ne enorm_ne_top) hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_mem hR).mono fun p hp => ?_
    simp only [indicator_of_mem hp]
    exact tsum_of_norm_bounded hbs.hasSum fun g => hle g p hp
  refine hH.congr_fun (fun p hp => ?_) hR
  simp only [indicator_of_mem hp]

lemma measurable_RD (g : S3.Conj.Mat) (s : ℝ) : Measurable (RD g s) := by
  unfold RD Rc Pc trR
  fun_prop

lemma pullF_SNH_eq {n : ℤ} (δ' : ZMod M) (s : ℝ) {p : ℝ × ℝ} (hp : 0 < p.2) :
    pullF (SNH M n δ' s) p = ∑' g : S3.Conj.Mat, wtN M n δ' g * RD g s p := by
  obtain ⟨hre, him⟩ := re_im_ofC hp
  unfold pullF SNH
  rw [← tsum_div_const]
  refine tsum_congr fun g => ?_
  rw [hre, him]
  unfold RD
  ring

lemma integrableOn_SNH {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y : ℝ}
    (hY : 1 ≤ Y) : IntegrableOn (pullF (SNH M n δ' s)) (HypPar.regY Y) := by
  have h := integrableOn_tsum_wtN (M := M) hn δ' hs (by norm_num : (0 : ℝ) ≤ 4)
    (G := fun g => RD g s) (fun g => measurable_RD g s)
    (fun g hg _ _ p hp => norm_RD_le (by rw [hg]; exact hn) hs.le hY hp)
  exact h.congr_fun (fun p hp => (pullF_SNH_eq δ' s (HypPar.im_pos_of_mem_regY hp)).symm)
    (HypPar.isClosed_regY Y).measurableSet

lemma SNH_ofC {n : ℤ} (δ' : ZMod M) (s : ℝ) {x y : ℝ} (hy : 0 < y) :
    SNH M n δ' s (ofComplex ((x : ℂ) + y * I)) =
      ∑' g : S3.Conj.Mat, wtN M n δ' g * ((Rc g x y ^ (-s - 1) : ℝ) : ℂ) := by
  obtain ⟨hre, him⟩ := re_im_ofC (p := (x, y)) hy
  dsimp only at hre him
  unfold SNH
  rw [hre, him]

lemma zeroMode_SNH_ofC {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ}
    (hy : 1 / 2 ≤ y) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), SNH M n δ' s (ofComplex ((x : ℂ) + y * I)) =
      ((∑' g, zA M n δ' s y g : ℝ) : ℂ) := by
  have hy0 : 0 < y := by linarith
  rw [← zeroMode_SNH hn δ' hs hy]
  exact intervalIntegral.integral_congr fun x _ => SNH_ofC δ' s hy0

/-! ## The uniform zero-mode constant -/

/-- `CS(s) = KZ(s, 1) · 2π² · (2 + 1/s)`: bounds `Σ' zA` for `y ≥ 1`. -/
def CS (M : ℕ) [NeZero M] (n : ℤ) (s : ℝ) : ℝ := KZ M n s 1 * (2 * π ^ 2) * (2 + 1 / s)

lemma CS_nonneg (n : ℤ) {s : ℝ} (hs : 0 < s) : 0 ≤ CS M n s := by
  unfold CS
  have := KZ_nonneg (M := M) n hs.le one_pos
  positivity

lemma mul_CS (n : ℤ) {s : ℝ} (hs : 0 < s) :
    s * CS M n s = KZ M n s 1 * (2 * π ^ 2) * (2 * s + 1) := by
  unfold CS
  rw [show s * (KZ M n s 1 * (2 * π ^ 2) * (2 + 1 / s)) =
      KZ M n s 1 * (2 * π ^ 2) * (2 * s + s * (1 / s)) by ring, mul_one_div_cancel hs.ne']

lemma tsum_zA_le_CS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 1 ≤ y) :
    ∑' g, zA M n δ' s y g ≤ CS M n s := by
  have hy2 : 1 / 2 ≤ y := by linarith
  have hZ0 : 0 ≤ ∑' c : ℤ, |(c : ℝ)| ^ (-(1 + 2 * s)) := tsum_nonneg fun c => by positivity
  have hZ := tsum_abs_int_rpow_le hs
  have h2 := tsum_zA_le hn δ' hs hy2
  have hK : KZ M n s y ≤ KZ M n s 1 := by
    unfold KZ
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
    exact div_le_div_of_nonneg_left (mul_nonneg (by linarith) (by positivity)) one_pos hy
  have hP : (y ^ 2) ^ (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ hy) (by linarith)
  have hK1 := KZ_nonneg (M := M) n hs.le one_pos
  calc _ ≤ _ := h2
    _ ≤ KZ M n s 1 * (2 * π ^ 2) * ∑' c : ℤ, |(c : ℝ)| ^ (-(1 + 2 * s)) := by
        refine mul_le_mul_of_nonneg_right ?_ hZ0
        refine mul_le_mul hK ?_ (by positivity) hK1
        exact mul_le_of_le_one_right (by positivity) hP
    _ ≤ CS M n s := by
        unfold CS
        exact mul_le_mul_of_nonneg_left hZ (mul_nonneg hK1 (by positivity))

/-! ## The `SNH` truncations and their limit -/

/-- `IS(s, Y) = ∫_{𝒟_Y} SNH_s`. -/
def IS (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (s Y : ℝ) : ℂ :=
  ∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, SNH M n δ' s z

/-- `LS(s) = lim_{Y → ∞} IS(s, Y)` (`= ∫_𝒟 SNH_s`). -/
def LS (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (s : ℝ) : ℂ := limUnder atTop (IS M n δ' s)

lemma IS_sub_eq {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y1 Y2 : ℝ} (h1 : 1 ≤ Y1)
    (h12 : Y1 ≤ Y2) :
    IS M n δ' s Y2 - IS M n δ' s Y1 =
      ∫ y in Y1..Y2, ((∑' g, zA M n δ' s y g : ℝ) : ℂ) / ((y : ℂ) ^ 2) := by
  unfold IS
  rw [integral_trunc_sub _ h1 h12 (integrableOn_SNH hn δ' hs (h1.trans h12))]
  refine intervalIntegral.integral_congr fun y hy => ?_
  have hy1 : Y1 ≤ y := by rw [uIcc_of_le h12] at hy; exact hy.1
  rw [zeroMode_SNH_ofC hn δ' hs (by linarith)]

lemma norm_IS_sub_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y1 Y2 : ℝ}
    (h1 : 1 ≤ Y1) (h12 : Y1 ≤ Y2) :
    ‖IS M n δ' s Y2 - IS M n δ' s Y1‖ ≤ CS M n s / Y1 := by
  rw [IS_sub_eq hn δ' hs h1 h12]
  have hC := CS_nonneg (M := M) n hs
  have hb : ∀ y : ℝ, y ∈ Ioc Y1 Y2 →
      ‖((∑' g, zA M n δ' s y g : ℝ) : ℂ) / ((y : ℂ) ^ 2)‖ ≤ CS M n s * (y ^ 2)⁻¹ := by
    intro y hy
    have hy1 : 1 ≤ y := h1.trans hy.1.le
    rw [norm_div, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg (zA_nonneg n δ' s y)), Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ y),
      div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (tsum_zA_le_CS hn δ' hs hy1) (by positivity)
  have hderiv : ∀ x ∈ uIcc Y1 Y2, HasDerivAt (fun y : ℝ => -CS M n s * y⁻¹) (CS M n s * (x ^ 2)⁻¹) x := by
    intro x hx
    rw [uIcc_of_le h12] at hx
    have hx0 : x ≠ 0 := by have := hx.1; linarith
    have := (hasDerivAt_inv hx0).const_mul (-CS M n s)
    rwa [neg_mul_neg] at this
  have hint : IntervalIntegrable (fun y : ℝ => CS M n s * (y ^ 2)⁻¹) volume Y1 Y2 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (ContinuousOn.inv₀ (continuous_pow 2).continuousOn fun x hx => ?_)
    rw [uIcc_of_le h12] at hx
    have : (0 : ℝ) < x := by have := hx.1; linarith
    exact pow_ne_zero 2 this.ne'
  calc _ ≤ ∫ y in Y1..Y2, CS M n s * (y ^ 2)⁻¹ :=
        intervalIntegral.norm_integral_le_of_norm_le h12 (Eventually.of_forall hb) hint
    _ = -CS M n s * Y2⁻¹ - -CS M n s * Y1⁻¹ := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ ≤ CS M n s / Y1 := by
        have : 0 ≤ CS M n s * Y2⁻¹ := mul_nonneg hC (inv_nonneg.2 (by linarith))
        rw [div_eq_mul_inv]
        linarith

theorem tendsto_IS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) :
    Tendsto (IS M n δ' s) atTop (𝓝 (LS M n δ' s)) ∧
      ∀ Y : ℝ, 1 ≤ Y → ‖LS M n δ' s - IS M n δ' s Y‖ ≤ CS M n s / Y := by
  obtain ⟨L, hL, hb⟩ := exists_lim_of_cauchy_bound (f := IS M n δ' s) (C := CS M n s) (Y0 := 1)
    (fun Y1 Y2 h1 h12 => norm_IS_sub_le hn δ' hs h1 h12)
  have e : LS M n δ' s = L := tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L, hL⟩) hL
  rw [e]
  exact ⟨hL, hb⟩

/-- **Full-domain identity** (fixed `s > 0`): `∫_{𝒟_Y} NHS_s → -n^s (s/(1+s)) ∫_𝒟 SNH_s`. -/
theorem tendsto_INS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun Y : ℝ => ∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, NHS M n δ' s z) atTop
      (𝓝 (-(((n : ℝ) ^ s : ℝ) : ℂ) * ((s / (1 + s) : ℝ) : ℂ) * LS M n δ' s)) := by
  have h1 := ((tendsto_TsY hn δ' hs).const_mul (-(((n : ℝ) ^ s : ℝ) : ℂ))).sub
    ((tendsto_IS hn δ' hs).1.const_mul ((((n : ℝ) ^ s : ℝ) : ℂ) * ((s / (1 + s) : ℝ) : ℂ)))
  have e : -(((n : ℝ) ^ s : ℝ) : ℂ) * ((s / (1 + s) : ℝ) : ℂ) * LS M n δ' s =
      -(((n : ℝ) ^ s : ℝ) : ℂ) * 0 - (((n : ℝ) ^ s : ℝ) : ℂ) * ((s / (1 + s) : ℝ) : ℂ) * LS M n δ' s := by
    ring
  rw [e]
  refine h1.congr' ((eventually_ge_atTop 1).mono fun Y hY => ?_)
  exact (integral_truncN hn δ' hs hY).symm

end RamanujanPetersson.EllW2


