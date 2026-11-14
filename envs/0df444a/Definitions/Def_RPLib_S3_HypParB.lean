-- Prove2me | Definitions.Def_RPLib_S3_HypParB
-- name    : RPLib_S3_HypParB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:51:27.342658+00:00
-- url     : https://prove2.me/theorems/8d8df7e4-76ef-49aa-a980-a0516787ffad
-- title:
--   Stokes' theorem on the truncated fundamental domain of $SL_2(\mathbb{Z})$
-- statement:
--   On $\{(x,y) : |x| \le 1/2,\ \sqrt{1 - x^2} \le y \le Y\}$, the integrals of partial derivatives $\partial_y V$ and $\partial_x V$ of a $C^1$ function equal the corresponding boundary integrals over the top edge, the two vertical sides and the arc.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib

/-!
# S3-HypParTerms, part B: Stokes on the truncated fundamental domain `𝒟_Y` (coordinates)

`regY Y = {(x, y) : |x| ≤ 1/2, √(1 - x²) ≤ y ≤ Y}`. For `V` with real partials `Vx`, `Vy` on `y > 0`:
* `integral_regY_Vy`: `∫∫ Vy = ∫_{-1/2}^{1/2} [V(x + iY) - V(x + i h(x))] dx` (FTC in `y`, Fubini);
* (next) `integral_regY_Vx`: `∫∫ Vx = ∫_{h(1/2)}^{Y} [V(1/2+iy) - V(-1/2+iy) - V(s(y)+iy) + V(-s(y)+iy)] dy`,
  `s(y) = √(1 - y²)`; then the arc substitution `y = h(x)` (`intervalIntegral.integral_deriv_smul_comp'`).
-/

open MeasureTheory Set Complex intervalIntegral
open scoped Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypPar

/-- The lower boundary arc `h(x) = √(1 - x²)`. -/
def arcH (x : ℝ) : ℝ := √(1 - x ^ 2)

/-- `h'(x) = -x / √(1 - x²)`. -/
def arcH' (x : ℝ) : ℝ := -x / √(1 - x ^ 2)

/-- `s(y) = √(1 - y²)` (`= 0` for `y ≥ 1`). -/
def sfun (y : ℝ) : ℝ := √(1 - y ^ 2)

/-- The truncated fundamental domain `𝒟_Y` in coordinates. -/
def regY (Y : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ arcH p.1 ≤ p.2 ∧ p.2 ≤ Y}

lemma continuous_arcH : Continuous arcH := by unfold arcH; fun_prop

lemma arcH_half_pos : 0 < arcH (1 / 2) := by
  unfold arcH; apply Real.sqrt_pos.2; norm_num

lemma arcH_ge {x : ℝ} (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) : arcH (1 / 2) ≤ arcH x := by
  unfold arcH; apply Real.sqrt_le_sqrt; nlinarith [hx.1, hx.2]

lemma arcH_pos {x : ℝ} (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) : 0 < arcH x :=
  lt_of_lt_of_le arcH_half_pos (arcH_ge hx)

lemma arcH_le_one (x : ℝ) : arcH x ≤ 1 := by
  unfold arcH
  calc √(1 - x ^ 2) ≤ √1 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
    _ = 1 := Real.sqrt_one

lemma hasDerivAt_arcH {x : ℝ} (hx : x ^ 2 < 1) : HasDerivAt arcH (arcH' x) x := by
  have h1 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  have h2 := h1.sqrt (sub_pos.2 hx).ne'
  unfold arcH arcH'
  convert h2 using 1
  have : √(1 - x ^ 2) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 hx)).ne'
  field_simp

lemma continuousOn_arcH' : ContinuousOn arcH' (Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
  unfold arcH'
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
  exact (Real.sqrt_pos.2 (by nlinarith [hx.1, hx.2])).ne'

lemma isClosed_regY (Y : ℝ) : IsClosed (regY Y) := by
  have e : regY Y = {p : ℝ × ℝ | -(1 / 2 : ℝ) ≤ p.1} ∩ {p | p.1 ≤ 1 / 2} ∩ {p | arcH p.1 ≤ p.2} ∩
      {p | p.2 ≤ Y} := by
    ext p; simp [regY, and_assoc]
  rw [e]
  exact (((isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_fst continuous_const)).inter
    (isClosed_le (continuous_arcH.comp continuous_fst) continuous_snd)).inter
    (isClosed_le continuous_snd continuous_const)

lemma isCompact_regY (Y : ℝ) : IsCompact (regY Y) :=
  (isCompact_Icc.prod (isCompact_Icc (a := (0 : ℝ)) (b := Y))).of_isClosed_subset (isClosed_regY Y)
    fun _p hp => ⟨hp.1, le_trans (Real.sqrt_nonneg _) hp.2.1, hp.2.2⟩

lemma im_pos_of_mem_regY {Y : ℝ} {p : ℝ × ℝ} (hp : p ∈ regY Y) : 0 < p.2 :=
  lt_of_lt_of_le (arcH_pos hp.1) hp.2.1

variable {V Vx Vy : ℂ → ℂ}

lemma continuousOn_regY {W : ℂ → ℂ} (cW : ContinuousOn W {z | 0 < z.im}) (Y : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => W (p.1 + p.2 * I)) (regY Y) :=
  cW.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I).continuousOn
    fun p hp => by
      show 0 < (((p : ℝ × ℝ).1 : ℂ) + p.2 * I).im
      simpa using im_pos_of_mem_regY hp

lemma ftc_x (hx : ∀ x y : ℝ, 0 < y → HasDerivAt (fun s : ℝ => V (s + y * I)) (Vx (x + y * I)) x)
    (cx : ContinuousOn Vx {z | 0 < z.im}) {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    ∫ x in a..b, Vx (x + y * I) = V (b + y * I) - V (a + y * I) := by
  have hc : Continuous fun x : ℝ => Vx (x + y * I) :=
    cx.comp_continuous (by fun_prop) (fun x => by show 0 < ((x : ℂ) + y * I).im; simpa using hy)
  exact integral_eq_sub_of_hasDerivAt (fun x _ => hx x y hy) (hc.intervalIntegrable a b)

lemma ftc_y (hy' : ∀ x y : ℝ, 0 < y → HasDerivAt (fun s : ℝ => V (x + s * I)) (Vy (x + y * I)) y)
    (cy : ContinuousOn Vy {z | 0 < z.im}) (x : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ y in a..b, Vy (x + y * I) = V (x + b * I) - V (x + a * I) := by
  have hc : ContinuousOn (fun y : ℝ => Vy (x + y * I)) (uIcc a b) :=
    cy.comp (by fun_prop : Continuous fun y : ℝ => (x : ℂ) + y * I).continuousOn fun y hy => by
      rw [uIcc_of_le hab] at hy
      show 0 < ((x : ℂ) + y * I).im
      simpa using lt_of_lt_of_le ha hy.1
  exact integral_eq_sub_of_hasDerivAt
    (fun y hy => hy' x y (by rw [uIcc_of_le hab] at hy; exact lt_of_lt_of_le ha hy.1))
    hc.intervalIntegrable

/-- **Stokes, the `∂_y` half.** -/
theorem integral_regY_Vy
    (hy' : ∀ x y : ℝ, 0 < y → HasDerivAt (fun s : ℝ => V (x + s * I)) (Vy (x + y * I)) y)
    (cy : ContinuousOn Vy {z | 0 < z.im}) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ p in regY Y, Vy (p.1 + p.2 * I) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), (V (x + Y * I) - V (x + arcH x * I)) := by
  have hmeas : MeasurableSet (regY Y) := (isClosed_regY Y).measurableSet
  have hint : IntegrableOn (fun p : ℝ × ℝ => Vy (p.1 + p.2 * I)) (regY Y) :=
    (continuousOn_regY cy Y).integrableOn_compact (isCompact_regY Y)
  have hI : Integrable ((regY Y).indicator fun p : ℝ × ℝ => Vy (p.1 + p.2 * I))
      ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hint.integrable_indicator hmeas
  rw [← MeasureTheory.integral_indicator hmeas, Measure.volume_eq_prod, MeasureTheory.integral_prod _ hI,
    intervalIntegral.integral_of_le (by norm_num), ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← MeasureTheory.integral_indicator measurableSet_Icc]
  congr 1
  funext x
  by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
  · rw [indicator_of_mem hx]
    have e : (fun y => (regY Y).indicator (fun p : ℝ × ℝ => Vy (p.1 + p.2 * I)) (x, y)) =
        (Icc (arcH x) Y).indicator (fun y : ℝ => Vy (x + y * I)) := by
      funext y
      by_cases hy : y ∈ Icc (arcH x) Y
      · rw [indicator_of_mem hy, indicator_of_mem (show (x, y) ∈ regY Y from ⟨hx, hy.1, hy.2⟩)]
      · rw [indicator_of_notMem hy, indicator_of_notMem (fun h => hy ⟨h.2.1, h.2.2⟩)]
    have hle : arcH x ≤ Y := le_trans (arcH_le_one x) hY
    rw [e, MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, ftc_y hy' cy x (arcH_pos hx) hle]
  · rw [indicator_of_notMem hx]
    have e : (fun y => (regY Y).indicator (fun p : ℝ × ℝ => Vy (p.1 + p.2 * I)) (x, y)) =
        fun _ => 0 := by
      funext y; exact indicator_of_notMem (fun h => hx h.1) _
    rw [e, MeasureTheory.integral_zero]


/-! ## The `∂_x` half and the arc substitution -/

lemma continuous_sfun : Continuous sfun := by unfold sfun; fun_prop

lemma sfun_nonneg (y : ℝ) : 0 ≤ sfun y := Real.sqrt_nonneg _

lemma sfun_eq_zero {y : ℝ} (hy : 1 ≤ y) : sfun y = 0 := by
  unfold sfun; exact Real.sqrt_eq_zero'.2 (by nlinarith)

lemma arcH_half_sq : arcH (1 / 2) ^ 2 = 3 / 4 := by
  unfold arcH; rw [Real.sq_sqrt (by norm_num)]; norm_num

lemma sfun_le_half {y : ℝ} (hy : arcH (1 / 2) ≤ y) : sfun y ≤ 1 / 2 := by
  have h1 : 3 / 4 ≤ y ^ 2 := by
    rw [← arcH_half_sq]; exact pow_le_pow_left₀ arcH_half_pos.le hy 2
  unfold sfun
  rw [Real.sqrt_le_left (by norm_num)]; nlinarith

lemma arcH_le_iff {x y : ℝ} (hy : 0 ≤ y) : arcH x ≤ y ↔ sfun y ≤ |x| := by
  unfold arcH sfun
  rw [Real.sqrt_le_left hy, Real.sqrt_le_left (abs_nonneg x), sq_abs]
  constructor <;> intro h <;> linarith

lemma mem_regY_iff {Y x y : ℝ} (hy : 0 ≤ y) :
    (x, y) ∈ regY Y ↔ x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) \ Ioo (-sfun y) (sfun y) ∧ y ≤ Y := by
  have hIoo : x ∈ Ioo (-sfun y) (sfun y) ↔ |x| < sfun y := by rw [abs_lt]; rfl
  simp only [regY, mem_ofPred_eq, mem_sdiff, hIoo, not_lt, arcH_le_iff hy]
  tauto

lemma arcH_zero : arcH 0 = 1 := by unfold arcH; simp

lemma arcH_neg (x : ℝ) : arcH (-x) = arcH x := by unfold arcH; ring_nf

lemma sfun_arcH {x : ℝ} (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) : sfun (arcH x) = |x| := by
  unfold sfun arcH
  rw [Real.sq_sqrt (by nlinarith [hx.1, hx.2]), show 1 - (1 - x ^ 2) = x ^ 2 by ring,
    Real.sqrt_sq_eq_abs]

lemma sq_lt_one_of_mem {x : ℝ} (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) : x ^ 2 < 1 := by
  nlinarith [hx.1, hx.2]

/-- Generic continuity of `t ↦ W (a t + b t * I)` where `b > 0`. -/
lemma contOn_comp {W : ℂ → ℂ} (cW : ContinuousOn W {z | 0 < z.im}) {a b : ℝ → ℝ}
    (ha : Continuous a) (hb : Continuous b) {s : Set ℝ} (hpos : ∀ t ∈ s, 0 < b t) :
    ContinuousOn (fun t => W (a t + b t * I)) s :=
  cW.comp (by fun_prop : Continuous fun t => (a t : ℂ) + b t * I).continuousOn fun t ht => by
    show 0 < ((a t : ℂ) + b t * I).im
    simpa using hpos t ht

lemma half_mem : (1 / 2 : ℝ) ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by norm_num, le_rfl⟩
lemma neg_half_mem : (-(1 / 2) : ℝ) ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨le_rfl, by norm_num⟩
lemma zero_mem_half : (0 : ℝ) ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by norm_num, by norm_num⟩

/-- **Stokes, the `∂_x` half** (Fubini in the other order). -/
theorem integral_regY_Vx
    (hx : ∀ x y : ℝ, 0 < y → HasDerivAt (fun s : ℝ => V (s + y * I)) (Vx (x + y * I)) x)
    (cx : ContinuousOn Vx {z | 0 < z.im}) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ p in regY Y, Vx (p.1 + p.2 * I) =
      ∫ y in arcH (1 / 2)..Y, (V (1 / 2 + y * I) - V (-(1 / 2) + y * I) -
        (V (sfun y + y * I) - V (-sfun y + y * I))) := by
  have hmeas : MeasurableSet (regY Y) := (isClosed_regY Y).measurableSet
  have hint : IntegrableOn (fun p : ℝ × ℝ => Vx (p.1 + p.2 * I)) (regY Y) :=
    (continuousOn_regY cx Y).integrableOn_compact (isCompact_regY Y)
  have hI : Integrable ((regY Y).indicator fun p : ℝ × ℝ => Vx (p.1 + p.2 * I))
      ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hint.integrable_indicator hmeas
  have hle : arcH (1 / 2) ≤ Y := le_trans (arcH_le_one _) hY
  rw [← MeasureTheory.integral_indicator hmeas, Measure.volume_eq_prod,
    MeasureTheory.integral_prod_symm _ hI, intervalIntegral.integral_of_le hle,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_indicator measurableSet_Icc]
  congr 1
  funext y
  by_cases hy : y ∈ Icc (arcH (1 / 2)) Y
  · rw [indicator_of_mem hy]
    have hy0 : 0 < y := lt_of_lt_of_le arcH_half_pos hy.1
    have hs := sfun_le_half hy.1
    have e : (fun x => (regY Y).indicator (fun p : ℝ × ℝ => Vx (p.1 + p.2 * I)) (x, y)) =
        (Icc (-(1 / 2 : ℝ)) (1 / 2) \ Ioo (-sfun y) (sfun y)).indicator
          (fun x : ℝ => Vx (x + y * I)) := by
      funext x
      by_cases hxm : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) \ Ioo (-sfun y) (sfun y)
      · rw [indicator_of_mem hxm, indicator_of_mem ((mem_regY_iff hy0.le).2 ⟨hxm, hy.2⟩)]
      · rw [indicator_of_notMem hxm,
          indicator_of_notMem (fun h => hxm ((mem_regY_iff hy0.le).1 h).1)]
    have hc : Continuous fun x : ℝ => Vx (x + y * I) :=
      cx.comp_continuous (by fun_prop) (fun x => by show 0 < ((x : ℂ) + y * I).im; simpa using hy0)
    have hsub : Ioo (-sfun y) (sfun y) ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2) :=
      Ioo_subset_Icc_self.trans (Icc_subset_Icc (by linarith) hs)
    rw [e, MeasureTheory.integral_indicator (measurableSet_Icc.diff measurableSet_Ioo),
      setIntegral_sdiff measurableSet_Ioo (hc.integrableOn_Icc) hsub,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [sfun_nonneg y]),
      ftc_x hx cx hy0, ftc_x hx cx hy0]
    push_cast; ring
  · rw [indicator_of_notMem hy]
    have e : (fun x => (regY Y).indicator (fun p : ℝ × ℝ => Vx (p.1 + p.2 * I)) (x, y)) =
        fun _ => 0 := by
      funext x
      exact indicator_of_notMem (fun h => hy ⟨le_trans (arcH_ge h.1) h.2.1, h.2.2⟩) _
    rw [e, MeasureTheory.integral_zero]

/-- **Arc substitution** `y = h(x)`: the inner side pieces become the arc integral. -/
theorem arc_subst (cV : ContinuousOn V {z | 0 < z.im}) :
    ∫ y in arcH (1 / 2)..1, (V (sfun y + y * I) - V (-sfun y + y * I)) =
      -∫ x in (-(1 / 2 : ℝ))..(1 / 2), (arcH' x : ℂ) * V (x + arcH x * I) := by
  set g1 : ℝ → ℂ := fun y => V (sfun y + y * I)
  set g2 : ℝ → ℂ := fun y => V (-sfun y + y * I)
  have cg : ∀ g : ℝ → ℂ, (g = g1 ∨ g = g2) → ContinuousOn g (Ioi 0) := by
    rintro g (rfl | rfl)
    · exact contOn_comp cV continuous_sfun continuous_id fun t ht => ht
    · have := contOn_comp cV continuous_sfun.neg continuous_id (s := Ioi 0) fun t ht => ht
      simpa [g2] using this
  have himg : ∀ a b : ℝ, a ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) → b ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) →
      arcH '' uIcc a b ⊆ Ioi 0 := by
    rintro a b ha hb _ ⟨x, hx, rfl⟩
    exact arcH_pos (uIcc_subset_Icc ha hb hx)
  have hder : ∀ a b : ℝ, a ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) → b ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) →
      ∀ x ∈ uIcc a b, HasDerivAt arcH (arcH' x) x := fun a b ha hb x hx =>
    hasDerivAt_arcH (sq_lt_one_of_mem (uIcc_subset_Icc ha hb hx))
  have hcd : ∀ a b : ℝ, a ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) → b ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) →
      ContinuousOn arcH' (uIcc a b) := fun a b ha hb =>
    continuousOn_arcH'.mono (uIcc_subset_Icc ha hb)
  -- the two substitutions
  have s1 := intervalIntegral.integral_deriv_smul_comp' (hder _ _ half_mem zero_mem_half)
    (hcd _ _ half_mem zero_mem_half) ((cg g1 (Or.inl rfl)).mono (himg _ _ half_mem zero_mem_half))
  have s2 := intervalIntegral.integral_deriv_smul_comp' (hder _ _ neg_half_mem zero_mem_half)
    (hcd _ _ neg_half_mem zero_mem_half) ((cg g2 (Or.inr rfl)).mono (himg _ _ neg_half_mem zero_mem_half))
  rw [arcH_zero] at s1 s2
  rw [arcH_neg] at s2
  -- rewrite the composed integrands on the intervals
  have e1 : ∫ x in (1 / 2 : ℝ)..0, arcH' x • (g1 ∘ arcH) x =
      ∫ x in (1 / 2 : ℝ)..0, (arcH' x : ℂ) * V (x + arcH x * I) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_ge (by norm_num)] at hx
    have hxm : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [hx.1], hx.2⟩
    simp only [Function.comp, g1, sfun_arcH hxm, abs_of_nonneg hx.1, Complex.real_smul]
  have e2 : ∫ x in (-(1 / 2) : ℝ)..0, arcH' x • (g2 ∘ arcH) x =
      ∫ x in (-(1 / 2) : ℝ)..0, (arcH' x : ℂ) * V (x + arcH x * I) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by norm_num)] at hx
    have hxm : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨hx.1, by linarith [hx.2]⟩
    simp only [Function.comp, g2, sfun_arcH hxm, abs_of_nonpos hx.2, Complex.real_smul,
      Complex.ofReal_neg, neg_neg]
  rw [e1] at s1
  rw [e2] at s2
  have hii : ∀ a b : ℝ, a ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) → b ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) →
      IntervalIntegrable (fun x : ℝ => (arcH' x : ℂ) * V (x + arcH x * I)) volume a b := by
    intro a b ha hb
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul ?_ ?_
    · exact (Complex.continuous_ofReal.comp_continuousOn (hcd a b ha hb))
    · exact contOn_comp cV continuous_id continuous_arcH fun t ht => arcH_pos (uIcc_subset_Icc ha hb ht)
  have hgi : ∀ g : ℝ → ℂ, (g = g1 ∨ g = g2) → IntervalIntegrable g volume (arcH (1 / 2)) 1 := by
    intro g hg
    refine ((cg g hg).mono fun t ht => ?_).intervalIntegrable
    rw [uIcc_of_le (arcH_le_one _)] at ht
    exact lt_of_lt_of_le arcH_half_pos ht.1
  rw [intervalIntegral.integral_sub (hgi g1 (Or.inl rfl)) (hgi g2 (Or.inr rfl)), ← s1, ← s2,
    intervalIntegral.integral_symm (0 : ℝ) (1 / 2),
    ← intervalIntegral.integral_add_adjacent_intervals (hii _ _ neg_half_mem zero_mem_half)
      (hii _ _ zero_mem_half half_mem)]
  ring

/-- **Stokes on `𝒟_Y`** for a `C¹` function `V` on the upper half plane:
`∫∫ (V_y + i V_x) = ∫_top V - ∫_arc V (1 - i h') dx + i ∫_sides [V(1/2+iy) - V(-1/2+iy)] dy`. -/
theorem stokes_regY
    (hx : ∀ x y : ℝ, 0 < y → HasDerivAt (fun s : ℝ => V (s + y * I)) (Vx (x + y * I)) x)
    (hy' : ∀ x y : ℝ, 0 < y → HasDerivAt (fun s : ℝ => V (x + s * I)) (Vy (x + y * I)) y)
    (cV : ContinuousOn V {z | 0 < z.im}) (cx : ContinuousOn Vx {z | 0 < z.im})
    (cy : ContinuousOn Vy {z | 0 < z.im}) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ p in regY Y, (Vy (p.1 + p.2 * I) + I * Vx (p.1 + p.2 * I)) =
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), V (x + Y * I)) -
        (∫ x in (-(1 / 2 : ℝ))..(1 / 2), (1 - I * arcH' x) * V (x + arcH x * I)) +
        I * ∫ y in arcH (1 / 2)..Y, (V (1 / 2 + y * I) - V (-(1 / 2) + y * I)) := by
  have hintx : IntegrableOn (fun p : ℝ × ℝ => Vx (p.1 + p.2 * I)) (regY Y) :=
    (continuousOn_regY cx Y).integrableOn_compact (isCompact_regY Y)
  have hinty : IntegrableOn (fun p : ℝ × ℝ => Vy (p.1 + p.2 * I)) (regY Y) :=
    (continuousOn_regY cy Y).integrableOn_compact (isCompact_regY Y)
  have hY0 : 0 < Y := lt_of_lt_of_le one_pos hY
  have hle : arcH (1 / 2) ≤ Y := le_trans (arcH_le_one _) hY
  rw [MeasureTheory.integral_add hinty (hintx.const_mul I), MeasureTheory.integral_const_mul,
    integral_regY_Vy hy' cy hY, integral_regY_Vx hx cx hY]
  -- integrability facts
  have posY : ∀ t ∈ uIcc (arcH (1 / 2)) Y, 0 < t := fun t ht => by
    rw [uIcc_of_le hle] at ht; exact lt_of_lt_of_le arcH_half_pos ht.1
  have iS1 : IntervalIntegrable (fun y : ℝ => V (1 / 2 + y * I)) volume (arcH (1 / 2)) Y := by
    have := contOn_comp cV (a := fun _ => 1 / 2) continuous_const continuous_id posY
    exact (by simpa using this : ContinuousOn (fun y : ℝ => V (1 / 2 + y * I)) _).intervalIntegrable
  have iS2 : IntervalIntegrable (fun y : ℝ => V (-(1 / 2) + y * I)) volume (arcH (1 / 2)) Y := by
    have := contOn_comp cV (a := fun _ => -(1 / 2)) continuous_const continuous_id posY
    exact (by simpa using this : ContinuousOn (fun y : ℝ => V (-(1 / 2) + y * I)) _).intervalIntegrable
  have iG : ∀ a b : ℝ, arcH (1 / 2) ≤ a → a ≤ b → IntervalIntegrable
      (fun y : ℝ => V (sfun y + y * I) - V (-sfun y + y * I)) volume a b := by
    intro a b ha hab
    have pos : ∀ t ∈ uIcc a b, 0 < t := fun t ht => by
      rw [uIcc_of_le hab] at ht; exact lt_of_lt_of_le arcH_half_pos (ha.trans ht.1)
    refine ContinuousOn.intervalIntegrable (ContinuousOn.sub ?_ ?_)
    · exact contOn_comp cV continuous_sfun continuous_id pos
    · have := contOn_comp cV continuous_sfun.neg continuous_id pos
      simpa using this
  have iTop : IntervalIntegrable (fun x : ℝ => V (x + Y * I)) volume (-(1 / 2)) (1 / 2) :=
    (contOn_comp cV continuous_id (b := fun _ => Y) continuous_const fun _ _ => hY0).intervalIntegrable
  have iArc : IntervalIntegrable (fun x : ℝ => V (x + arcH x * I)) volume (-(1 / 2)) (1 / 2) :=
    (contOn_comp cV continuous_id continuous_arcH fun t ht =>
      arcH_pos (uIcc_subset_Icc neg_half_mem half_mem ht)).intervalIntegrable
  have iArc' : IntervalIntegrable (fun x : ℝ => (arcH' x : ℂ) * V (x + arcH x * I)) volume
      (-(1 / 2)) (1 / 2) := by
    refine ContinuousOn.intervalIntegrable (ContinuousOn.mul ?_ ?_)
    · exact Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_arcH'.mono (uIcc_subset_Icc neg_half_mem half_mem))
    · exact contOn_comp cV continuous_id continuous_arcH fun t ht =>
        arcH_pos (uIcc_subset_Icc neg_half_mem half_mem ht)
  -- the part of the inner sides above `y = 1` vanishes
  have hzero : ∫ y in (1 : ℝ)..Y, (V (sfun y + y * I) - V (-sfun y + y * I)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun y hy => ?_]
    · simp
    · rw [uIcc_of_le hY] at hy
      simp [sfun_eq_zero hy.1]
  rw [intervalIntegral.integral_sub (iS1.sub iS2) (iG _ _ le_rfl hle),
    ← intervalIntegral.integral_add_adjacent_intervals (iG _ _ le_rfl (arcH_le_one _))
      (iG _ _ (arcH_le_one _) hY),
    hzero, arc_subst cV, intervalIntegral.integral_sub iTop iArc,
    intervalIntegral.integral_sub iS1 iS2]
  have e : ∫ x in (-(1 / 2 : ℝ))..(1 / 2), (1 - I * arcH' x) * V (x + arcH x * I) =
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), V (x + arcH x * I)) -
        I * ∫ x in (-(1 / 2 : ℝ))..(1 / 2), (arcH' x : ℂ) * V (x + arcH x * I) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub iArc
      (iArc'.const_mul I)]
    congr 1; funext x; ring
  rw [e]; ring

end RamanujanPetersson.HypPar


