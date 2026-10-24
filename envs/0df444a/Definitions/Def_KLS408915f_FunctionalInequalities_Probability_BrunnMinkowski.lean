-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
-- name    : KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:06:15.230163+00:00
-- url     : https://prove2.me/theorems/fb93d3d3-5b60-4eda-bf43-3e5511df6662
-- title:
--   Finite-dimensional Prékopa–Leindler and log-concave convolution
-- statement:
--   The property `IsPL` records the Prékopa–Leindler inequality for a measure μ on a measurable real vector space at a real exponent t: for measurable functions f, g, h taking values in $[0,\infty]$ (`ENNReal`), the pointwise inequality at $t x+(1-t)y$ implies the corresponding inequality between their `lintegral`s, with powers interpreted in $[0,\infty]$. The theorem `prekopaLeindler` establishes this inequality for real-valued, measurable, pointwise nonnegative functions on any finite-dimensional inner-product space equipped with Lebesgue measure, assuming $0<t<1$; the integrals are of the `ENNReal` quantities obtained using `ENNReal.ofReal`, and no finiteness assumption is imposed.
--
--   The auxiliary results `isPL_real`, `isPL_pi`, `isPL_euclidean`, and `isPL_volume` establish the `IsPL` property for one-dimensional, finite product, Euclidean, and finite-dimensional inner-product spaces, respectively, while `IsPL.comp`, `IsPL.symm`, and `IsPL.prod` provide transport, measurable-linear equivalence, and product closure. The helper `rpow_iSup` handles positive powers of suprema in $[0,\infty]$, and `iSup_min_natCast` supports truncation by finite natural values. Finally, `lintegral_mul_translate_logConcave` states that if measurable $p,q:V\to[0,\infty]$ are log-concave in the stated extended-real sense, then the Lebesgue convolution integrals $\int p(z)q(a-z)\,dz$ satisfy the same Prékopa–Leindler inequality under translation, again allowing infinite values and using no probability normalization.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/BrunnMinkowski.lean#L28-L236 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.BrunnMinkowski`, definition bundle `KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Pointwise
namespace FunctionalInequalities
universe u
namespace Analysis
section Isodiametric
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- A positive real power commutes with suprema in `ℝ≥0∞` (copy of the private helper of
`FunctionalInequalities.Probability.Line.BrunnMinkowski`, which is not exported). -/
 theorem rpow_iSup {ι : Sort*} (u : ι → ENNReal) {t : ℝ} (ht : 0 < t) :
    (⨆ i, u i) ^ t = ⨆ i, u i ^ t :=
  (ENNReal.orderIsoRpow t ht).map_iSup u
/-- The `ℝ≥0∞`-valued Prékopa–Leindler property at exponent `t`. -/
 def IsPL (X : Type*) [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    (μ : Measure X) (t : ℝ) : Prop :=
  ∀ f g h : X → ℝ≥0∞, Measurable f → Measurable g → Measurable h →
    (∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) →
    (∫⁻ x, f x ∂μ) ^ t * (∫⁻ y, g y ∂μ) ^ (1 - t) ≤ ∫⁻ z, h z ∂μ
 theorem iSup_min_natCast (a : ℝ≥0∞) : ⨆ n : ℕ, min a (n : ℝ≥0∞) = a := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  by_cases ha : a = ⊤
  · subst ha
    have hmt : ∀ n : ℕ, min (⊤ : ℝ≥0∞) (n : ℝ≥0∞) = (n : ℝ≥0∞) := fun n => min_eq_right le_top
    simp_rw [hmt]
    exact le_of_eq ENNReal.iSup_natCast.symm
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
    exact le_iSup_of_le n (le_min le_rfl hn.le)
 theorem isPL_real {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    FunctionalInequalities.Analysis.IsPL ℝ (volume : Measure ℝ) t := by
  have ht1' : (0:ℝ) < 1 - t := by linarith
  intro f g h hf hg hh hfgh
  have hmin : ∀ (u : ℝ → ℝ≥0∞) (N : ℕ) (x : ℝ), min (u x) (N : ℝ≥0∞) ≠ ⊤ := by
    intro u N x
    exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
  have hstep : ∀ N : ℕ,
      (∫⁻ x, min (f x) (N : ℝ≥0∞)) ^ t * (∫⁻ y, min (g y) (N : ℝ≥0∞)) ^ (1 - t) ≤
        ∫⁻ z, h z := by
    intro N
    have hkey : ∀ x y : ℝ,
        (min (f x) (N : ℝ≥0∞)) ^ t * (min (g y) (N : ℝ≥0∞)) ^ (1 - t)
          ≤ min (h (t * x + (1 - t) * y)) (N : ℝ≥0∞) := by
      intro x y
      refine le_min ?_ ?_
      · refine le_trans (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) ht0.le)
          (ENNReal.rpow_le_rpow (min_le_left _ _) ht1'.le)) ?_
        simpa using hfgh x y
      · refine le_trans (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_right _ _) ht0.le)
          (ENNReal.rpow_le_rpow (min_le_right _ _) ht1'.le)) ?_
        rw [← ENNReal.rpow_add_of_nonneg _ _ ht0.le ht1'.le]
        simp
    have hreal : ∀ x y : ℝ,
        ((min (f x) (N : ℝ≥0∞)).toReal) ^ t * ((min (g y) (N : ℝ≥0∞)).toReal) ^ (1 - t)
          ≤ (min (h (t * x + (1 - t) * y)) (N : ℝ≥0∞)).toReal := by
      intro x y
      rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
      refine ENNReal.toReal_mono (hmin h N _) (hkey x y)
    have hmeas : ∀ u : ℝ → ℝ≥0∞, Measurable u →
        Measurable fun x => (min (u x) (N : ℝ≥0∞)).toReal :=
      fun u hu => (hu.min measurable_const).ennreal_toReal
    have hPL := Probability.Line.prekopaLeindler
      (hmeas f hf) (hmeas g hg) (hmeas h hh)
      (fun x => ENNReal.toReal_nonneg) (fun y => ENNReal.toReal_nonneg) ht0 ht1 hreal
    have hof : ∀ (u : ℝ → ℝ≥0∞) (x : ℝ),
        ENNReal.ofReal ((min (u x) (N : ℝ≥0∞)).toReal) = min (u x) (N : ℝ≥0∞) :=
      fun u x => ENNReal.ofReal_toReal (hmin u N x)
    simp only [hof] at hPL
    exact hPL.trans (lintegral_mono fun z => min_le_left _ _)
  have hmono : ∀ u : ℝ → ℝ≥0∞, Monotone fun N : ℕ => ∫⁻ x, min (u x) (N : ℝ≥0∞) :=
    fun u a b hab => lintegral_mono fun x => min_le_min le_rfl (by exact_mod_cast hab)
  have hsup : ∀ u : ℝ → ℝ≥0∞, Measurable u →
      (⨆ N : ℕ, ∫⁻ x, min (u x) (N : ℝ≥0∞)) = ∫⁻ x, u x := by
    intro u hu
    rw [← lintegral_iSup (fun N => hu.min measurable_const)
      (fun a b hab x => min_le_min le_rfl (by exact_mod_cast hab))]
    exact lintegral_congr fun x => FunctionalInequalities.Analysis.iSup_min_natCast (u x)
  rw [← hsup f hf, ← hsup g hg, FunctionalInequalities.Analysis.rpow_iSup _ ht0, FunctionalInequalities.Analysis.rpow_iSup _ ht1', ENNReal.iSup_mul]
  refine iSup_le fun N => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun M => ?_
  exact le_trans (mul_le_mul' (ENNReal.rpow_le_rpow (hmono f (le_max_left N M)) ht0.le)
    (ENNReal.rpow_le_rpow (hmono g (le_max_right N M)) ht1'.le)) (hstep (max N M))
section MeasurableSpace
variable {X Y : Type*}
variable [AddCommGroup X] [Module ℝ X] [MeasurableSpace X] [AddCommGroup Y] [Module ℝ Y]
variable [MeasurableSpace Y]
 theorem IsPL.comp {μ : Measure X} {ν : Measure Y} {t : ℝ}
    (hX : FunctionalInequalities.Analysis.IsPL X μ t) {e : X → Y} (hmp : MeasurePreserving e μ ν)
    (hlin : ∀ (a b : ℝ) (x y : X), e (a • x + b • y) = a • e x + b • e y) : FunctionalInequalities.Analysis.IsPL Y ν t := by
  intro f g h hf hg hh hfgh
  have hyp : ∀ x y : X, (f ∘ e) x ^ t * ((g ∘ e) y) ^ (1 - t)
      ≤ (h ∘ e) (t • x + (1 - t) • y) := by
    intro x y
    simp only [Function.comp_apply, hlin]
    exact hfgh (e x) (e y)
  have h1 := hX (f ∘ e) (g ∘ e) (h ∘ e) (hf.comp hmp.measurable) (hg.comp hmp.measurable)
    (hh.comp hmp.measurable) hyp
  simp only [Function.comp_apply] at h1
  rwa [hmp.lintegral_comp hf, hmp.lintegral_comp hg, hmp.lintegral_comp hh] at h1
 theorem IsPL.symm {μ : Measure X} {ν : Measure Y} {t : ℝ}
    (hY : FunctionalInequalities.Analysis.IsPL Y ν t) (e : X ≃ᵐ Y) (hmp : MeasurePreserving e μ ν)
    (hlin : ∀ (a b : ℝ) (x y : X), e (a • x + b • y) = a • e x + b • e y) : FunctionalInequalities.Analysis.IsPL X μ t := by
  refine hY.comp (e := ⇑e.symm) (hmp.symm e) ?_
  intro a b x y
  refine e.injective ?_
  rw [hlin, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
 theorem IsPL.prod {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {t : ℝ}
    (hX : FunctionalInequalities.Analysis.IsPL X μ t) (hY : FunctionalInequalities.Analysis.IsPL Y ν t) : FunctionalInequalities.Analysis.IsPL (X × Y) (μ.prod ν) t := by
  intro f g h hf hg hh hfgh
  have hslice : ∀ (u : X × Y → ℝ≥0∞), Measurable u → ∀ x : X, Measurable fun y => u (x, y) :=
    fun u hu x => hu.comp (measurable_const.prodMk measurable_id)
  have hFGH : ∀ x₁ x₂ : X,
      (∫⁻ y, f (x₁, y) ∂ν) ^ t * (∫⁻ y, g (x₂, y) ∂ν) ^ (1 - t)
        ≤ ∫⁻ y, h (t • x₁ + (1 - t) • x₂, y) ∂ν := by
    intro x₁ x₂
    refine hY (fun y => f (x₁, y)) (fun y => g (x₂, y))
      (fun y => h (t • x₁ + (1 - t) • x₂, y)) (hslice f hf x₁) (hslice g hg x₂)
      (hslice h hh _) ?_
    intro y₁ y₂
    have hxy := hfgh (x₁, y₁) (x₂, y₂)
    simpa [Prod.smul_mk, Prod.mk_add_mk] using hxy
  have h1 := hX (fun x => ∫⁻ y, f (x, y) ∂ν) (fun x => ∫⁻ y, g (x, y) ∂ν)
    (fun x => ∫⁻ y, h (x, y) ∂ν) hf.lintegral_prod_right' hg.lintegral_prod_right'
    hh.lintegral_prod_right' hFGH
  rwa [← lintegral_prod _ hf.aemeasurable, ← lintegral_prod _ hg.aemeasurable,
    ← lintegral_prod _ hh.aemeasurable] at h1
end MeasurableSpace
 theorem isPL_pi {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ n : ℕ, FunctionalInequalities.Analysis.IsPL (Fin n → ℝ) (volume : Measure (Fin n → ℝ)) t
  | 0 => by
      intro f g h hf hg hh hfgh
      rw [Measure.volume_pi_eq_dirac 0, lintegral_dirac' _ hf, lintegral_dirac' _ hg,
        lintegral_dirac' _ hh]
      simpa using hfgh 0 0
  | (n + 1) => by
      have hprod : FunctionalInequalities.Analysis.IsPL (ℝ × (Fin n → ℝ)) (volume : Measure (ℝ × (Fin n → ℝ))) t := by
        rw [show (volume : Measure (ℝ × (Fin n → ℝ)))
          = (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)) from rfl]
        exact (FunctionalInequalities.Analysis.isPL_real ht0 ht1).prod (isPL_pi ht0 ht1 n)
      exact hprod.symm (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)
        (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0) (by intro a b x y; rfl)
 theorem isPL_euclidean {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (n : ℕ) :
    FunctionalInequalities.Analysis.IsPL (EuclideanSpace ℝ (Fin n)) (volume : Measure (EuclideanSpace ℝ (Fin n))) t :=
  (FunctionalInequalities.Analysis.isPL_pi ht0 ht1 n).comp (PiLp.volume_preserving_toLp (Fin n)) (by intro a b x y; rfl)
 theorem isPL_volume {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) : FunctionalInequalities.Analysis.IsPL E (volume : Measure E) t :=
  (FunctionalInequalities.Analysis.isPL_euclidean ht0 ht1 (Module.finrank ℝ E)).comp
    ((stdOrthonormalBasis ℝ E).measurePreserving_repr_symm)
    (by intro a b x y; simp)
/-- **Prékopa–Leindler inequality** on a finite-dimensional inner-product space, for Lebesgue
measure.  The one-dimensional case is `FunctionalInequalities.Probability.Line.prekopaLeindler`;
the general case follows by induction on the dimension and Fubini along a line. -/
theorem prekopaLeindler {f g h : V → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hfgh : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, ENNReal.ofReal (f x)) ^ t * (∫⁻ y, ENNReal.ofReal (g y)) ^ (1 - t) ≤
      ∫⁻ z, ENNReal.ofReal (h z) := by
  have ht1' : (0:ℝ) < 1 - t := by linarith
  refine FunctionalInequalities.Analysis.isPL_volume ht0 ht1 (fun x => ENNReal.ofReal (f x)) (fun y => ENNReal.ofReal (g y))
    (fun z => ENNReal.ofReal (h z)) hf.ennreal_ofReal hg.ennreal_ofReal hh.ennreal_ofReal ?_
  intro x y
  rw [ENNReal.ofReal_rpow_of_nonneg (hf0 x) ht0.le,
    ENNReal.ofReal_rpow_of_nonneg (hg0 y) ht1'.le, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) t)]
  exact ENNReal.ofReal_le_ofReal (hfgh x y)
/-- The convolution integral of two measurable log-concave nonnegative densities is
log-concave. The extended-real formulation also covers integrals equal to infinity;
finiteness and smoothness are separate regularization obligations. -/
theorem lintegral_mul_translate_logConcave
    {p q : V → ENNReal} (hp : Measurable p) (hq : Measurable q)
    (hpLC : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 →
      p x ^ t * p y ^ (1 - t) ≤ p (t • x + (1 - t) • y))
    (hqLC : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 →
      q x ^ t * q y ^ (1 - t) ≤ q (t • x + (1 - t) • y))
    (a b : V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (∫⁻ z, p z * q (a - z) ∂(volume : Measure V)) ^ t *
      (∫⁻ z, p z * q (b - z) ∂(volume : Measure V)) ^ (1 - t) ≤
        ∫⁻ z, p z * q ((t • a + (1 - t) • b) - z) ∂(volume : Measure V) := by
  have ht1' : 0 ≤ 1 - t := by linarith
  have hmeas (x : V) : Measurable (fun z : V => p z * q (x - z)) :=
    hp.mul (hq.comp (measurable_const.sub measurable_id))
  refine FunctionalInequalities.Analysis.isPL_volume ht0 ht1 _ _ _ (hmeas a) (hmeas b)
    (hmeas (t • a + (1 - t) • b)) ?_
  intro x y
  have harg : t • (a - x) + (1 - t) • (b - y) =
      (t • a + (1 - t) • b) - (t • x + (1 - t) • y) := by
    simp only [smul_sub]
    abel
  calc
    (p x * q (a - x)) ^ t * (p y * q (b - y)) ^ (1 - t)
        = (p x ^ t * p y ^ (1 - t)) *
            (q (a - x) ^ t * q (b - y) ^ (1 - t)) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ ht0.le,
              ENNReal.mul_rpow_of_nonneg _ _ ht1']
            ac_rfl
    _ ≤ p (t • x + (1 - t) • y) *
        q (t • (a - x) + (1 - t) • (b - y)) :=
          mul_le_mul' (hpLC x y t ht0 ht1) (hqLC (a - x) (b - y) t ht0 ht1)
    _ = _ := by rw [harg]
end Isodiametric
end Analysis
end FunctionalInequalities


