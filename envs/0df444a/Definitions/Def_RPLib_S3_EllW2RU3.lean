-- Prove2me | Definitions.Def_RPLib_S3_EllW2RU3
-- name    : RPLib_S3_EllW2RU3
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:32:14.555206+00:00
-- url     : https://prove2.me/theorems/7fd2e132-2886-4bce-8eba-cd1af7e55714
-- title:
--   The Eichler-Selberg trace formula in weight two: the unfolding identities for complex (Bochner) integrands
-- statement:
--   The unfolding identities for complex (Bochner) integrands.
--
--   For `F : ℍ → ℂ` measurable and `SL(2, ℤ)`-invariant:
--   * `integral_fd_mul_cp` (`IntegrableOn F (S_Y)`):
--     `∫_𝒟 F · #{(c, d) coprime : Y |cz+d|² ≤ im z} = 2 ∫_{S_Y} F`;
--   * `integrableOn_strip_of_lintegral` and **`integral_fd_mul_eCnt`** (`y0 > 0`, `∫⁻_𝒟 ‖F‖ E_{y0} < ∞`):
--     `∫_𝒟 F · E_{y0} = Σ_m 2 ∫_{S_{(m+1)² y0}} F`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec, Spectral Methods of Automorphic Forms, 2nd ed., Graduate Studies in Mathematics 53, AMS 2002, Chapter 2

import Mathlib
import Definitions.Def_RPLib_S3_EllW2LC1

/-!
# S3-ES-Wt2 (RU3): the unfolding identities for complex (Bochner) integrands

For `F : ℍ → ℂ` measurable and `SL(2, ℤ)`-invariant:
* `integral_fd_mul_cp` (`IntegrableOn F (S_Y)`):
  `∫_𝒟 F · #{(c, d) coprime : Y |cz+d|² ≤ im z} = 2 ∫_{S_Y} F`;
* `integrableOn_strip_of_lintegral` and **`integral_fd_mul_eCnt`** (`y0 > 0`, `∫⁻_𝒟 ‖F‖ E_{y0} < ∞`):
  `∫_𝒟 F · E_{y0} = Σ_m 2 ∫_{S_{(m+1)² y0}} F`.
-/

set_option autoImplicit false

open MeasureTheory UpperHalfPlane ModularGroup RP.FundDomain Function
open scoped MatrixGroups ENNReal Pointwise Modular

noncomputable section

attribute [local instance] measurableConstSMul_pgl smulInvariantMeasure_pgl
  smulInvariantMeasure_subgroup

namespace RamanujanPetersson.EllW2

/-- The real strip indicator pulled back by `g ∈ PSL₂(ℤ)`. -/
def indS (Y : ℝ) (g : PSL2Z) (z : ℍ) : ℝ := (stripH Y).indicator 1 ((g : PGL(2, ℝ)) • z)

lemma toReal_indicator_one (Y : ℝ) (w : ℍ) :
    ((stripH Y).indicator (1 : ℍ → ℝ≥0∞) w).toReal = (stripH Y).indicator (1 : ℍ → ℝ) w := by
  by_cases h : w ∈ stripH Y <;> simp [h]

lemma toReal_tsum_cpInd (Y : ℝ) (z : ℍ) :
    (∑' p : ℤ × ℤ, cpInd Y z p).toReal = 2 * ∑' g : PSL2Z, indS Y g z := by
  rw [← two_mul_tsum_PSL_strip, ENNReal.toReal_mul, ENNReal.tsum_toReal_eq]
  · simp only [indS, toReal_indicator_one]
    norm_num
  · intro g
    by_cases h : ((g : PGL(2, ℝ)) • z) ∈ stripH Y <;> simp [h]

lemma enorm_ofReal_toReal {a : ℝ≥0∞} (h : a ≠ ∞) : ‖((a.toReal : ℝ) : ℂ)‖ₑ = a := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal h]

/-- **Unfolding** (Bochner form). -/
theorem integral_fd_mul_cp {F : ℍ → ℂ} (hF : Measurable F)
    (hinv : ∀ (γ : SL(2, ℤ)) (z : ℍ), F (γ • z) = F z) (Y : ℝ)
    (hint : IntegrableOn F (stripH Y)) :
    ∫ z in 𝒟, F z * ((∑' p : ℤ × ℤ, cpInd Y z p).toReal : ℂ) = 2 * ∫ z in stripH Y, F z := by
  have := countable_PSL2Z
  have hS := measurableSet_stripH Y
  have hinvG : ∀ (g : PSL2Z) (z : ℍ), F ((g : PGL(2, ℝ)) • z) = F z := by
    intro g z
    obtain ⟨γ, hγ⟩ := mem_PSL2Z.1 g.2
    rw [← hγ, toPGLR_smul, hinv]
  have hterm : ∀ (g : PSL2Z) (z : ℍ),
      (stripH Y).indicator F (g • z) = F z * (indS Y g z : ℂ) := by
    intro g z
    unfold indS
    by_cases h : (g : PGL(2, ℝ)) • z ∈ stripH Y
    · rw [Set.indicator_of_mem (show g • z ∈ stripH Y from h), Set.indicator_of_mem h,
        Pi.one_apply, Complex.ofReal_one, mul_one]
      exact hinvG g z
    · rw [Set.indicator_of_notMem (show g • z ∉ stripH Y from h), Set.indicator_of_notMem h,
        Complex.ofReal_zero, mul_zero]
  have hmeasI : ∀ g : PSL2Z, Measurable (indS Y g) := fun g =>
    (measurable_one.indicator hS).comp (measurable_const_smul (g : PGL(2, ℝ)))
  have hmeasC : ∀ g : PSL2Z, Measurable fun z => F z * (indS Y g z : ℂ) := fun g =>
    hF.mul (Complex.measurable_ofReal.comp (hmeasI g))
  have hI : Integrable ((stripH Y).indicator F) := (integrable_indicator_iff hS).2 hint
  have hfin : ∑' g : PSL2Z, ∫⁻ z in 𝒟, ‖F z * (indS Y g z : ℂ)‖ₑ ≠ ∞ := by
    have e := isFundamentalDomain_fd.lintegral_eq_tsum'' (fun z => ‖(stripH Y).indicator F z‖ₑ)
    simp_rw [hterm] at e
    rw [← e]
    exact ne_of_lt hI.hasFiniteIntegral
  calc ∫ z in 𝒟, F z * ((∑' p : ℤ × ℤ, cpInd Y z p).toReal : ℂ)
      = ∫ z in 𝒟, 2 * ∑' g : PSL2Z, F z * (indS Y g z : ℂ) := by
        congr 1
        funext z
        rw [toReal_tsum_cpInd, Complex.ofReal_mul, Complex.ofReal_tsum, tsum_mul_left]
        push_cast
        ring
    _ = 2 * ∑' g : PSL2Z, ∫ z in 𝒟, F z * (indS Y g z : ℂ) := by
        rw [integral_const_mul,
          integral_tsum (fun g => (hmeasC g).aestronglyMeasurable) hfin]
    _ = 2 * ∫ z in stripH Y, F z := by
        rw [← integral_indicator hS, isFundamentalDomain_fd.integral_eq_tsum'' _ hI]
        congr 1
        exact tsum_congr fun g => integral_congr_ae (ae_of_all _ fun z => (hterm g z).symm)

lemma measurable_tsum_cpInd (Y : ℝ) : Measurable fun z : ℍ => ∑' p : ℤ × ℤ, cpInd Y z p :=
  Measurable.ennreal_tsum fun p => measurable_cpInd Y p

/-- The strips are integrable once `∫⁻_𝒟 ‖F‖ E_{y0}` is finite. -/
lemma integrableOn_strip_of_lintegral {F : ℍ → ℂ} (hF : Measurable F)
    (hinv : ∀ (γ : SL(2, ℤ)) (z : ℍ), F (γ • z) = F z) {y0 : ℝ}
    (hfin : ∫⁻ z in 𝒟, ‖F z‖ₑ * eCnt y0 z ≠ ∞) (m : ℕ) :
    IntegrableOn F (stripH (((m : ℝ) + 1) ^ 2 * y0)) := by
  have hinv' : ∀ (γ : SL(2, ℤ)) (z : ℍ), ‖F (γ • z)‖ₑ = ‖F z‖ₑ := fun γ z => by rw [hinv]
  have hsum := lintegral_fd_mul_eCnt hF.enorm hinv' y0
  rw [hsum] at hfin
  have hle : 2 * ∫⁻ z in stripH (((m : ℝ) + 1) ^ 2 * y0), ‖F z‖ₑ ≠ ∞ :=
    ne_top_of_le_ne_top hfin (ENNReal.le_tsum (f := fun m : ℕ =>
      2 * ∫⁻ z in stripH (((m : ℝ) + 1) ^ 2 * y0), ‖F z‖ₑ) m)
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  exact lt_top_iff_ne_top.2 fun h => hle (by rw [h, ENNReal.mul_top h2])

/-- **Unfolding of the lattice count** (Bochner form). -/
theorem integral_fd_mul_eCnt {F : ℍ → ℂ} (hF : Measurable F)
    (hinv : ∀ (γ : SL(2, ℤ)) (z : ℍ), F (γ • z) = F z) {y0 : ℝ} (hy0 : 0 < y0)
    (hfin : ∫⁻ z in 𝒟, ‖F z‖ₑ * eCnt y0 z ≠ ∞) :
    ∫ z in 𝒟, F z * ((eCnt y0 z).toReal : ℂ) =
      ∑' m : ℕ, 2 * ∫ z in stripH (((m : ℝ) + 1) ^ 2 * y0), F z := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℍ → ℝ≥0∞,
      N = fun (m : ℕ) (z : ℍ) => ∑' p : ℤ × ℤ, cpInd (((m : ℝ) + 1) ^ 2 * y0) z p := ⟨_, rfl⟩
  have hE : ∀ z, eCnt y0 z = ∑' m : ℕ, N m z := fun z => by rw [eCnt_eq_tsum, hN]
  have hmN : ∀ m, Measurable (N m) := fun m => by rw [hN]; exact measurable_tsum_cpInd _
  have hNle : ∀ m z, N m z ≤ eCnt y0 z := fun m z => by
    rw [hE]; exact ENNReal.le_tsum (f := fun m : ℕ => N m z) m
  have hNne : ∀ m z, N m z ≠ ∞ := fun m z => ne_top_of_le_ne_top (eCnt_ne_top hy0 z) (hNle m z)
  have hpt : ∀ z, ((eCnt y0 z).toReal : ℂ) = ∑' m : ℕ, ((N m z).toReal : ℂ) := by
    intro z
    rw [hE, ENNReal.tsum_toReal_eq (fun m => hNne m z), Complex.ofReal_tsum]
  have hmeasC : ∀ m : ℕ, Measurable fun z => F z * ((N m z).toReal : ℂ) := fun m =>
    hF.mul (Complex.measurable_ofReal.comp (hmN m).ennreal_toReal)
  have hfin' : ∑' m : ℕ, ∫⁻ z in 𝒟, ‖F z * ((N m z).toReal : ℂ)‖ₑ ≠ ∞ := by
    have e : ∀ m : ℕ, ∫⁻ z in 𝒟, ‖F z * ((N m z).toReal : ℂ)‖ₑ = ∫⁻ z in 𝒟, ‖F z‖ₑ * N m z :=
      fun m => lintegral_congr fun z => by rw [enorm_mul, enorm_ofReal_toReal (hNne m z)]
    simp_rw [e]
    have hmL : ∀ m : ℕ, AEMeasurable (fun z => ‖F z‖ₑ * N m z) (volume.restrict 𝒟) :=
      fun m => (hF.enorm.mul (hmN m)).aemeasurable
    rw [← lintegral_tsum hmL]
    simp_rw [ENNReal.tsum_mul_left, ← hE]
    exact hfin
  calc ∫ z in 𝒟, F z * ((eCnt y0 z).toReal : ℂ)
      = ∫ z in 𝒟, ∑' m : ℕ, F z * ((N m z).toReal : ℂ) := by
        congr 1
        funext z
        rw [hpt, tsum_mul_left]
    _ = ∑' m : ℕ, ∫ z in 𝒟, F z * ((N m z).toReal : ℂ) :=
        integral_tsum (fun m => (hmeasC m).aestronglyMeasurable) hfin'
    _ = ∑' m : ℕ, 2 * ∫ z in stripH (((m : ℝ) + 1) ^ 2 * y0), F z := by
        refine tsum_congr fun m => ?_
        rw [← integral_fd_mul_cp hF hinv _ (integrableOn_strip_of_lintegral hF hinv hfin m), hN]

end RamanujanPetersson.EllW2


