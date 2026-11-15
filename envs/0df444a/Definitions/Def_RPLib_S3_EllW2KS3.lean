-- Prove2me | Definitions.Def_RPLib_S3_EllW2KS3
-- name    : RPLib_S3_EllW2KS3
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:50:24.444503+00:00
-- url     : https://prove2.me/theorems/3277cbcc-4101-4d66-b08c-20b93d57334e
-- title:
--   The Eichler-Selberg trace formula in weight two: bounds and continuity of `KS`
-- statement:
--   Bounds and continuity of `KS`.
--
--   * `Qe_rpow_le_inv` (`s, ε ≥ 0`): `Qe^(-s-1) ≤ Qe⁻¹`; `Qe_rpow_le_fC` (`0 ≤ ε ≤ 1`): `≤ 9 fC (μ + τ)`.
--   * `inv_Qe_le` (`ε ≥ 0`, `m = √(μ²+ε)`): `Qe⁻¹ ≤ fC μ (fC (τ − m) + fC (τ + m))`.
--   * `integral_Qe_rpow_le`: `∫_τ Qe^(-s-1) ≤ 2π fC μ`; `KS_nonneg`, `KS_le` (`KS s ε ≤ 2π²`, all `s, ε ≥ 0`).
--   * `tendsto_KS`: `KS s ε → π²/2` as `(s, ε) → (0, 0)` within `[0,∞) × [0,1]` (dominated convergence twice).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2KS2

/-!
# S3-ES-Wt2 (KS3): bounds and continuity of `KS`

* `Qe_rpow_le_inv` (`s, ε ≥ 0`): `Qe^(-s-1) ≤ Qe⁻¹`; `Qe_rpow_le_fC` (`0 ≤ ε ≤ 1`): `≤ 9 fC (μ + τ)`.
* `inv_Qe_le` (`ε ≥ 0`, `m = √(μ²+ε)`): `Qe⁻¹ ≤ fC μ (fC (τ − m) + fC (τ + m))`.
* `integral_Qe_rpow_le`: `∫_τ Qe^(-s-1) ≤ 2π fC μ`; `KS_nonneg`, `KS_le` (`KS s ε ≤ 2π²`, all `s, ε ≥ 0`).
* `tendsto_KS`: `KS s ε → π²/2` as `(s, ε) → (0, 0)` within `[0,∞) × [0,1]` (dominated convergence twice).
-/

set_option autoImplicit false

open MeasureTheory Real Filter Topology

noncomputable section

namespace RamanujanPetersson.EllW2

lemma Qe_rpow_nonneg (s : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (μ τ : ℝ) : 0 ≤ Qe ε μ τ ^ (-s - 1) :=
  Real.rpow_nonneg (Qe_pos hε μ τ).le _

lemma Qe_rpow_le_inv {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 ≤ ε) (μ τ : ℝ) :
    Qe ε μ τ ^ (-s - 1) ≤ (Qe ε μ τ)⁻¹ := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_Qe hε μ τ) (by linarith)

lemma Qe_rpow_le_fC {s ε : ℝ} (hs : 0 ≤ s) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (μ τ : ℝ) :
    Qe ε μ τ ^ (-s - 1) ≤ 9 * fC (μ + τ) := by
  refine (Qe_rpow_le_inv hs hε0 μ τ).trans ?_
  have h9 := Qe0_le_nine_mul hε0 hε1 μ τ
  have hB : 1 + (μ + τ) ^ 2 ≤ Qe 0 μ τ := by
    rw [Qe_zero]; nlinarith [sq_nonneg (μ - τ), sq_nonneg (μ + τ)]
  calc (Qe ε μ τ)⁻¹ ≤ ((1 + (μ + τ) ^ 2) / 9)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    _ = 9 * fC (μ + τ) := by rw [inv_div, div_eq_mul_inv]; rfl

lemma inv_Qe_le {ε : ℝ} (hε : 0 ≤ ε) (μ τ : ℝ) :
    (Qe ε μ τ)⁻¹ ≤ fC μ * (fC (τ - √(μ ^ 2 + ε)) + fC (τ + √(μ ^ 2 + ε))) := by
  set m := √(μ ^ 2 + ε) with hmdef
  have hm : m ^ 2 = μ ^ 2 + ε := Real.sq_sqrt (by positivity)
  rw [Qe_factor hm.symm]
  have hA : 0 < 1 + (m - τ) ^ 2 := by positivity
  have hB : 0 < 1 + (m + τ) ^ 2 := by positivity
  have hC : 0 < 1 + μ ^ 2 := by positivity
  have e1 : fC (τ - m) = (1 + (m - τ) ^ 2)⁻¹ := by unfold fC; ring_nf
  have e2 : fC (τ + m) = (1 + (m + τ) ^ 2)⁻¹ := by unfold fC; ring_nf
  rw [e1, e2]
  unfold fC
  have key : (1 + μ ^ 2)⁻¹ * ((1 + (m - τ) ^ 2)⁻¹ + (1 + (m + τ) ^ 2)⁻¹)
      - ((1 + (m - τ) ^ 2) * (1 + (m + τ) ^ 2))⁻¹
      = ((1 + (m - τ) ^ 2) + (1 + (m + τ) ^ 2) - (1 + μ ^ 2)) /
          ((1 + μ ^ 2) * (1 + (m - τ) ^ 2) * (1 + (m + τ) ^ 2)) := by
    field_simp
    ring
  have hnum : 0 ≤ (1 + (m - τ) ^ 2) + (1 + (m + τ) ^ 2) - (1 + μ ^ 2) := by
    nlinarith [sq_nonneg τ, sq_nonneg μ]
  have : 0 ≤ ((1 + (m - τ) ^ 2) + (1 + (m + τ) ^ 2) - (1 + μ ^ 2)) /
      ((1 + μ ^ 2) * (1 + (m - τ) ^ 2) * (1 + (m + τ) ^ 2)) := div_nonneg hnum (by positivity)
  linarith

lemma integral_Qe_rpow_le {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 ≤ ε) (μ : ℝ) :
    ∫ τ, Qe ε μ τ ^ (-s - 1) ≤ 2 * π * fC μ := by
  set m := √(μ ^ 2 + ε) with hmdef
  have i1 : Integrable fun τ : ℝ => fC (τ - m) := integrable_fC.comp_sub_right m
  have i2 : Integrable fun τ : ℝ => fC (τ + m) := integrable_fC.comp_add_right m
  have hg : Integrable fun τ : ℝ => fC μ * (fC (τ - m) + fC (τ + m)) := (i1.add i2).const_mul _
  calc ∫ τ, Qe ε μ τ ^ (-s - 1) ≤ ∫ τ, fC μ * (fC (τ - m) + fC (τ + m)) :=
        integral_mono_of_nonneg (ae_of_all _ fun τ => Qe_rpow_nonneg s hε μ τ) hg
          (ae_of_all _ fun τ => (Qe_rpow_le_inv hs hε μ τ).trans (inv_Qe_le hε μ τ))
    _ = 2 * π * fC μ := by
        rw [integral_const_mul, integral_add i1 i2, integral_sub_right_eq_self fC m,
          integral_add_right_eq_self fC m, integral_fC]
        ring

lemma KS_nonneg (s : ℝ) {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ KS s ε :=
  integral_nonneg fun μ => integral_nonneg fun τ => Qe_rpow_nonneg s hε μ τ

lemma KS_le {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 ≤ ε) : KS s ε ≤ 2 * π ^ 2 := by
  unfold KS
  calc ∫ μ, ∫ τ, Qe ε μ τ ^ (-s - 1) ≤ ∫ μ, 2 * π * fC μ :=
        integral_mono_of_nonneg
          (ae_of_all _ fun μ => integral_nonneg fun τ => Qe_rpow_nonneg s hε μ τ)
          (integrable_fC.const_mul _) (ae_of_all _ fun μ => integral_Qe_rpow_le hs hε μ)
    _ = 2 * π ^ 2 := by rw [integral_const_mul, integral_fC]; ring

/-! ## Continuity at `(0, 0)` -/

/-- The parameter filter `(s, ε) → (0, 0)`, `s ≥ 0`, `0 ≤ ε ≤ 1`. -/
abbrev lKS : Filter (ℝ × ℝ) := 𝓝[Set.Ici 0 ×ˢ Set.Icc 0 1] (0, 0)

lemma eventually_lKS : ∀ᶠ p in lKS, 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 :=
  eventually_nhdsWithin_of_forall fun p hp => ⟨hp.1, hp.2.1, hp.2.2⟩

lemma continuous_Qe (ε : ℝ) : Continuous fun q : ℝ × ℝ => Qe ε q.1 q.2 := by
  unfold Qe; fun_prop

lemma continuous_Qe_rpow (s : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    Continuous fun q : ℝ × ℝ => Qe ε q.1 q.2 ^ (-s - 1) :=
  (continuous_Qe ε).rpow_const fun q => Or.inl (Qe_pos hε q.1 q.2).ne'

lemma tendsto_Qe_rpow (μ τ : ℝ) :
    Tendsto (fun p : ℝ × ℝ => Qe p.2 μ τ ^ (-p.1 - 1)) (𝓝 (0, 0))
      (𝓝 (Qe 0 μ τ ^ (-(0 : ℝ) - 1))) := by
  have h1 : Continuous fun p : ℝ × ℝ => Qe p.2 μ τ := by unfold Qe; fun_prop
  have h2 : Continuous fun p : ℝ × ℝ => -p.1 - 1 := by fun_prop
  exact (h1.tendsto (0, 0)).rpow (h2.tendsto (0, 0)) (Or.inl (Qe_pos le_rfl μ τ).ne')

lemma tendsto_KS_inner (μ : ℝ) :
    Tendsto (fun p : ℝ × ℝ => ∫ τ, Qe p.2 μ τ ^ (-p.1 - 1)) lKS
      (𝓝 (∫ τ, Qe 0 μ τ ^ (-(0 : ℝ) - 1))) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun τ => 9 * fC (μ + τ)) ?_ ?_ ?_ ?_
  · filter_upwards [eventually_lKS] with p hp
    exact ((continuous_Qe_rpow p.1 hp.2.1).comp (Continuous.prodMk_right μ)).aestronglyMeasurable
  · filter_upwards [eventually_lKS] with p hp
    refine ae_of_all _ fun τ => ?_
    rw [Real.norm_of_nonneg (Qe_rpow_nonneg _ hp.2.1 μ τ)]
    exact Qe_rpow_le_fC hp.1 hp.2.1 hp.2.2 μ τ
  · exact (integrable_fC.comp_add_left μ).const_mul 9
  · exact ae_of_all _ fun τ => (tendsto_Qe_rpow μ τ).mono_left nhdsWithin_le_nhds

lemma aesm_KS_inner (s : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    AEStronglyMeasurable (fun μ : ℝ => ∫ τ, Qe ε μ τ ^ (-s - 1)) volume :=
  ((continuous_Qe_rpow s hε).stronglyMeasurable.integral_prod_right'
    (ν := volume)).aestronglyMeasurable

theorem tendsto_KS : Tendsto (fun p : ℝ × ℝ => KS p.1 p.2) lKS (𝓝 (π ^ 2 / 2)) := by
  rw [← KS_zero]
  unfold KS
  refine tendsto_integral_filter_of_dominated_convergence (fun μ => 2 * π * fC μ) ?_ ?_ ?_ ?_
  · filter_upwards [eventually_lKS] with p hp
    exact aesm_KS_inner p.1 hp.2.1
  · filter_upwards [eventually_lKS] with p hp
    refine ae_of_all _ fun μ => ?_
    rw [Real.norm_of_nonneg (integral_nonneg fun τ => Qe_rpow_nonneg _ hp.2.1 μ τ)]
    exact integral_Qe_rpow_le hp.1 hp.2.1 μ
  · exact integrable_fC.const_mul _
  · exact ae_of_all _ tendsto_KS_inner

end RamanujanPetersson.EllW2


