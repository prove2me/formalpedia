-- Prove2me | Definitions.Def_RPLib_S3_EllW2AS2
-- name    : RPLib_S3_EllW2AS2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:58:53.320051+00:00
-- url     : https://prove2.me/theorems/4750cbab-77b6-4c34-ba0f-2f6fd1ee8d80
-- title:
--   The Eichler-Selberg trace formula in weight two: the strip limits and the unfolded lattice count as `s → 0+`
-- statement:
--   The strip limits and the unfolded lattice count as `s → 0+`.
--
--   * `ofReal_mul_strip`, `integrand_eq`, `lintegral_Ici_inv_sq_mul`, `integrand_le`, `strip_le`.
--   * **`strip_bound`**: eventually `ofReal s · ∫⁻_{S_Y} SNE ≤ ofReal (Kb c1 c2 Y / Y)` for all `Y > 0`.
--   * **`tendsto_strip`**: `ofReal s · ∫⁻_{S_Y} SNE → ofReal (rhoE n / Y)` (dominated convergence).
--   * `hasSum_inv_sq_succ`, `tsum_two_ofReal`.
--   * **`tendsto_eCnt`**: `ofReal s · ∫⁻_𝒟 SNE · E_{y0} → ofReal (2 rhoE n / y0 · π²/6)`
--     (unfolding `lintegral_fd_mul_eCnt`, then dominated convergence for the counting measure on `ℕ`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec, Spectral Methods of Automorphic Forms, 2nd ed., Graduate Studies in Mathematics 53, AMS 2002, Chapter 2

import Mathlib
import Definitions.Def_RPLib_S3_EllW2AS1

/-!
# S3-ES-Wt2 (O6, file AS2): the strip limits and the unfolded lattice count as `s → 0+`

* `ofReal_mul_strip`, `integrand_eq`, `lintegral_Ici_inv_sq_mul`, `integrand_le`, `strip_le`.
* **`strip_bound`**: eventually `ofReal s · ∫⁻_{S_Y} SNE ≤ ofReal (Kb c1 c2 Y / Y)` for all `Y > 0`.
* **`tendsto_strip`**: `ofReal s · ∫⁻_{S_Y} SNE → ofReal (rhoE n / Y)` (dominated convergence).
* `hasSum_inv_sq_succ`, `tsum_two_ofReal`.
* **`tendsto_eCnt`**: `ofReal s · ∫⁻_𝒟 SNE · E_{y0} → ofReal (2 rhoE n / y0 · π²/6)`
  (unfolding `lintegral_fd_mul_eCnt`, then dominated convergence for the counting measure on `ℕ`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups ENNReal Modular Real

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

lemma measurable_inv_sq_ofReal : Measurable fun y : ℝ => ENNReal.ofReal ((y ^ 2)⁻¹) :=
  ENNReal.measurable_ofReal.comp (by fun_prop)

lemma ofReal_mul_strip (n : ℤ) (δ' : ZMod M) (s : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ENNReal.ofReal s * ∫⁻ z in stripH Y, SNE M n δ' s z =
      ∫⁻ y in Ici Y, ENNReal.ofReal s * (ENNReal.ofReal ((y ^ 2)⁻¹) * ZE M n δ' s y) := by
  rw [lintegral_stripH_ZE n δ' s hY, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma integrand_eq {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 0 < y) :
    ENNReal.ofReal s * (ENNReal.ofReal ((y ^ 2)⁻¹) * ZE M n δ' s y) =
      ENNReal.ofReal ((y ^ 2)⁻¹ * (s * ZS M n δ' s y)) := by
  rw [ZE_eq hn δ' hs hy, ← ENNReal.ofReal_mul (inv_nonneg.2 (sq_nonneg y)),
    ← ENNReal.ofReal_mul hs.le]
  congr 1
  ring

lemma lintegral_Ici_inv_sq_mul {Y : ℝ} (hY : 0 < Y) (K : ℝ) :
    ∫⁻ y in Ici Y, ENNReal.ofReal ((y ^ 2)⁻¹ * K) = ENNReal.ofReal (K / Y) := by
  have e : ∀ y : ℝ, ENNReal.ofReal ((y ^ 2)⁻¹ * K) = ENNReal.ofReal ((y ^ 2)⁻¹) * ENNReal.ofReal K :=
    fun y => ENNReal.ofReal_mul (inv_nonneg.2 (sq_nonneg y))
  simp_rw [e]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_Ici_inv_sq hY,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hY.le)]
  congr 1
  ring

lemma integrand_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    {s : ℝ} (hs : 0 < s ∧ s ≤ 1 ∧ ∀ y : ℝ, 0 < y → s * ZS M n δ' s y ≤ c1 * max 1 (y ^ 2)⁻¹ + c2 * KY y)
    {Y y : ℝ} (hY : 0 < Y) (hy : Y ≤ y) :
    ENNReal.ofReal s * (ENNReal.ofReal ((y ^ 2)⁻¹) * ZE M n δ' s y) ≤
      ENNReal.ofReal ((y ^ 2)⁻¹ * Kb c1 c2 Y) := by
  have hy0 : 0 < y := hY.trans_le hy
  rw [integrand_eq hn δ' hs.1 hy0]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (sq_nonneg y)))
  have h1 : s * ZS M n δ' s y ≤ Kb c1 c2 y := hs.2.2 y hy0
  exact h1.trans (Kb_anti hc1 hc2 hY hy)

theorem strip_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) {s : ℝ}
    (hs : 0 < s ∧ s ≤ 1 ∧ ∀ y : ℝ, 0 < y → s * ZS M n δ' s y ≤ c1 * max 1 (y ^ 2)⁻¹ + c2 * KY y)
    {Y : ℝ} (hY : 0 < Y) :
    ENNReal.ofReal s * ∫⁻ z in stripH Y, SNE M n δ' s z ≤ ENNReal.ofReal (Kb c1 c2 Y / Y) := by
  rw [ofReal_mul_strip n δ' s hY, ← lintegral_Ici_inv_sq_mul hY (Kb c1 c2 Y)]
  exact setLIntegral_mono' measurableSet_Ici fun y hy => integrand_le hn δ' hc1 hc2 hs hY hy

theorem strip_bound {n : ℤ} (hn : 0 < n) (hnM : Nat.Coprime n.natAbs M) {δ' : ZMod M}
    (hδ : IsUnit δ') :
    ∃ c1 c2 : ℝ, 0 ≤ c1 ∧ 0 ≤ c2 ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ Y : ℝ, 0 < Y →
      ENNReal.ofReal s * ∫⁻ z in stripH Y, SNE M n δ' s z ≤ ENNReal.ofReal (Kb c1 c2 Y / Y) := by
  obtain ⟨c1, c2, hc1, hc2, hev⟩ := exists_dom hn hnM hδ
  exact ⟨c1, c2, hc1, hc2, hev.mono fun s hs Y hY => strip_le hn δ' hc1 hc2 hs hY⟩

theorem tendsto_strip {n : ℤ} (hn : 0 < n) (hnM : Nat.Coprime n.natAbs M) {δ' : ZMod M}
    (hδ : IsUnit δ') {Y : ℝ} (hY : 0 < Y) :
    Tendsto (fun s : ℝ => ENNReal.ofReal s * ∫⁻ z in stripH Y, SNE M n δ' s z) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (rhoE n / Y))) := by
  obtain ⟨c1, c2, hc1, hc2, hev⟩ := exists_dom hn hnM hδ
  have e : (fun s : ℝ => ENNReal.ofReal s * ∫⁻ z in stripH Y, SNE M n δ' s z) =
      fun s => ∫⁻ y in Ici Y, ENNReal.ofReal s * (ENNReal.ofReal ((y ^ 2)⁻¹) * ZE M n δ' s y) := by
    funext s
    exact ofReal_mul_strip n δ' s hY
  rw [e, ← lintegral_Ici_inv_sq_mul hY (rhoE n)]
  refine tendsto_lintegral_filter_of_dominated_convergence'
    (fun y => ENNReal.ofReal ((y ^ 2)⁻¹ * Kb c1 c2 Y)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun s =>
      (measurable_const.mul (measurable_inv_sq_ofReal.mul (measurable_ZE n δ' s))).aemeasurable
  · filter_upwards [hev] with s hs
    exact (ae_restrict_iff' measurableSet_Ici).2
      (ae_of_all _ fun y hy => integrand_le hn δ' hc1 hc2 hs hY hy)
  · rw [lintegral_Ici_inv_sq_mul hY]
    exact ENNReal.ofReal_ne_top
  · refine (ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun y hy => ?_)
    have hy0 : 0 < y := hY.trans_le hy
    have h := ENNReal.tendsto_ofReal ((tendsto_ZS_rho hn hnM hδ hy0).const_mul ((y ^ 2)⁻¹))
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (integrand_eq hn δ' hs hy0).symm

/-! ## The `m`-sum -/

lemma hasSum_inv_sq_succ : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  simpa using h

lemma tsum_two_ofReal {a y0 : ℝ} (ha : 0 ≤ a) (hy0 : 0 < y0) :
    ∑' m : ℕ, 2 * ENNReal.ofReal (a / (((m : ℝ) + 1) ^ 2 * y0)) =
      ENNReal.ofReal (2 * a / y0 * (π ^ 2 / 6)) := by
  have hs := hasSum_inv_sq_succ.mul_left (2 * a / y0)
  have hnn : ∀ m : ℕ, 0 ≤ 2 * a / y0 * (1 / ((m : ℝ) + 1) ^ 2) := fun m => by positivity
  have e : ∀ m : ℕ, 2 * ENNReal.ofReal (a / (((m : ℝ) + 1) ^ 2 * y0)) =
      ENNReal.ofReal (2 * a / y0 * (1 / ((m : ℝ) + 1) ^ 2)) := by
    intro m
    have hX : ((m : ℝ) + 1) ^ 2 ≠ 0 := by positivity
    have hy0' : y0 ≠ 0 := hy0.ne'
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    field_simp
  simp_rw [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs.summable, hs.tsum_eq]

theorem tendsto_eCnt {n : ℤ} (hn : 0 < n) (hnM : Nat.Coprime n.natAbs M) {δ' : ZMod M}
    (hδ : IsUnit δ') {y0 : ℝ} (hy0 : 0 < y0) :
    Tendsto (fun s : ℝ => ENNReal.ofReal s * ∫⁻ z in 𝒟, SNE M n δ' s z * eCnt y0 z) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (2 * rhoE n / y0 * (π ^ 2 / 6)))) := by
  obtain ⟨c1, c2, hc1, hc2, hev⟩ := strip_bound hn hnM hδ
  have hYm : ∀ m : ℕ, 0 < ((m : ℝ) + 1) ^ 2 * y0 := fun m => by positivity
  have hYm1 : ∀ m : ℕ, y0 ≤ ((m : ℝ) + 1) ^ 2 * y0 := fun m => by
    have h0 : (0 : ℝ) ≤ m := m.cast_nonneg
    have : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
    nlinarith
  have e : (fun s : ℝ => ENNReal.ofReal s * ∫⁻ z in 𝒟, SNE M n δ' s z * eCnt y0 z) = fun s =>
      ∫⁻ m : ℕ, 2 * (ENNReal.ofReal s * ∫⁻ z in stripH (((m : ℝ) + 1) ^ 2 * y0), SNE M n δ' s z)
        ∂Measure.count := by
    funext s
    rw [lintegral_fd_mul_eCnt (measurable_SNE n δ' s) (fun γ z => SNE_smul n δ' s γ z) y0,
      lintegral_count, ← ENNReal.tsum_mul_left]
    congr 1
    funext m
    ring
  rw [e, ← tsum_two_ofReal (rhoE_nonneg n) hy0, ← lintegral_count]
  refine tendsto_lintegral_filter_of_dominated_convergence'
    (fun m : ℕ => 2 * ENNReal.ofReal (Kb c1 c2 y0 / (((m : ℝ) + 1) ^ 2 * y0))) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun s => (measurable_of_countable _).aemeasurable
  · filter_upwards [hev] with s hs
    refine ae_of_all _ fun m => ?_
    gcongr 2 * ?_
    refine (hs _ (hYm m)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (Kb_anti hc1 hc2 hy0 (hYm1 m)) (hYm m).le
  · rw [lintegral_count, tsum_two_ofReal (Kb_nonneg hc1 hc2 hy0) hy0]
    exact ENNReal.ofReal_ne_top
  · exact ae_of_all _ fun m =>
      ENNReal.Tendsto.const_mul (tendsto_strip hn hnM hδ (hYm m)) (Or.inr (by simp))

end RamanujanPetersson.EllW2


