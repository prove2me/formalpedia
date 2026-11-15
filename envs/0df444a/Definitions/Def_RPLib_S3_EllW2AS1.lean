-- Prove2me | Definitions.Def_RPLib_S3_EllW2AS1
-- name    : RPLib_S3_EllW2AS1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:55:35.754192+00:00
-- url     : https://prove2.me/theorems/27401be9-b978-4053-aa13-264ba759beb7
-- title:
--   The Eichler-Selberg trace formula in weight two: the uniform domination of `s · ZS` and the strip in `(x, y)` form
-- statement:
--   The uniform domination of `s · ZS` and the strip in `(x, y)` form.
--
--   * `rhoE n = 3 σ_{-1}(|n|)`; `tendsto_ZS_rho`: `s · ZS(s, y) → rhoE n` (`y > 0`).
--   * **`exists_dom`**: constants `c1, c2 ≥ 0` with, eventually in `s → 0+`, `0 < s ≤ 1` and
--     `s · ZS(s, y) ≤ c1 · max 1 y⁻² + c2 · KY y` for every `y > 0`.
--   * `Kb c1 c2 Y`, `max_inv_sq_anti`, `KY_anti`, `Kb_anti`.
--   * `lintegral_Ici_inv_sq`: `∫⁻_{y ≥ Y} y⁻² = Y⁻¹`.
--   * `ZE s y = ∫⁻_{x ∈ [-1/2, 1/2)} SNE(x + iy)`; `measurable_ZE`; `ZE_eq` (`= ofReal (ZS s y)`);
--     **`lintegral_stripH_ZE`**: `∫⁻_{S_Y} SNE = ∫⁻_{y ≥ Y} y⁻² ZE s y`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec, Spectral Methods of Automorphic Forms, 2nd ed., Graduate Studies in Mathematics 53, AMS 2002, Chapter 2

import Mathlib
import Definitions.Def_RPLib_S3_EllW2MV8

/-!
# S3-ES-Wt2 (O6, file AS1): the uniform domination of `s · ZS` and the strip in `(x, y)` form

* `rhoE n = 3 σ_{-1}(|n|)`; `tendsto_ZS_rho`: `s · ZS(s, y) → rhoE n` (`y > 0`).
* **`exists_dom`**: constants `c1, c2 ≥ 0` with, eventually in `s → 0+`, `0 < s ≤ 1` and
  `s · ZS(s, y) ≤ c1 · max 1 y⁻² + c2 · KY y` for every `y > 0`.
* `Kb c1 c2 Y`, `max_inv_sq_anti`, `KY_anti`, `Kb_anti`.
* `lintegral_Ici_inv_sq`: `∫⁻_{y ≥ Y} y⁻² = Y⁻¹`.
* `ZE s y = ∫⁻_{x ∈ [-1/2, 1/2)} SNE(x + iy)`; `measurable_ZE`; `ZE_eq` (`= ofReal (ZS s y)`);
  **`lintegral_stripH_ZE`**: `∫⁻_{S_Y} SNE = ∫⁻_{y ≥ Y} y⁻² ZE s y`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups ENNReal Modular Real

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-- The residue `3 σ_{-1}(|n|)`. -/
def rhoE (n : ℤ) : ℝ := 3 * ∑ h ∈ n.natAbs.divisors, (1 : ℝ) / h

lemma rhoE_nonneg (n : ℤ) : 0 ≤ rhoE n := by
  unfold rhoE
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun h _ => by positivity)

theorem tendsto_ZS_rho {n : ℤ} (hn : 0 < n) (hnM : Nat.Coprime n.natAbs M) {δ' : ZMod M}
    (hδ : IsUnit δ') {y : ℝ} (hy : 0 < y) :
    Tendsto (fun s : ℝ => s * ZS M n δ' s y) (𝓝[>] 0) (𝓝 (rhoE n)) :=
  tendsto_ZS_val hn hnM hδ hy

theorem exists_dom {n : ℤ} (hn : 0 < n) (hnM : Nat.Coprime n.natAbs M) {δ' : ZMod M}
    (hδ : IsUnit δ') :
    ∃ c1 c2 : ℝ, 0 ≤ c1 ∧ 0 ≤ c2 ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ 1 ∧
      ∀ y : ℝ, 0 < y → s * ZS M n δ' s y ≤ c1 * max 1 (y ^ 2)⁻¹ + c2 * KY y := by
  have hlim := tendsto_fpm_mean (M := M) hn.ne' hnM hδ
  set l := (∑ h ∈ n.natAbs.divisors, (1 : ℝ) / h) * (6 / Real.pi ^ 2) with hl
  have hl0 : 0 ≤ l := mul_nonneg (Finset.sum_nonneg fun h _ => by positivity) (by positivity)
  have hA := tendsto_abel (fpm_nonneg (M := M) n δ') hlim
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s * ∑' m : ℕ, Fab (fpm M n δ') s m < l / 2 + 1 :=
    hA.eventually (gt_mem_nhds (by linarith))
  refine ⟨(l / 2 + 1) * (4 * π ^ 2), |CZD M n|, by positivity, abs_nonneg _, ?_⟩
  filter_upwards [hev, Ioc_mem_nhdsGT one_pos] with s hs1 hs
  refine ⟨hs.1, hs.2, fun y hy => ?_⟩
  obtain ⟨_, hJ⟩ := abs_ZS_sub_le (M := M) hn δ' hs.1 hs.2 hy
  have hZ : ZS M n δ' s y ≤ ∑' c : ℤ, Jm M n δ' s y c + KY y * CZD M n := by
    have := (abs_le.1 hJ).2; linarith
  rw [tsum_Jm_eq hn δ' hs.1 hs.2 hy] at hZ
  have hn' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.le
  set C := 2 * max 1 (y ^ 2)⁻¹ * (2 * π ^ 2) with hC
  have hC0 : 0 ≤ C := by positivity
  have hF := summable_Fab (fpm_nonneg (M := M) n δ') hlim hs.1
  have hFn : ∀ m, 0 ≤ Fab (fpm M n δ') s m := fun m => Fab_nonneg (fpm_nonneg n δ') s m
  have hk : ∀ m, |kerY (n : ℝ) y s m| ≤ C := fun m => abs_kerY_le hn' hy hs.1 hs.2 m
  have hsum : Summable fun m => Fab (fpm M n δ') s m * kerY (n : ℝ) y s m := by
    refine Summable.of_norm_bounded (hF.mul_right C) fun m => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hFn m)]
    exact mul_le_mul_of_nonneg_left (hk m) (hFn m)
  have hb : ∀ m, Fab (fpm M n δ') s m * kerY (n : ℝ) y s m ≤ Fab (fpm M n δ') s m * C := fun m =>
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hk m)) (hFn m)
  have h1 : ∑' m, Fab (fpm M n δ') s m * kerY (n : ℝ) y s m ≤ (∑' m, Fab (fpm M n δ') s m) * C := by
    rw [← tsum_mul_right]
    exact hsum.tsum_le_tsum hb (hF.mul_right C)
  have hK := KY_nonneg hy
  have h2 : s * (KY y * CZD M n) ≤ KY y * |CZD M n| := by
    calc s * (KY y * CZD M n) ≤ s * (KY y * |CZD M n|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self _) hK) hs.1.le
      _ ≤ 1 * (KY y * |CZD M n|) := mul_le_mul_of_nonneg_right hs.2 (mul_nonneg hK (abs_nonneg _))
      _ = KY y * |CZD M n| := one_mul _
  have h3 : (s * ∑' m, Fab (fpm M n δ') s m) * C ≤ (l / 2 + 1) * C :=
    mul_le_mul_of_nonneg_right hs1.le hC0
  calc s * ZS M n δ' s y
      ≤ s * ((∑' m, Fab (fpm M n δ') s m) * C + KY y * CZD M n) :=
        mul_le_mul_of_nonneg_left (by linarith) hs.1.le
    _ = (s * ∑' m, Fab (fpm M n δ') s m) * C + s * (KY y * CZD M n) := by ring
    _ ≤ (l / 2 + 1) * C + KY y * |CZD M n| := add_le_add h3 h2
    _ = (l / 2 + 1) * (4 * π ^ 2) * max 1 (y ^ 2)⁻¹ + |CZD M n| * KY y := by rw [hC]; ring

/-! ## Monotonicity of the bound -/

/-- The bound at height `Y`. -/
def Kb (c1 c2 Y : ℝ) : ℝ := c1 * max 1 (Y ^ 2)⁻¹ + c2 * KY Y

lemma max_inv_sq_anti {Y y : ℝ} (hY : 0 < Y) (h : Y ≤ y) : max 1 (y ^ 2)⁻¹ ≤ max 1 (Y ^ 2)⁻¹ :=
  max_le_max le_rfl (inv_anti₀ (pow_pos hY 2) (pow_le_pow_left₀ hY.le h 2))

lemma KY_anti {Y y : ℝ} (hY : 0 < Y) (h : Y ≤ y) : KY y ≤ KY Y := by
  unfold KY
  exact div_le_div₀ ((zero_le_one).trans (le_max_left _ _)) (max_inv_sq_anti hY h) hY h

lemma Kb_anti {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) {Y y : ℝ} (hY : 0 < Y) (h : Y ≤ y) :
    Kb c1 c2 y ≤ Kb c1 c2 Y :=
  add_le_add (mul_le_mul_of_nonneg_left (max_inv_sq_anti hY h) hc1)
    (mul_le_mul_of_nonneg_left (KY_anti hY h) hc2)

lemma Kb_nonneg {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) {Y : ℝ} (hY : 0 < Y) : 0 ≤ Kb c1 c2 Y :=
  add_nonneg (mul_nonneg hc1 ((zero_le_one).trans (le_max_left _ _))) (mul_nonneg hc2 (KY_nonneg hY))

/-! ## `∫⁻_{y ≥ Y} y⁻² = Y⁻¹` -/

theorem lintegral_Ici_inv_sq {Y : ℝ} (hY : 0 < Y) :
    ∫⁻ y in Ici Y, ENNReal.ofReal ((y ^ 2)⁻¹) = ENNReal.ofReal Y⁻¹ := by
  rw [← setLIntegral_congr Ioi_ae_eq_Ici]
  have hc : EqOn (fun y : ℝ => ENNReal.ofReal ((y ^ 2)⁻¹)) (fun y => ENNReal.ofReal (y ^ (-2 : ℝ)))
      (Ioi Y) := by
    intro y hy
    have hy0 : 0 ≤ y := hY.le.trans (le_of_lt hy)
    simp only
    rw [Real.rpow_neg hy0, Real.rpow_two]
  rw [setLIntegral_congr_fun measurableSet_Ioi hc]
  have hi := integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hY
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun y hy =>
      Real.rpow_nonneg (hY.le.trans (le_of_lt hy)) _)),
    integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hY]
  congr 1
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  ring

/-! ## The strip in `(x, y)` coordinates -/

/-- The `x`-integral of `SNE` over one period. -/
def ZE (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (s y : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ico (-(1 / 2 : ℝ)) (1 / 2), SNE M n δ' s (ofComplex ((x : ℂ) + y * Complex.I))

lemma measurable_ZE (n : ℤ) (δ' : ZMod M) (s : ℝ) : Measurable (ZE M n δ' s) := by
  have hf : Measurable fun p : ℝ × ℝ => SNE M n δ' s (ofComplex ((p.1 : ℂ) + p.2 * Complex.I)) :=
    (measurable_SNE n δ' s).comp (measurable_ofComplex.comp (by fun_prop))
  have h2 := hf.lintegral_prod_left' (μ := volume.restrict (Ico (-(1 / 2 : ℝ)) (1 / 2)))
  exact h2

lemma ZE_eq {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 0 < y) :
    ZE M n δ' s y = ENNReal.ofReal (ZS M n δ' s y) :=
  lintegral_SNE_Ico_ZS hn δ' hs hy

theorem lintegral_stripH_ZE (n : ℤ) (δ' : ZMod M) (s : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ∫⁻ z in stripH Y, SNE M n δ' s z =
      ∫⁻ y in Ici Y, ENNReal.ofReal ((y ^ 2)⁻¹) * ZE M n δ' s y :=
  setLIntegral_stripH hY (measurable_SNE n δ' s)

end RamanujanPetersson.EllW2


