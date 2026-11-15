-- Prove2me | Definitions.Def_RPLib_S3_EllW2I
-- name    : RPLib_S3_EllW2I
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:21:25.078376+00:00
-- url     : https://prove2.me/theorems/60dd08c7-04e4-4793-8dda-b90d7900ebbb
-- title:
--   The Eichler-Selberg trace formula in weight two: Stokes for the split/parabolic part at `s = 0` on `𝒟_Y`
-- statement:
--   Stokes for the split/parabolic part at `s = 0` on `𝒟_Y`.
--
--   * `wtS`: the weight `[IsSP] wt`; `wtS_conj`, `summable_wtS_mul` (from `summable_SP`).
--   * the weighted boundary terms at `m = 1` are summable; arcs cancel under `S`, sides under `T`.
--   * **`integral_truncS`**: `∫_{𝒟 ∩ {Im ≤ Y}} SPS_0 = -Σ' g, wtS g * topI g 1 Y`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2H

/-!
# S3-ES-Wt2 (O6, part I): Stokes for the split/parabolic part at `s = 0` on `𝒟_Y`

* `wtS`: the weight `[IsSP] wt`; `wtS_conj`, `summable_wtS_mul` (from `summable_SP`).
* the weighted boundary terms at `m = 1` are summable; arcs cancel under `S`, sides under `T`.
* **`integral_truncS`**: `∫_{𝒟 ∩ {Im ≤ Y}} SPS_0 = -Σ' g, wtS g * topI g 1 Y`.
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
/-- The split/parabolic rest weight `[IsSP g] wt g`. -/
def wtS (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (g : S3.Conj.Mat) : ℂ :=
  if IsSP g then HypPar.wt M n δ' g else 0

lemma wtS_of_not {n : ℤ} {δ' : ZMod M} {g : S3.Conj.Mat}
    (h : ¬(g.det = n ∧ HypPar.IsRest g ∧ IsSP g)) : wtS M n δ' g = 0 := by
  unfold wtS
  split_ifs with hs
  · exact HypPar.wt_of_not (fun h' => h ⟨h'.1, h'.2, hs⟩)
  · rfl

lemma norm_wtS_le (n : ℤ) (δ' : ZMod M) (g : S3.Conj.Mat) :
    ‖wtS M n δ' g‖ ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) := by
  unfold wtS
  split_ifs
  · exact HypPar.norm_wt_le n δ' g
  · rw [norm_zero]; positivity

lemma isSP_conj (h : SL(2, ℤ)) (g : S3.Conj.Mat) : IsSP (S3.Conj.conj h g) ↔ IsSP g := by
  unfold IsSP
  rw [HypPar.trace_conj', S3.Conj.det_conj]

lemma wtS_conj (n : ℤ) (δ' : ZMod M) (h : SL(2, ℤ)) (g : S3.Conj.Mat) :
    wtS M n δ' (S3.Conj.conj h g) = wtS M n δ' g := by
  unfold wtS
  rw [HypPar.wt_conj]
  by_cases hs : IsSP g
  · rw [if_pos ((isSP_conj h g).2 hs), if_pos hs]
  · rw [if_neg (fun h' => hs ((isSP_conj h g).1 h')), if_neg hs]

lemma eventually_largeS {n : ℤ} (hn : 0 < n) {R0 : ℝ} (hR0 : 0 < R0) :
    ∀ᶠ g : Matrix (Fin 2) (Fin 2) ℤ in cofinite, g.det = n → IsSP g → R0 ≤ N g := by
  have hs := summable_SP hn
  filter_upwards [hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (inv_pos.2 hR0))] with g hg hdet hsp
  rw [indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g} from ⟨hdet, hsp⟩),
    Eg_two] at hg
  have hNp := N_pos (g := g) (by rw [hdet]; exact hn)
  exact ((inv_lt_inv₀ hNp hR0).1 hg).le

lemma summable_wtS_mul {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {T : S3.Conj.Mat → ℂ}
    {C R0 : ℝ} (hC : 0 ≤ C) (hR0 : 0 < R0)
    (hT : ∀ g : S3.Conj.Mat, g.det = n → HypPar.IsRest g → IsSP g → R0 ≤ N g →
      ‖T g‖ ≤ C * HypPar.Eg 2 g) :
    Summable fun g => wtS M n δ' g * T g := by
  refine Summable.of_norm_bounded_eventually
    ((summable_SP hn).mul_left ((Fintype.card (Fin 2 → ZMod M) : ℝ) * C)) ?_
  filter_upwards [eventually_largeS hn hR0] with g hg
  by_cases h : g.det = n ∧ HypPar.IsRest g ∧ IsSP g
  · rw [norm_mul, indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g} from
      ⟨h.1, h.2.2⟩)]
    have h1 := norm_wtS_le n δ' g
    have h2 := hT g h.1 h.2.1 h.2.2 (hg h.1 h.2.2)
    calc ‖wtS M n δ' g‖ * ‖T g‖ ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) * (C * HypPar.Eg 2 g) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (Fintype.card (Fin 2 → ZMod M) : ℝ) * C * HypPar.Eg 2 g := by ring
  · rw [wtS_of_not h, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hC)
      (indicator_nonneg (fun g _ => HypPar.Eg_nonneg 2 g) g)

lemma summable_topS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => wtS M n δ' g * HypPar.topI g 1 Y :=
  summable_wtS_mul hn δ' (T := fun g => HypPar.topI g 1 Y) (HypPar.CV_nonneg 1 (by linarith))
    (HypPar.R0_pos hn hY) fun g hg _ _ hR =>
      HypPar.norm_topI_le (by rw [hg]; exact hn) le_rfl hY (by rw [hg]; exact hR)

lemma summable_arcS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => wtS M n δ' g * HypPar.arcI g 1 :=
  summable_wtS_mul hn δ' (T := fun g => HypPar.arcI g 1) (C := 2 * HypPar.CV 1 Y)
    (mul_nonneg (by norm_num) (HypPar.CV_nonneg 1 (by linarith))) (HypPar.R0_pos hn hY)
    fun g hg _ _ hR => HypPar.norm_arcI_le (by rw [hg]; exact hn) le_rfl hY (by rw [hg]; exact hR)

lemma summable_sideAS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => wtS M n δ' g * HypPar.sideA g 1 Y :=
  summable_wtS_mul hn δ' (T := fun g => HypPar.sideA g 1 Y) (C := HypPar.CV 1 Y * Y)
    (mul_nonneg (HypPar.CV_nonneg 1 (by linarith)) (by linarith)) (HypPar.R0_pos hn hY)
    fun g hg _ _ hR => HypPar.norm_sideA_le (by rw [hg]; exact hn) le_rfl hY (by rw [hg]; exact hR)

lemma summable_sideBS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => wtS M n δ' g * HypPar.sideB g 1 Y :=
  summable_wtS_mul hn δ' (T := fun g => HypPar.sideB g 1 Y) (C := HypPar.CV 1 Y * Y)
    (mul_nonneg (HypPar.CV_nonneg 1 (by linarith)) (by linarith)) (HypPar.R0_pos hn hY)
    fun g hg _ _ hR => HypPar.norm_sideB_le (by rw [hg]; exact hn) le_rfl hY (by rw [hg]; exact hR)

/-- The `g`-th term of `SPS_0 / y²` on `regY`. -/
def FgS (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (g : S3.Conj.Mat) (p : ℝ × ℝ) : ℂ :=
  wtS M n δ' g * (phiG (1 + 1) g (ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2))

lemma integrable_FgS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (Y : ℝ) (g : S3.Conj.Mat) :
    Integrable (FgS M n δ' g) (volume.restrict (HypPar.regY Y)) := by
  by_cases h : g.det = n ∧ HypPar.IsRest g ∧ IsSP g
  · exact Integrable.const_mul
      (HypPar.integrableOn_phiG_div (by rw [h.1]; exact hn) (HypPar.goodQ_of_rest h.2.1) 1 le_rfl Y) _
  · have e : FgS M n δ' g = fun _ => 0 := by
      funext p; unfold FgS; rw [wtS_of_not h, zero_mul]
    rw [e]; exact integrable_zero _ _ _

lemma integral_norm_FgS_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ} (hY : 1 ≤ Y)
    (g : S3.Conj.Mat) :
    ∫ p in HypPar.regY Y, ‖FgS M n δ' g p‖ ≤
      ((Fintype.card (Fin 2 → ZMod M) : ℝ) * (4 * (Y ^ (1 + 1) * (144 * Y ^ 4) ^ (1 + 1))) *
        volume.real (HypPar.regY Y)) *
        {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g}.indicator (HypPar.Eg (1 + 1)) g := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  by_cases h : g.det = n ∧ HypPar.IsRest g ∧ IsSP g
  · rw [indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g} from
      ⟨h.1, h.2.2⟩)]
    have hdet : 0 < g.det := by rw [h.1]; exact hn
    have hb : ∀ p ∈ HypPar.regY Y, ‖‖FgS M n δ' g p‖‖ ≤
        (Fintype.card (Fin 2 → ZMod M) : ℝ) *
          (4 * (Y ^ (1 + 1) * (144 * Y ^ 4) ^ (1 + 1) * HypPar.Eg (1 + 1) g)) := by
      intro p hp
      rw [norm_norm]
      unfold FgS
      rw [norm_mul]
      exact mul_le_mul (norm_wtS_le n δ' g) (HypPar.norm_phiG_div_le hdet (1 + 1) hY hp)
        (norm_nonneg _) (Nat.cast_nonneg _)
    have := norm_setIntegral_le_of_norm_le_const
      ((HypPar.isCompact_regY Y).measure_lt_top (μ := volume)) hb
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  · have e : ∀ p, ‖FgS M n δ' g p‖ = 0 := fun p => by
      unfold FgS; rw [wtS_of_not h, zero_mul, norm_zero]
    simp only [e, integral_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))
      measureReal_nonneg) (indicator_nonneg (fun g _ => HypPar.Eg_nonneg _ g) g)

lemma summable_integral_norm_FgS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => ∫ p in HypPar.regY Y, ‖FgS M n δ' g p‖ :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (integral_norm_FgS_le hn δ' hY) ((summable_SP hn).mul_left _)

lemma integral_FgS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ} (hY : 1 ≤ Y) (g : S3.Conj.Mat) :
    ∫ p in HypPar.regY Y, FgS M n δ' g p =
      -(wtS M n δ' g * HypPar.topI g 1 Y) + wtS M n δ' g * HypPar.arcI g 1 -
        I * (wtS M n δ' g * HypPar.sideA g 1 Y - wtS M n δ' g * HypPar.sideB g 1 Y) := by
  unfold FgS
  rw [integral_const_mul]
  by_cases h : g.det = n ∧ HypPar.IsRest g ∧ IsSP g
  · rw [HypPar.stokes_g (by rw [h.1]; exact hn) (HypPar.goodQ_of_rest h.2.1) 1 le_rfl hY]; ring
  · rw [wtS_of_not h]; ring

lemma tsum_arc_zeroS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) :
    ∑' g : S3.Conj.Mat, wtS M n δ' g * HypPar.arcI g 1 = 0 := by
  have hpt : ∀ g : S3.Conj.Mat, wtS M n δ' (HypPar.conjEquiv ModularGroup.S g) *
      HypPar.arcI (HypPar.conjEquiv ModularGroup.S g) 1 = -(wtS M n δ' g * HypPar.arcI g 1) := by
    intro g
    show wtS M n δ' (S3.Conj.conj ModularGroup.S g) * HypPar.arcI (S3.Conj.conj ModularGroup.S g) 1 = _
    rw [wtS_conj]
    by_cases h : g.det = n ∧ HypPar.IsRest g ∧ IsSP g
    · rw [HypPar.arcI_S (by rw [h.1]; exact hn) (HypPar.goodQ_of_rest h.2.1) 1]; ring
    · rw [wtS_of_not h]; ring
  have e : ∑' g : S3.Conj.Mat, wtS M n δ' g * HypPar.arcI g 1 =
      -∑' g : S3.Conj.Mat, wtS M n δ' g * HypPar.arcI g 1 :=
    ((HypPar.conjEquiv ModularGroup.S).tsum_eq (fun g => wtS M n δ' g * HypPar.arcI g 1)).symm.trans
      ((tsum_congr hpt).trans tsum_neg)
  linear_combination e / 2

lemma tsum_side_eqS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ} (hY : 0 < Y) :
    ∑' g : S3.Conj.Mat, wtS M n δ' g * HypPar.sideA g 1 Y =
      ∑' g : S3.Conj.Mat, wtS M n δ' g * HypPar.sideB g 1 Y := by
  have hpt : ∀ g : S3.Conj.Mat, wtS M n δ' (HypPar.conjEquiv ModularGroup.T g) *
      HypPar.sideA (HypPar.conjEquiv ModularGroup.T g) 1 Y = wtS M n δ' g * HypPar.sideB g 1 Y := by
    intro g
    show wtS M n δ' (S3.Conj.conj ModularGroup.T g) * HypPar.sideA (S3.Conj.conj ModularGroup.T g) 1 Y = _
    rw [wtS_conj]
    by_cases h : g.det = n ∧ HypPar.IsRest g ∧ IsSP g
    · rw [HypPar.sideA_T (by rw [h.1]; exact hn) (HypPar.goodQ_of_rest h.2.1) 1 hY]
    · rw [wtS_of_not h, zero_mul, zero_mul]
  exact ((HypPar.conjEquiv ModularGroup.T).tsum_eq (fun g => wtS M n δ' g * HypPar.sideA g 1 Y)).symm.trans
    (tsum_congr hpt)

lemma SPS_zero_eq (n : ℤ) (δ' : ZMod M) (z : ℍ) :
    SPS M n δ' 0 z = ∑' g : S3.Conj.Mat, wtS M n δ' g * phiG (1 + 1) g z := by
  unfold SPS
  refine tsum_congr fun g => ?_
  unfold termP wtS HypPar.wt
  rw [phiGS_zero]
  by_cases h : g.det = n ∧ HypPar.IsRest g ∧ IsSP g
  · rw [if_pos h, if_pos h.2.2, if_pos (And.intro h.1 h.2.1)]
  · rw [if_neg h]
    by_cases hs : IsSP g
    · rw [if_pos hs, if_neg (fun h' => h ⟨h'.1, h'.2, hs⟩), zero_mul]
    · rw [if_neg hs, zero_mul]

/-- **Stokes for the split/parabolic part at `s = 0`**: `∫_{𝒟 ∩ {Im ≤ Y}} SPS_0 = -Σ' g, wtS g * topI g 1 Y`. -/
theorem integral_truncS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, SPS M n δ' 0 z =
      -∑' g : S3.Conj.Mat, wtS M n δ' g * HypPar.topI g 1 Y := by
  have : Countable S3.Conj.Mat := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  have h1 : ∀ p ∈ HypPar.regY Y, SPS M n δ' 0 (ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2) =
      ∑' g : S3.Conj.Mat, FgS M n δ' g p := by
    intro p _
    rw [SPS_zero_eq, ← tsum_div_const]
    exact tsum_congr fun g => by unfold FgS; ring
  rw [HypPar.setIntegral_H_eq _ (HypPar.measurableSet_trunc Y) _ (HypPar.isClosed_regY Y).measurableSet
      (HypPar.coe_image_trunc Y),
    setIntegral_congr_fun (HypPar.isClosed_regY Y).measurableSet h1,
    ← integral_tsum_of_summable_integral_norm (integrable_FgS hn δ' Y)
      (summable_integral_norm_FgS hn δ' hY),
    tsum_congr (integral_FgS hn δ' hY)]
  have hsum := ((summable_topS hn δ' hY).hasSum.neg.add (summable_arcS hn δ' hY).hasSum).sub
    (((summable_sideAS hn δ' hY).hasSum.sub (summable_sideBS hn δ' hY).hasSum).mul_left I)
  refine hsum.tsum_eq.trans ?_
  rw [tsum_arc_zeroS hn δ', tsum_side_eqS hn δ' (by linarith : (0 : ℝ) < Y)]
  ring

end RamanujanPetersson.EllW2


