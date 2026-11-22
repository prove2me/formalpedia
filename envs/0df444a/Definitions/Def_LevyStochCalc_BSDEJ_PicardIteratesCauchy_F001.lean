-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesCauchy_F001
-- name    : LevyStochCalc_BSDEJ_PicardIteratesCauchy_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:04:46.75779+00:00
-- url     : https://prove2.me/theorems/7ab14dce-88fb-46f4-8d29-dcf010973f14
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.PicardIteratesCauchy
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.PicardIteratesCauchy. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesCauchy_F000
import Definitions.Def_SourceProof_21431cc356d9363f35d4c54e
import Definitions.Def_SourceProof_388a40baa407d0b0ae15b23c
import Definitions.Def_SourceProof_39fe24509dab75a4c4176089
import Definitions.Def_SourceProof_74549f342024460457cb4481
import Definitions.Def_SourceProof_869b93343dd8836d1387ab78

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The geometric Cauchy estimate for the Picard iterates

The exponentially weighted norm `wNorm` at a nonnegative weight dominates the energies of the
value process, of the diffusion coordinates and of the jump integrand, and is subadditive along
an intermediate triple up to a factor of two. Combined with the one-step contraction at the Young
weight `β = max 2 (24 L²)`, this gives a geometric bound with ratio `1/4` on the weighted norm of
consecutive Picard iterates, and hence a Cauchy estimate for the iterates in the weighted norm
and in the unweighted energies on the horizon.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Subadditivity and lower bounds for the weighted norm -/

section WNorm

variable {β T : ℝ}

omit [SigmaFinite ν] in
/-- The weighted norm of the difference of a triple with itself vanishes. -/
theorem wNorm_sub_self (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) :
    wNorm P ν β T (fun t ω => Y t ω - Y t ω) (fun t ω => Z t ω - Z t ω)
      (fun t ω e => U t ω e - U t ω e) = 0 := by
  simp [wNorm]
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The weighted norm of a difference of triples is symmetric in the two triples. -/
theorem wNorm_sub_comm (Y₁ Y₂ : ℝ → Ω → ℝ) (Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ))
    (U₁ U₂ : ℝ → Ω → E → ℝ) :
    wNorm P ν β T (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
        (fun t ω e => U₁ t ω e - U₂ t ω e)
      = wNorm P ν β T (fun t ω => Y₂ t ω - Y₁ t ω) (fun t ω => Z₂ t ω - Z₁ t ω)
        (fun t ω e => U₂ t ω e - U₁ t ω e) := by
  classical
  have hswap : ∀ a b : ℝ, (‖a - b‖₊ : ℝ≥0∞) ^ 2 = (‖b - a‖₊ : ℝ≥0∞) ^ 2 := fun a b => by
    rw [coe_nnnorm_sub_comm]
  simp only [wNorm, Pi.sub_apply]
  refine lintegral_congr fun ω => lintegral_congr fun s => ?_
  congr 2
  · congr 1
    · exact hswap _ _
    · exact Finset.sum_congr rfl fun j _ => hswap _ _
  · exact lintegral_congr fun e => hswap _ _
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The energy of the pointwise density on the horizon is at most the weighted norm. -/
theorem lintegral_density_le_wNorm (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, density ν Y Z U ω s ∂volume ∂P ≤ wNorm P ν β T Y Z U := by
  rw [wNorm_eq_lintegral_density]
  refine lintegral_mono fun ω => lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal]
  exact Real.one_le_exp (mul_nonneg hβ hs.1)
omit [SigmaFinite ν] in
/-- The sum of the energy of the value, of the energies of the diffusion coordinates and of the
marked energy of the jump integrand is at most the weighted norm. -/
theorem energies_le_wNorm (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) :
    Brownian.Ito.energy P T (fun ω s => Y s ω)
        + (∑ j, Brownian.Ito.energy P T (fun ω s => Z s ω j))
        + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e)
      ≤ wNorm P ν β T Y Z U := by
  rw [← _root_.Prove2MeSourceProof.h_869b93343dd8836d1387ab78 hYm hZm]
  exact lintegral_density_le_wNorm hβ
omit [SigmaFinite ν] in
/-- The energy of the value of a triple is at most its weighted norm. -/
theorem energy_le_wNorm (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) :
    Brownian.Ito.energy P T (fun ω s => Y s ω) ≤ wNorm P ν β T Y Z U :=
  (le_self_add.trans le_self_add).trans (energies_le_wNorm hβ hYm hZm)
omit [SigmaFinite ν] in
/-- The energy of a diffusion coordinate of a triple is at most its weighted norm. -/
theorem energy_coord_le_wNorm (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) (i : Fin d) :
    Brownian.Ito.energy P T (fun ω s => Z s ω i) ≤ wNorm P ν β T Y Z U :=
  ((Finset.single_le_sum (f := fun j => Brownian.Ito.energy P T (fun ω s => Z s ω j))
    (fun _ _ => zero_le) (Finset.mem_univ i)).trans
      (le_add_self.trans le_self_add)).trans (energies_le_wNorm hβ hYm hZm)
omit [SigmaFinite ν] in
/-- The marked energy of the jump integrand of a triple is at most its weighted norm. -/
theorem markedEnergy_le_wNorm (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) :
    Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≤ wNorm P ν β T Y Z U :=
  le_add_self.trans (energies_le_wNorm hβ hYm hZm)
/-- The value process of an admissible triple is jointly measurable in the sample point and the
time. -/
theorem Admissible.measurable_uncurry_Y {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (h : Admissible D T Y Z U) : Measurable (Function.uncurry fun ω s => Y s ω) :=
  h.Y_meas.comp measurable_swap
/-- The weighted norm of the difference of two admissible triples is finite. -/
theorem Admissible.wNorm_sub_ne_top {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {Y₁ Y₂ : ℝ → Ω → ℝ} {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U₁ U₂ : ℝ → Ω → E → ℝ}
    (h₁ : Admissible D T Y₁ Z₁ U₁) (h₂ : Admissible D T Y₂ Z₂ U₂) (hβ : 0 ≤ β) :
    wNorm P ν β T (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
      (fun t ω e => U₁ t ω e - U₂ t ω e) ≠ ⊤ :=
  _root_.Prove2MeSourceProof.h_74549f342024460457cb4481 hβ (h₁.measurable_uncurry_Y.sub h₂.measurable_uncurry_Y)
    (fun j => (h₁.Z_meas j).sub (h₂.Z_meas j))
    (_root_.Prove2MeSourceProof.h_21431cc356d9363f35d4c54e h₁.measurable_uncurry_Y h₂.measurable_uncurry_Y h₁.Y_sq h₂.Y_sq)
    (fun j => _root_.Prove2MeSourceProof.h_21431cc356d9363f35d4c54e (h₁.Z_meas j) (h₂.Z_meas j) (h₁.Z_sq j) (h₂.Z_sq j))
    (_root_.Prove2MeSourceProof.h_388a40baa407d0b0ae15b23c h₁.U_meas h₂.U_meas
      (lt_top_iff_ne_top.mpr h₁.U_sq) (lt_top_iff_ne_top.mpr h₂.U_sq)).ne
end WNorm

/-! ### The geometric Cauchy estimate along the iterates -/

section Cauchy

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ}
  (hT : 0 < T)
  (hf : ∀ u : E → ℝ, Measurable fun q : ℝ × ℝ × (Fin d → ℝ) => f q.1 q.2.1 q.2.2 u)
  (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
    (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
      ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
        + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
  (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
  (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P)

/-- The Young weight of the Picard contraction is nonnegative. -/
theorem zero_le_youngWeight (L : ℝ) : (0 : ℝ) ≤ max 2 (24 * L ^ 2) :=
  le_trans (by norm_num) (le_max_left _ _)
/-- Consecutive Picard iterates contract the weighted norm by `1/4` at the Young weight
`max 2 (24 L²)`. -/
theorem wNorm_picardSeq_succ_le (hL : 0 ≤ L) (p₀ : AdmTriple D T) (n : ℕ) :
    wNorm P ν (max 2 (24 * L ^ 2)) T
        (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1 + 1)).1 t ω
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).1 t ω)
        (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1 + 1)).2.1 t ω
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.1 t ω)
        (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1 + 1)).2.2 t ω e
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.2 t ω e)
      ≤ 4⁻¹ * wNorm P ν (max 2 (24 * L ^ 2)) T
        (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).1 t ω
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1 t ω)
        (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.1 t ω
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1 t ω)
        (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.2 t ω e
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 t ω e) := by
  obtain ⟨b₁, hb₁m, hb₁p, hb₁z, hb₁q, hb₁, hout₁⟩ :=
    picardSeq_succ_isStep hT hf hlip hf0 hξ2 hξm p₀ (n + 1)
  obtain ⟨b₂, hb₂m, hb₂p, hb₂z, hb₂q, hb₂, hout₂⟩ :=
    picardSeq_succ_isStep hT hf hlip hf0 hξ2 hξm p₀ n
  have hA₁ := picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ (n + 1)
  have hA₀ := picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ n
  exact wNorm_sub_le_of_picardOutput hL hlip hT hout₁ hout₂
    (hA₁.measurable_uncurry_Y.sub hA₀.measurable_uncurry_Y)
    (fun j => (hA₁.Z_meas j).sub (hA₀.Z_meas j)) (hA₁.U_meas.sub hA₀.U_meas)
    hb₁m hb₁p hb₁z hb₁q hb₁ hb₂m hb₂p hb₂z hb₂q hb₂
    (hA₁.wNorm_sub_ne_top hA₀ (zero_le_youngWeight L))
/-- The weighted norm of consecutive Picard iterates decays geometrically with ratio `1/4`. -/
theorem wNorm_picardSeq_geom (hL : 0 ≤ L) (p₀ : AdmTriple D T) (n : ℕ) :
    wNorm P ν (max 2 (24 * L ^ 2)) T
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1 t ω)
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1 t ω)
      (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.2 t ω e
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 t ω e)
      ≤ ((4 : ℝ≥0∞)⁻¹) ^ n *
        wNorm P ν (max 2 (24 * L ^ 2)) T
          (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).1 t ω
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).1 t ω)
          (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.1 t ω
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.1 t ω)
          (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.2 t ω e
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.2 t ω e) := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine le_trans (wNorm_picardSeq_succ_le hT hf hlip hf0 hξ2 hξm hL p₀ n) ?_
    refine le_trans (mul_le_mul' le_rfl ih) (le_of_eq ?_)
    rw [pow_succ]
    ring
/-- The weighted norm of the difference between an iterate and a later one is at most four
times the geometric bound at the earlier index. -/
theorem wNorm_picardSeq_sub_le_of_add (hL : 0 ≤ L) (p₀ : AdmTriple D T) (k m : ℕ) :
    wNorm P ν (max 2 (24 * L ^ 2)) T
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (m + k)).1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).1 t ω)
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (m + k)).2.1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.1 t ω)
      (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (m + k)).2.2 t ω e
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.2 t ω e)
      ≤ 4 * ((4 : ℝ≥0∞)⁻¹) ^ m *
        wNorm P ν (max 2 (24 * L ^ 2)) T
          (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).1 t ω
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).1 t ω)
          (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.1 t ω
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.1 t ω)
          (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.2 t ω e
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.2 t ω e) := by
  have harith : ∀ a W : ℝ≥0∞,
      2 * (4 * (a * (4 : ℝ≥0∞)⁻¹) * W) + 2 * (a * W) = 4 * a * W := by
    intro a W
    have h84 : (8 : ℝ≥0∞) * (4 : ℝ≥0∞)⁻¹ = 2 := by
      rw [show (8 : ℝ≥0∞) = 2 * 4 by norm_num, mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    calc 2 * (4 * (a * (4 : ℝ≥0∞)⁻¹) * W) + 2 * (a * W)
        = 8 * (4 : ℝ≥0∞)⁻¹ * (a * W) + 2 * (a * W) := by ring
      _ = 2 * (a * W) + 2 * (a * W) := by rw [h84]
      _ = 4 * a * W := by ring
  induction k generalizing m with
  | zero =>
    rw [Nat.add_zero, wNorm_sub_self]
    exact zero_le
  | succ k ih =>
    have hidx : m + (k + 1) = m + 1 + k := by omega
    rw [hidx]
    have hA₁ := picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ (m + 1 + k)
    have hA₂ := picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ (m + 1)
    refine le_trans (_root_.Prove2MeSourceProof.h_39fe24509dab75a4c4176089
      (hA₁.measurable_uncurry_Y.sub hA₂.measurable_uncurry_Y)
      (fun j => (hA₁.Z_meas j).sub (hA₂.Z_meas j)) (hA₁.U_meas.sub hA₂.U_meas)) ?_
    refine le_trans (add_le_add (mul_le_mul' le_rfl (ih (m + 1)))
      (mul_le_mul' le_rfl (wNorm_picardSeq_geom hT hf hlip hf0 hξ2 hξm hL p₀ m)))
      (le_of_eq ?_)
    rw [pow_succ]
    exact harith _ _
/-- Powers of `1/4` in the extended nonnegative reals decrease along the exponent. -/
theorem pow_four_inv_le_of_le {i j : ℕ} (hij : i ≤ j) :
    ((4 : ℝ≥0∞)⁻¹) ^ j ≤ ((4 : ℝ≥0∞)⁻¹) ^ i := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [pow_add]
  exact mul_le_of_le_one_right' (pow_le_one' (ENNReal.inv_le_one.mpr (by norm_num)) c)
/-- A geometric sequence of ratio `1/4` with a finite factor is eventually below any positive
threshold. -/
theorem exists_geom_lt (W : ℝ≥0∞) (hW : W ≠ ⊤) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → 4 * ((4 : ℝ≥0∞)⁻¹) ^ j * W < ε := by
  have htend : Tendsto (fun N : ℕ => ((4 : ℝ≥0∞)⁻¹) ^ N * (4 * W)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ((4 : ℝ≥0∞)⁻¹) ^ N) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by rw [ENNReal.inv_lt_one]; norm_num)
    simpa using ENNReal.Tendsto.mul_const h1
      (Or.inr (ENNReal.mul_ne_top (by norm_num) hW))
  obtain ⟨N, hN⟩ := (htend.eventually (gt_mem_nhds hε)).exists
  refine ⟨N, fun j hj => ?_⟩
  refine lt_of_le_of_lt ?_ hN
  calc 4 * ((4 : ℝ≥0∞)⁻¹) ^ j * W = ((4 : ℝ≥0∞)⁻¹) ^ j * (4 * W) := by ring
    _ ≤ ((4 : ℝ≥0∞)⁻¹) ^ N * (4 * W) := mul_le_mul' (pow_four_inv_le_of_le hj) le_rfl
/-- The weighted norm of the difference of two Picard iterates is at most four times the
geometric bound at the smaller index. -/
theorem wNorm_picardSeq_sub_le (hL : 0 ≤ L) (p₀ : AdmTriple D T) (m n : ℕ) :
    wNorm P ν (max 2 (24 * L ^ 2)) T
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1 t ω)
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1 t ω)
      (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.2 t ω e
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 t ω e)
      ≤ 4 * ((4 : ℝ≥0∞)⁻¹) ^ min m n *
        wNorm P ν (max 2 (24 * L ^ 2)) T
          (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).1 t ω
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).1 t ω)
          (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.1 t ω
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.1 t ω)
          (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.2 t ω e
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.2 t ω e) := by
  rcases le_total m n with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [min_eq_left (Nat.le_add_right m k)]
    refine le_trans (le_of_eq (wNorm_sub_comm _ _ _ _ _ _)) ?_
    exact wNorm_picardSeq_sub_le_of_add hT hf hlip hf0 hξ2 hξm hL p₀ k m
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [min_eq_right (Nat.le_add_right n k)]
    exact wNorm_picardSeq_sub_le_of_add hT hf hlip hf0 hξ2 hξm hL p₀ k n
/-- The weighted norm of the first difference of the Picard iterates is finite. -/
theorem wNorm_picardSeq_zero_ne_top (p₀ : AdmTriple D T) :
    wNorm P ν (max 2 (24 * L ^ 2)) T
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).1 t ω)
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.1 t ω)
      (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.2 t ω e
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.2 t ω e) ≠ ⊤ :=
  (picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ 1).wNorm_sub_ne_top
    (picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ 0) (zero_le_youngWeight L)
/-- The Picard iterates are Cauchy for the weighted norm at the Young weight
`max 2 (24 L²)`. -/
theorem wNorm_picardSeq_cauchy (hL : 0 ≤ L) (p₀ : AdmTriple D T) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n →
      wNorm P ν (max 2 (24 * L ^ 2)) T
        (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).1 t ω
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1 t ω)
        (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.1 t ω
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1 t ω)
        (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.2 t ω e
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 t ω e) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_geom_lt _
    (wNorm_picardSeq_zero_ne_top hT hf hlip hf0 hξ2 hξm p₀) ε hε
  exact ⟨N, fun m hm n hn => lt_of_le_of_lt
    (wNorm_picardSeq_sub_le hT hf hlip hf0 hξ2 hξm hL p₀ m n) (hN _ (le_min hm hn))⟩
end Cauchy

end LevyStochCalc.BSDEJ.Solves


