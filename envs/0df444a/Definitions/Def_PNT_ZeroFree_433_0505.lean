-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0505
-- name    : PNT_ZeroFree_433_0505
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:35:41.234004+00:00
-- url     : https://prove2.me/theorems/08d716ab-58d0-4624-9dda-e92f9896655e
-- title:
--   Zero-free region foundations: Detector.GramLatticeDecay, Detector.GramAnnularLattice [0505]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Detector.GramLatticeDecay
--   - OAI.NumberTheory.DirichletL.Detector.GramAnnularLattice
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/GramLatticeDecay.lean#L12-L294
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/GramAnnularLattice.lean#L13-L163

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0014
import Definitions.Def_PNT_ZeroFree_433_0021_1
import Definitions.Def_PNT_ZeroFree_433_0038
import Definitions.Def_PNT_ZeroFree_433_0038_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0045
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0079_1_1
import Definitions.Def_PNT_ZeroFree_433_0167
import Definitions.Def_PNT_ZeroFree_433_0327

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/GramLatticeDecay.lean#L12-L294
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/GramAnnularLattice.lean#L13-L163
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Detector.GramLatticeDecay
section
namespace OAI

noncomputable section
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramLatticeDecay
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

abbrev Joint := WithLp 2 (ℂ × ℂ)

def point (x y : ℂ) : Joint := WithLp.toLp 2 (x,y)

def sourceControl (S : Finset (ℕ × ℕ)) (W : 𝓢(Joint, ℂ)) : ℝ :=
  S.sup (schwartzSeminormFamily ℝ Joint ℂ) W

theorem sourceControl_nonneg (S : Finset (ℕ × ℕ)) (W : 𝓢(Joint, ℂ)) :
    0 ≤ sourceControl S W := apply_nonneg _ _

@[simp] theorem norm_point_sq (x y : ℂ) :
    ‖point x y‖^2 = ‖x‖^2 + ‖y‖^2 := WithLp.prod_norm_sq_eq_of_L2 _

theorem product_decay (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ((1+‖x‖^2)^2 * (1+‖y‖^2)^2) * ‖W (point x y)‖ ≤
      (2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W := by
  have hx := WithLp.norm_fst_le ℂ (point x y)
  have hy := WithLp.norm_snd_le ℂ (point x y)
  change ‖x‖ ≤ ‖point x y‖ at hx
  change ‖y‖ ≤ ‖point x y‖ at hy
  have hx2 : 1+‖x‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hy2 : 1+‖y‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hpow : (1+‖x‖^2)^2 * (1+‖y‖^2)^2 ≤ (1+‖point x y‖)^8 := by
    calc
      _ ≤ ((1+‖point x y‖)^2)^2 * ((1+‖point x y‖)^2)^2 := by gcongr
      _ = _ := by ring
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (8,0)) (k := 8) (n := 0) le_rfl le_rfl W (point x y)
  simp only [norm_iteratedFDeriv_zero] at h
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans h

def physicalPoint (N : ℝ) (m : O × O) : Joint :=
  point (eisEmbedding m.1 / (Real.sqrt N : ℂ))
    (eisEmbedding m.2 / (Real.sqrt N : ℂ))

theorem physicalPoint_eq_smul (N : ℝ) (m : O × O) :
    physicalPoint N m = (Real.sqrt N)⁻¹ • point (eisEmbedding m.1) (eisEmbedding m.2) := by
  apply WithLp.ofLp_injective
  simp [physicalPoint, point, div_eq_mul_inv, Algebra.smul_def, mul_comm]

theorem physical_summable (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N) :
    Summable (fun m : O × O => ‖W (physicalPoint N m)‖) := by
  let g : O → ℝ := fun m => ((1+N⁻¹*‖eisEmbedding m‖^2)^2)⁻¹
  have hg : Summable g := scaled_eisenstein_cauchy_summable _ (inv_pos.mpr hN)
  have hp := hg.mul_of_nonneg hg (fun _ => by dsimp [g]; positivity)
    (fun _ => by dsimp [g]; positivity)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hp.mul_left ((2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W))
  intro m
  have hb := product_decay W (eisEmbedding m.1 / (Real.sqrt N : ℂ))
    (eisEmbedding m.2 / (Real.sqrt N : ℂ))
  have hnorm (m : O) : ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 = N⁻¹*‖eisEmbedding m‖^2 := by
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hN.le]
    ring
  simp only [hnorm] at hb
  change ‖W (physicalPoint N m)‖ ≤ ((2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W) * (g m.1*g m.2)
  dsimp only [g]
  rw [ ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa only [physicalPoint, mul_comm] using hb

theorem physical_lattice_bound :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (N : ℝ), 1 ≤ N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2 := by
  refine ⟨Finset.Iic (8,0), (2:ℝ)^8 * (4*(1+Real.pi)^2)^2, by positivity, ?_⟩
  intro W N hN
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let g : O → ℝ := fun m => ((1+N⁻¹*‖eisEmbedding m‖^2)^2)⁻¹
  have hg : Summable g := scaled_eisenstein_cauchy_summable _ (inv_pos.mpr hNp)
  have hp := hg.mul_of_nonneg hg (fun _ => by dsimp [g]; positivity)
    (fun _ => by dsimp [g]; positivity)
  have hpoint (m : O × O) : ‖W (physicalPoint N m)‖ ≤
      ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W) * (g m.1*g m.2) := by
    have hb := product_decay W (eisEmbedding m.1 / (Real.sqrt N : ℂ))
      (eisEmbedding m.2 / (Real.sqrt N : ℂ))
    have hn (m : O) : ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 = N⁻¹*‖eisEmbedding m‖^2 := by
      rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hNp.le]
      ring
    simp only [hn] at hb
    dsimp only [g]
    rw [ ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    simpa only [physicalPoint, mul_comm] using hb
  have hmass : (∑' m : O, g m) ≤ (4*(1+Real.pi)^2)*N := by
    have h := scaled_eisenstein_cauchy_small N⁻¹ (inv_pos.mpr hNp) ((inv_le_one₀ hNp).mpr hN)
    have hh := mul_le_mul_of_nonneg_left h hNp.le
    simpa only [g, ← mul_assoc, mul_inv_cancel₀ hNp.ne', one_mul, mul_comm] using hh
  calc
    _ ≤ ∑' m : O × O, ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(g m.1*g m.2) :=
      (physical_summable W N hNp).tsum_le_tsum hpoint (hp.mul_left _)
    _ = ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(∑' m : O, g m)^2 := by
      rw [tsum_mul_left, ← hg.tsum_mul_tsum hg hp, pow_two]
    _ ≤ ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*((4*(1+Real.pi)^2)*N)^2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (sourceControl_nonneg _ _))
      exact pow_le_pow_left₀ (tsum_nonneg (fun _ => by dsimp [g]; positivity)) hmass 2
    _ = _ := by ring

abbrev DualIndex := (ℤ × ℤ) × (ℤ × ℤ)

def dualPoint (p : DualIndex) : Joint :=
  point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)

def dualRow (p : DualIndex) : Fin 2 → O :=
  ![dualFrequencyEquiv p.1, dualFrequencyEquiv p.2]

def dualCoordinates (p : DualIndex) : (Fin 2 × Fin 2) → ℤ :=
  CubicEisenstein.rowCoordinates (dualRow p)

theorem dualCoordinates_injective : Function.Injective dualCoordinates := by
  intro p q hp
  have h := CubicEisenstein.rowCoordinates_injective hp
  apply Prod.ext
  · exact dualFrequencyEquiv.injective (congrFun h 0)
  · exact dualFrequencyEquiv.injective (congrFun h 1)

@[simp] theorem dualCoordinates_zero : dualCoordinates 0 = 0 := by
  have hzero : ActualEisensteinCoordinates.coords (0 : O) = (0,0) := by
    simpa [ActualEisensteinCoordinates.eval] using ShortDraftLatticeCount.coords_eval 0 0
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [dualCoordinates, CubicEisenstein.rowCoordinates, dualRow,
      dualFrequencyEquiv, ActualEisensteinCoordinates.eval, hzero]

theorem dualCoordinates_norm_le (p : DualIndex) :
    ‖dualCoordinates p‖ ≤ 2 * ‖dualPoint p‖ := by
  have hc := CubicEisenstein.coordinates_norm_bound (dualRow p)
  have hp : ‖fun i => eisEmbedding (dualRow p i)‖ ≤ ‖dualPoint p‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have h1 := explicitDualFrequency_norm_sq 1 p.1
    have h2 := explicitDualFrequency_norm_sq 1 p.2
    norm_num only [norm_one, one_pow, div_one] at h1 h2
    have hq := norm_point_sq (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)
    fin_cases i
    · change ‖eisEmbedding (dualFrequencyEquiv p.1)‖ ≤ ‖dualPoint p‖
      dsimp only [dualPoint]
      nlinarith [sq_nonneg ‖eisEmbedding (dualFrequencyEquiv p.2)‖,
        norm_nonneg (point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)),
        norm_nonneg (eisEmbedding (dualFrequencyEquiv p.1))]
    · change ‖eisEmbedding (dualFrequencyEquiv p.2)‖ ≤ ‖dualPoint p‖
      dsimp only [dualPoint]
      nlinarith [sq_nonneg ‖eisEmbedding (dualFrequencyEquiv p.1)‖,
        norm_nonneg (point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)),
        norm_nonneg (eisEmbedding (dualFrequencyEquiv p.2))]
  exact hc.trans (mul_le_mul_of_nonneg_left hp (by norm_num))

theorem dualPoint_norm_pos (p : DualIndex) (hp : p ≠ 0) : 0 < ‖dualPoint p‖ := by
  have hc : dualCoordinates p ≠ 0 := by
    intro h
    exact hp (dualCoordinates_injective (h.trans dualCoordinates_zero.symm))
  have hh := norm_pos_iff.mpr hc
  have hb := dualCoordinates_norm_le p
  linarith

theorem dual_power_summable (k : ℝ) (hk : 4 < k) :
    Summable (fun p : {p : DualIndex // p ≠ 0} => ‖dualPoint p.val‖ ^ (-k)) := by
  have hs : Summable (fun p : {p : DualIndex // p ≠ 0} => ‖dualCoordinates p.val‖ ^ (-k)) :=
    (CubicEisenstein.summable_integer_four_rpow k hk).comp_injective
    (dualCoordinates_injective.comp (Subtype.val_injective))
  apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _) _
    (hs.mul_left ((2:ℝ)^k))
  intro p
  have hc : 0 < ‖dualCoordinates p.val‖ := norm_pos_iff.mpr (by
    intro h
    exact p.property (dualCoordinates_injective (h.trans dualCoordinates_zero.symm)))
  have h := Real.rpow_le_rpow_of_nonpos (half_pos hc)
    (by have := dualCoordinates_norm_le p.val; linarith : ‖dualCoordinates p.val‖ / 2 ≤ ‖dualPoint p.val‖)
    (by linarith : -k ≤ 0)
  calc
    _ ≤ (‖dualCoordinates p.val‖ / 2) ^ (-k) := h
    _ = (2:ℝ)^k * ‖dualCoordinates p.val‖ ^ (-k) := by
      rw [Real.div_rpow (norm_nonneg _) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      simp only [div_inv_eq_mul, mul_comm]

def scaledDualPoint (L : ℝ) (u : ℂ) (p : DualIndex) : Joint :=
  point (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)

theorem norm_scaledDualPoint (L : ℝ) (hL : 0 ≤ L) (u : ℂ) (hu : ‖u‖ = 1)
    (p : DualIndex) : ‖scaledDualPoint L u p‖ = L * ‖dualPoint p‖ := by
  have h1 := norm_point_sq (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)
  have h2 := norm_point_sq (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)
  simp only [norm_mul, hu, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL,
    one_mul] at h1
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  change ‖point (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)‖^2 =
      (L*‖point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)‖)^2
  simp only [h1, mul_pow, h2]
  ring

theorem fourier_seminorm_control (k : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(Joint, ℂ),
      SchwartzMap.seminorm ℝ k 0 (𝓕 W) ≤ C * sourceControl S W := by
  let T : 𝓢(Joint, ℂ) →L[ℝ] 𝓢(Joint, ℂ) := SchwartzMap.fourierTransformCLM ℝ
  let q : Seminorm ℝ 𝓢(Joint, ℂ) := (SchwartzMap.seminorm ℝ k 0).comp T.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℝ Joint ℂ).continuous_seminorm (k,0)).comp T.continuous
  obtain ⟨S,C,hC,hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ Joint ℂ) q hq
  refine ⟨S,C,?_,?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W
    exact Seminorm.le_def.mp hbound W

theorem scaledDual_decay (F : 𝓢(Joint, ℂ)) (k : ℕ) (L : ℝ) (hL : 0 < L)
    (u : ℂ) (hu : ‖u‖ = 1) (p : DualIndex) (hp : p ≠ 0) :
    ‖F (scaledDualPoint L u p)‖ ≤ SchwartzMap.seminorm ℝ k 0 F *
      L^(-(k:ℝ)) * ‖dualPoint p‖^(-(k:ℝ)) := by
  have hn : 0 < ‖scaledDualPoint L u p‖ := by
    rw [norm_scaledDualPoint L hL.le u hu]
    exact mul_pos hL (dualPoint_norm_pos p hp)
  have hb := SchwartzMap.norm_pow_mul_le_seminorm ℝ F k (scaledDualPoint L u p)
  have hh : ‖F (scaledDualPoint L u p)‖ ≤
      SchwartzMap.seminorm ℝ k 0 F * ‖scaledDualPoint L u p‖^(-(k:ℝ)) := by
    rw [Real.rpow_neg hn.le, Real.rpow_natCast, ← div_eq_mul_inv,
      le_div_iff₀ (pow_pos hn k)]
    simpa only [mul_comm] using hb
  rw [norm_scaledDualPoint L hL.le u hu,
    Real.mul_rpow hL.le (norm_nonneg _)] at hh
  simpa only [mul_assoc] using hh

theorem dual_fourier_summable (A : ℕ) (hA : 2 < A)
    (W : 𝓢(Joint, ℂ)) (L : ℝ) (hL : 0 < L) (u : ℂ) (hu : ‖u‖ = 1) :
    Summable (fun p : {p : DualIndex // p ≠ 0} => ‖(𝓕 W) (scaledDualPoint L u p.val)‖) := by
  have hdim : (4:ℝ) < ((2*A:ℕ):ℝ) := by exact_mod_cast (by omega : 4 < 2*A)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((dual_power_summable ((2*A:ℕ):ℝ) hdim).mul_left
      (SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ))))
  intro p
  exact scaledDual_decay (𝓕 W) (2*A) L hL u hu p.val p.property

theorem dual_fourier_lattice_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (L : ℝ), 1 ≤ L → ∀ (u : ℂ), ‖u‖ = 1 →
        (∑' p : {p : DualIndex // p ≠ 0}, ‖(𝓕 W) (scaledDualPoint L u p.val)‖) ≤
          C * sourceControl S W * L^(-((2*A:ℕ):ℝ)) := by
  obtain ⟨S,C,hC,hbound⟩ := fourier_seminorm_control (2*A)
  let mass : ℝ := ∑' p : {p : DualIndex // p ≠ 0}, ‖dualPoint p.val‖^(-((2*A:ℕ):ℝ))
  have hm : 0 ≤ mass := tsum_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨S,C*(mass+1),mul_pos hC (by positivity),?_⟩
  intro W L hL u hu
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hdim : (4:ℝ) < ((2*A:ℕ):ℝ) := by exact_mod_cast (by omega : 4 < 2*A)
  calc
    _ ≤ ∑' p : {p : DualIndex // p ≠ 0},
        (SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ))) *
          ‖dualPoint p.val‖^(-((2*A:ℕ):ℝ)) :=
      (dual_fourier_summable A hA W L hLp u hu).tsum_le_tsum
        (fun p => scaledDual_decay (𝓕 W) (2*A) L hLp u hu p.val p.property)
        ((dual_power_summable ((2*A:ℕ):ℝ) hdim).mul_left _)
    _ = SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ)) * mass := tsum_mul_left
    _ ≤ (C * sourceControl S W) * L^(-((2*A:ℕ):ℝ)) * (mass+1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (hbound W) (Real.rpow_nonneg hLp.le _)
      · linarith
      · exact hm
      · exact mul_nonneg (mul_nonneg hC.le (sourceControl_nonneg S W)) (Real.rpow_nonneg hLp.le _)
    _ = _ := by ring

theorem sourceControl_mono {S T : Finset (ℕ × ℕ)} (hST : S ⊆ T)
    (W : 𝓢(Joint, ℂ)) : sourceControl S W ≤ sourceControl T W :=
  Seminorm.le_def.mp (Finset.sup_mono hST) W

theorem joint_lattice_bounds (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      (∀ (W : 𝓢(Joint, ℂ)) (N : ℝ), 1 ≤ N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2) ∧
      (∀ (W : 𝓢(Joint, ℂ)) (L : ℝ), 1 ≤ L → ∀ (u : ℂ), ‖u‖ = 1 →
        (∑' p : {p : DualIndex // p ≠ 0}, ‖(𝓕 W) (scaledDualPoint L u p.val)‖) ≤
          C * sourceControl S W * L^(-((2*A:ℕ):ℝ))) := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩ := physical_lattice_bound
  obtain ⟨S₂,C₂,hC₂,h₂⟩ := dual_fourier_lattice_bound A hA
  refine ⟨S₁∪S₂,C₁+C₂,add_pos hC₁ hC₂,?_,?_⟩
  · intro W N hN
    apply (h₁ W N hN).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul (le_add_of_nonneg_right hC₂.le)
      (sourceControl_mono Finset.subset_union_left W) (sourceControl_nonneg _ _) (by positivity)
  · intro W L hL u hu
    apply (h₂ W L hL u hu).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    exact mul_le_mul (le_add_of_nonneg_left hC₁.le)
      (sourceControl_mono Finset.subset_union_right W) (sourceControl_nonneg _ _) (by positivity)

end ProbeGramLatticeDecay

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Detector.GramAnnularLattice
section
namespace OAI

noncomputable section
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramAnnularLattice
open ProbeGramLatticeDecay ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def AnnularSupport (a b : ℝ) (W : 𝓢(Joint, ℂ)) : Prop :=
  Function.support W ⊆ {z : Joint | a ≤ ‖z.fst‖^2 ∧ ‖z.fst‖^2 ≤ b ∧
    a ≤ ‖z.snd‖^2 ∧ ‖z.snd‖^2 ≤ b}

theorem scaled_embedding_norm_sq (m : O) (N : ℝ) (hN : 0 ≤ N) :
    ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 = ‖eisEmbedding m‖^2 / N := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hN]

theorem physical_sample_eq_zero (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (W : 𝓢(Joint, ℂ)) (hW : AnnularSupport a b W)
    (N : ℝ) (hN : 0 < N) (hsmall : N < b⁻¹) (m : O × O) :
    W (physicalPoint N m) = 0 := by
  by_contra h
  have hw := hW h
  change a ≤ ‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2 ∧
    ‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2 ≤ b ∧ _ at hw
  have hm : m.1 ≠ 0 := by
    intro hz
    have hh := hw.1
    rw [hz, map_zero, zero_div, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hh
    linarith
  have hl := one_le_eisenstein_norm_sq m.1 hm
  have hu := hw.2.1
  rw [scaled_embedding_norm_sq m.1 N hN.le, div_le_iff₀ hN] at hu
  have hs : b*N < 1 := by
    have hh := mul_lt_mul_of_pos_left hsmall hb
    simpa only [mul_inv_cancel₀ hb.ne'] using hh
  linarith

def cauchyWeight (m : O) : ℝ := ((1+‖eisEmbedding m‖^2)^2)⁻¹

theorem cauchyWeight_summable : Summable cauchyWeight := by
  change Summable (fun m : O => ((1+‖eisEmbedding m‖^2)^2)⁻¹)
  simpa only [one_mul] using scaled_eisenstein_cauchy_summable 1 zero_lt_one

theorem cauchyWeight_mass_le : (∑' m : O, cauchyWeight m) ≤ 4*(1+Real.pi)^2 := by
  simpa only [cauchyWeight, one_mul] using scaled_eisenstein_cauchy_small 1 zero_lt_one le_rfl

theorem physical_subunit_majorant (W : 𝓢(Joint, ℂ))
    (N : ℝ) (hN : 0 < N) (hN1 : N ≤ 1) (m : O × O) :
    ‖W (physicalPoint N m)‖ ≤ (2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W *
      (cauchyWeight m.1 * cauchyWeight m.2) := by
  have hn (m : O) : ‖eisEmbedding m‖^2 ≤ ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 := by
    rw [scaled_embedding_norm_sq m N hN.le, le_div_iff₀ hN]
    exact mul_le_of_le_one_right (sq_nonneg _) hN1
  have hd : (1+‖eisEmbedding m.1‖^2)^2 * (1+‖eisEmbedding m.2‖^2)^2 ≤
      (1+‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2)^2 *
        (1+‖eisEmbedding m.2 / (Real.sqrt N : ℂ)‖^2)^2 := by
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) (hn m.1)) 2)
      (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) (hn m.2)) 2) (by positivity) (by positivity)
  have hp := (mul_le_mul_of_nonneg_right hd (norm_nonneg (W (physicalPoint N m)))).trans
    (product_decay W (eisEmbedding m.1 / (Real.sqrt N : ℂ))
      (eisEmbedding m.2 / (Real.sqrt N : ℂ)))
  dsimp only [cauchyWeight]
  rw [← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using hp

theorem physical_subunit_bound (W : 𝓢(Joint, ℂ))
    (N : ℝ) (hN : 0 < N) (hN1 : N ≤ 1) :
    (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤
      ((2:ℝ)^8*(4*(1+Real.pi)^2)^2) * sourceControl (Finset.Iic (8,0)) W := by
  have hg := cauchyWeight_summable
  have hp := hg.mul_of_nonneg hg (fun _ => by unfold cauchyWeight; positivity)
    (fun _ => by unfold cauchyWeight; positivity)
  calc
    _ ≤ ∑' m : O × O, ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*
        (cauchyWeight m.1*cauchyWeight m.2) :=
      (physical_summable W N hN).tsum_le_tsum (physical_subunit_majorant W N hN hN1)
        (hp.mul_left _)
    _ = ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(∑' m : O, cauchyWeight m)^2 := by
      rw [tsum_mul_left, ← hg.tsum_mul_tsum hg hp, pow_two]
    _ ≤ ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(4*(1+Real.pi)^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (sourceControl_nonneg _ _))
      exact pow_le_pow_left₀ (tsum_nonneg (fun _ => by unfold cauchyWeight; positivity))
        cauchyWeight_mass_le 2
    _ = _ := by ring

theorem annular_lattice_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), AnnularSupport a b W → ∀ (N : ℝ), 0 < N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2 := by
  obtain ⟨S₀,C₀,hC₀,h₀⟩ := physical_lattice_bound
  let K : ℝ := (2:ℝ)^8*(4*(1+Real.pi)^2)^2
  have hK : 0 < K := by dsimp [K]; positivity
  have hb : 0 < b := ha.trans hab
  refine ⟨S₀ ∪ Finset.Iic (8,0),C₀ + K*b^2,by positivity,?_⟩
  intro W hW N hN
  have hS₀ := sourceControl_mono (S := S₀) (T := S₀ ∪ Finset.Iic (8,0)) Finset.subset_union_left W
  have hS₁ := sourceControl_mono (S := Finset.Iic (8,0))
    (T := S₀ ∪ Finset.Iic (8,0)) Finset.subset_union_right W
  by_cases hN1 : 1 ≤ N
  · apply (h₀ W N hN1).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul (le_add_of_nonneg_right (by positivity)) hS₀
      (sourceControl_nonneg _ _) (by positivity)
  · by_cases hs : N < b⁻¹
    · have hz : (∑' m : O × O, ‖W (physicalPoint N m)‖) = 0 := by
        calc
          _ = ∑' _m : O × O, (0:ℝ) := tsum_congr (fun m => by
            rw [physical_sample_eq_zero a b ha hb W hW N hN hs m, norm_zero])
          _ = 0 := tsum_zero
      rw [hz]
      exact mul_nonneg (mul_nonneg (by positivity) (sourceControl_nonneg _ _)) (sq_nonneg _)
    · have hBN : 1 ≤ b*N := by
        have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hs) hb.le
        simpa only [mul_inv_cancel₀ hb.ne'] using hh
      have hBN2 : 1 ≤ b^2*N^2 := by nlinarith [sq_nonneg (b*N-1)]
      calc
        _ ≤ K * sourceControl (Finset.Iic (8,0)) W :=
          physical_subunit_bound W N hN (le_of_not_ge hN1)
        _ ≤ K * sourceControl (S₀ ∪ Finset.Iic (8,0)) W :=
          mul_le_mul_of_nonneg_left hS₁ hK.le
        _ ≤ (K * sourceControl (S₀ ∪ Finset.Iic (8,0)) W) * (b^2*N^2) :=
          le_mul_of_one_le_right (mul_nonneg hK.le (sourceControl_nonneg _ _)) hBN2
        _ = (K*b^2) * sourceControl (S₀ ∪ Finset.Iic (8,0)) W * N^2 := by ring
        _ ≤ (C₀+K*b^2) * sourceControl (S₀ ∪ Finset.Iic (8,0)) W * N^2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀.le)
              (sourceControl_nonneg _ _)) (sq_nonneg _)

theorem weighted_summable (W : 𝓢(Joint, ℂ)) (d : O × O → ℂ) (B : ℝ)
    (hd : ∀ m, ‖d m‖ ≤ B) (N : ℝ) (hN : 0 < N) :
    Summable (fun m : O × O => d m * W (physicalPoint N m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((physical_summable W N hN).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hd m) (norm_nonneg _)

theorem annular_weighted_lattice_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), AnnularSupport a b W →
      ∀ (d : O × O → ℂ) (B : ℝ), 0 ≤ B → (∀ m, ‖d m‖ ≤ B) →
      ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O => d m * W (physicalPoint N m)) ∧
        ‖∑' m : O × O, d m * W (physicalPoint N m)‖ ≤ C * sourceControl S W * B * N^2 := by
  obtain ⟨S,C,hC,hbound⟩ := annular_lattice_bound a b ha hab
  refine ⟨S,C,hC,?_⟩
  intro W hW d B hB hd N hN
  refine ⟨weighted_summable W d B hd N hN,?_⟩
  calc
    _ ≤ ∑' m : O × O, B * ‖W (physicalPoint N m)‖ := by
      apply (norm_tsum_le_tsum_norm ((weighted_summable W d B hd N hN).norm)).trans
      apply ((weighted_summable W d B hd N hN).norm).tsum_le_tsum _
        ((physical_summable W N hN).mul_left B)
      intro m
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hd m) (norm_nonneg _)
    _ = B * ∑' m : O × O, ‖W (physicalPoint N m)‖ := tsum_mul_left
    _ ≤ B * (C * sourceControl S W * N^2) := mul_le_mul_of_nonneg_left (hbound W hW N hN) hB
    _ = _ := by ring

end ProbeGramAnnularLattice

end

end OAI

end


