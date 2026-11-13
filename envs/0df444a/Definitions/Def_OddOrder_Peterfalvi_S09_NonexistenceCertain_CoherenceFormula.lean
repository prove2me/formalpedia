-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_CoherenceFormula
-- name    : OddOrder_Peterfalvi_S09_NonexistenceCertain_CoherenceFormula
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:41:55.60854+00:00
-- url     : https://prove2.me/theorems/6fd2adb6-266e-49b3-b34d-26264a78c393
-- title:
--   Peterfalvi (7.8.b): the coherence formula, norm estimates (tail)
-- statement:
--   The final part of the Peterfalvi §7 coherence-formula development, concerning the (7.8.b) norm estimate.
--
--   The main structure is `NormEstimates`, the (7.8.b) target: under $2e+1\le h$, a norm bound for the coherent $\zeta$-image.
--
--   The bundle also proves 19 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_QuadraticTerm

namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_8

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype L]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- Arithmetic core of Peterfalvi (7.8.b): if `2e + 1 ≤ h`, then the
quadratic correction `u a² - 2 v a` is nonnegative for every integer `a`, where
`u = (1/e)(1 - 1/h)` and `v = 1/h`. -/
lemma quadraticTerm_nonneg_of_smallIndex {e h : ℝ} (a : ℤ)
    (he : 0 < e) (hsmall : 2 * e + 1 ≤ h) :
    0 ≤ (1 / e) * (1 - 1 / h) * (a : ℝ) ^ 2 - 2 * (1 / h) * (a : ℝ) := by
  have hh_pos : 0 < h := by linarith
  have he_ne : e ≠ 0 := ne_of_gt he
  have hh_ne : h ≠ 0 := ne_of_gt hh_pos
  have hsmall' : 2 * e ≤ h - 1 := by linarith
  have hu_eq : (1 / e) * (1 - 1 / h) = (h - 1) / (e * h) := by
    field_simp [he_ne, hh_ne]
  have hkey : 2 * (1 / h) ≤ (1 / e) * (1 - 1 / h) := by
    rw [hu_eq]
    rw [show 2 * (1 / h) = 2 / h by ring]
    rw [div_le_div_iff₀ hh_pos (mul_pos he hh_pos)]
    nlinarith
  have hv_nonneg : 0 ≤ 2 * (1 / h) := by
    rw [one_div]
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr hh_pos.le)
  have hu_nonneg : 0 ≤ (1 / e) * (1 - 1 / h) := le_trans hv_nonneg hkey
  by_cases ha_nonpos_int : a ≤ 0
  · have ha_nonpos : (a : ℝ) ≤ 0 := by exact_mod_cast ha_nonpos_int
    have hsq_nonneg : 0 ≤ (a : ℝ) ^ 2 := sq_nonneg _
    have hterm1 : 0 ≤ (1 / e) * (1 - 1 / h) * (a : ℝ) ^ 2 :=
      mul_nonneg hu_nonneg hsq_nonneg
    have hprod_nonpos : 2 * (1 / h) * (a : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hv_nonneg ha_nonpos
    nlinarith
  · have ha_ge_one_int : 1 ≤ a := by omega
    have ha_ge_one : (1 : ℝ) ≤ a := by exact_mod_cast ha_ge_one_int
    have ha_nonneg : 0 ≤ (a : ℝ) := by linarith
    have ha_sq_ge : (a : ℝ) ≤ (a : ℝ) ^ 2 := by nlinarith
    have hmul1 : 2 * (1 / h) * (a : ℝ) ≤
        ((1 / e) * (1 - 1 / h)) * (a : ℝ) :=
      mul_le_mul_of_nonneg_right hkey ha_nonneg
    have hmul2 : ((1 / e) * (1 - 1 / h)) * (a : ℝ) ≤
        ((1 / e) * (1 - 1 / h)) * (a : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left ha_sq_ge hu_nonneg
    nlinarith

/-- **Peterfalvi (7.8.b) target.**  Under `2e + 1 ≤ h`, the coherent
`ζ`-image satisfies `‖(ζ^ν)^ρ‖² ≥ 1 - e/h`, and the residual term from
(7.8.a) satisfies `‖Γ‖² ≤ e - 1`.

As with `BetaDecomp`, this is a standalone future-proof target rather than a
new field of `Hypothesis78`. -/
structure NormEstimates (H78 : Hypothesis78 G A L)
    (hBD : H78.BetaDecomp) : Prop where
  /-- `‖(ζ^ν)^ρ‖² ≥ 1 - e/h`. -/
  zetaNuRho_norm_sq_ge :
    H78.smallIndex →
      1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤
        H78.zetaNuRhoNormSq
  /-- `‖Γ‖² ≤ e - 1`. -/
  gamma_norm_sq_le :
    H78.smallIndex → H78.gammaNormSq hBD ≤ (H78.complementIndex : ℝ) - 1

/-- Under `2e + 1 ≤ h`, Peterfalvi's quadratic correction is nonnegative. -/
theorem normQuadraticCorrection_nonneg_of_smallIndex
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    H78.smallIndex → 0 ≤ H78.normQuadraticCorrection hBD := by
  intro hsmall
  rw [normQuadraticCorrection]
  have he : 0 < (H78.complementIndex : ℝ) := by
    exact_mod_cast H78.complementIndex_pos
  exact quadraticTerm_nonneg_of_smallIndex hBD.a he (H78.smallIndex_real hsmall)

/-- If `(ζ^ν)^ρ` has Peterfalvi's quadratic norm formula, its lower bound follows. -/
theorem zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzeta : H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD +
        (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ))) :
    H78.smallIndex →
      1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤
        H78.zetaNuRhoNormSq := by
  intro hsmall
  rw [hzeta]
  exact le_add_of_nonneg_left (H78.normQuadraticCorrection_nonneg_of_smallIndex hBD hsmall)

/-- The distinguished `νζ` is orthogonal to `1_G`, in the displayed direction. -/
theorem zetaImage_orth_one (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
      (Hypothesis71.constOne G) = 0 :=
  hBD.orth_one H78.zetaDistinct H78.zetaDistinct_ne_ind1H

/-- Hermitian-symmetric form of `zetaImage_orth_one`. -/
theorem constOne_orth_zetaImage (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (Hypothesis71.constOne G)
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.zetaImage_orth_one hBD, star_zero]

/-- The residual `Γ` is orthogonal to the distinguished `νζ`, in the displayed direction. -/
theorem gamma_orth_zetaImage (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner hBD.Gamma (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 0 :=
  hBD.Gamma_orth_nu H78.zetaDistinct H78.zetaDistinct_ne_ind1H

/-- Hermitian-symmetric form of `gamma_orth_zetaImage`. -/
theorem zetaImage_orth_gamma (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) hBD.Gamma = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.gamma_orth_zetaImage hBD, star_zero]

/-- Hermitian-symmetric form of `BetaDecomp.Gamma_orth_one`. -/
theorem constOne_orth_gamma (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (Hypothesis71.constOne G) hBD.Gamma = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, hBD.Gamma_orth_one, star_zero]

/-- Each coherent image in `S^ν` is orthogonal to `Γ`, in the opposite direction. -/
theorem nu_orth_gamma (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (i : Fin (H78.hyp76.n + 1)) (hi : i ≠ H78.ind1H) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta i)) hBD.Gamma = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, hBD.Gamma_orth_nu i hi, star_zero]

/-- The weighted `S^ν`-sum is orthogonal to `1_G`. -/
theorem weightedNuSum_orth_one (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner H78.weightedNuSum (Hypothesis71.constOne G) = 0 := by
  classical
  rw [weightedNuSum, inner_sum_left]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi_ne : i ≠ H78.ind1H := (Finset.mem_erase.mp hi).1
  rw [ClassFunction.inner_smul_left, hBD.orth_one i hi_ne, mul_zero]

/-- Hermitian-symmetric form of `weightedNuSum_orth_one`. -/
theorem constOne_orth_weightedNuSum
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner (Hypothesis71.constOne G) H78.weightedNuSum = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.weightedNuSum_orth_one hBD, star_zero]

/-- The weighted `S^ν`-sum is orthogonal to the residual `Γ`. -/
theorem weightedNuSum_orth_gamma
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner H78.weightedNuSum hBD.Gamma = 0 := by
  classical
  rw [weightedNuSum, inner_sum_left]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi_ne : i ≠ H78.ind1H := (Finset.mem_erase.mp hi).1
  rw [ClassFunction.inner_smul_left, H78.nu_orth_gamma hBD i hi_ne, mul_zero]

/-- Hermitian-symmetric form of `weightedNuSum_orth_gamma`. -/
theorem gamma_orth_weightedNuSum
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner hBD.Gamma H78.weightedNuSum = 0 := by
  rw [Hypothesis71.ClassFunction.inner_symm, H78.weightedNuSum_orth_gamma hBD, star_zero]

/-- Orthogonal expansion of the beta decomposition in Peterfalvi (7.8.a).

After the remaining source-side computation of `‖Σ‖² = (h - 1)/e`, the displayed
decomposition of `β` gives the real norm formula used in (7.8.b). -/
theorem betaNormSq_eq_of_weightedNuSum_norm
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzeta_norm :
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1)
    (hweighted_zeta :
      ClassFunction.inner H78.weightedNuSum
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1)
    (hweighted_norm :
      ClassFunction.inner H78.weightedNuSum H78.weightedNuSum =
        ((((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) : ℂ)) :
    H78.betaNormSq =
      2 +
        (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) *
          (hBD.a : ℝ) ^ 2 -
        2 * (hBD.a : ℝ) + H78.gammaNormSq hBD := by
  have hzeta_weighted :
      ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        H78.weightedNuSum = 1 := by
    rw [Hypothesis71.ClassFunction.inner_symm, hweighted_zeta, star_one]
  have hinner :
      ClassFunction.inner H78.beta H78.beta =
        2 +
          (hBD.a : ℂ) * (hBD.a : ℂ) *
            ((((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) : ℂ) -
          2 * (hBD.a : ℂ) +
          ClassFunction.inner hBD.Gamma hBD.Gamma := by
    rw [hBD.beta_eq]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      Hypothesis71.constOne_inner_self_eq_one, H78.zetaImage_orth_one hBD,
      H78.constOne_orth_zetaImage hBD, H78.weightedNuSum_orth_one hBD,
      H78.constOne_orth_weightedNuSum hBD, hBD.Gamma_orth_one,
      H78.constOne_orth_gamma hBD, H78.gamma_orth_zetaImage hBD,
      H78.zetaImage_orth_gamma hBD, H78.weightedNuSum_orth_gamma hBD,
      H78.gamma_orth_weightedNuSum hBD, hzeta_norm, hweighted_zeta, hzeta_weighted,
      hweighted_norm, star_intCast, mul_zero, add_zero, sub_zero, zero_add]
    ring
  rw [betaNormSq, hinner, gammaNormSq]
  norm_num [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub]
  ring

/-- Any indexed coherent image `νζᵢ` has norm one once the source `ζᵢ` does. -/
theorem nu_zeta_inner_self_eq_one (H78 : Hypothesis78 G A L)
    {i : Fin (H78.hyp76.n + 1)} (hi : i ≠ H78.ind1H)
    (hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) = 1) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta i))
        (H78.nu (H78.hyp76.zeta i)) = 1 := by
  rw [H78.nu_isometry i i hi hi, hzeta_norm]

/-- The distinguished image `νζ` has norm one once the source `ζ` has norm one. -/
theorem zetaImage_inner_self_eq_one (H78 : Hypothesis78 G A L)
    (hzeta_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1) :
    ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 :=
  H78.nu_zeta_inner_self_eq_one H78.zetaDistinct_ne_ind1H hzeta_norm

/-- If the source `ζ_i` are orthogonal to the distinguished `ζ`, the weighted
`S^ν`-sum has inner product `1` with `νζ`.

This is the coefficient computation in Peterfalvi (7.8.a) that feeds the
`(β, ζ^ν) = a - 1` identity used in (7.8.b). -/
theorem weightedNuSum_inner_zetaImage_eq_one (H78 : Hypothesis78 G A L)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta H78.zetaDistinct) =
        if i = H78.zetaDistinct then (1 : ℂ) else 0)
    (hzeta_one_ne_zero : H78.hyp76.zeta H78.zetaDistinct (1 : L) ≠ 0) :
    ClassFunction.inner H78.weightedNuSum
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 := by
  classical
  set s : Finset (Fin (H78.hyp76.n + 1)) := Finset.univ.erase H78.ind1H with hs
  have hzeta_mem : H78.zetaDistinct ∈ s := by
    simp [hs, H78.zetaDistinct_ne_ind1H]
  rw [weightedNuSum, ← hs, inner_sum_left]
  have hsum :
      (∑ i ∈ s,
        ClassFunction.inner
          ((H78.hyp76.zeta i (1 : L) /
            (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
              ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))) •
            H78.nu (H78.hyp76.zeta i))
          (H78.nu (H78.hyp76.zeta H78.zetaDistinct))) =
        ∑ i ∈ s,
          if i = H78.zetaDistinct then
            H78.hyp76.zeta i (1 : L) /
              (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
                ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))
          else 0 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ClassFunction.inner_smul_left,
      H78.nu_isometry i H78.zetaDistinct (Finset.ne_of_mem_erase (hs ▸ hi))
        H78.zetaDistinct_ne_ind1H, horth i hi]
    by_cases hiz : i = H78.zetaDistinct
    · rw [if_pos hiz, if_pos hiz, mul_one]
    · rw [if_neg hiz, if_neg hiz, mul_zero]
  rw [hsum, Finset.sum_ite_eq' s H78.zetaDistinct
    (fun i =>
      H78.hyp76.zeta i (1 : L) /
        (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))),
    if_pos hzeta_mem, horth H78.zetaDistinct hzeta_mem]
  rw [if_pos rfl]
  field_simp [hzeta_one_ne_zero]

/-- Source orthogonality and the Burnside degree sum evaluate the norm of the
weighted `S^ν`-sum in Peterfalvi (7.8.a).

This is the source-side computation of `‖Σ‖² = (h - 1) / e`: after `ν` transports
orthogonality from `L` to `G`, only diagonal terms remain, and the degree sum
collapses to the non-principal part of the kernel. -/
theorem weightedNuSum_inner_self_eq_of_source_orthogonal
    (H78 : Hypothesis78 G A L)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ)) :
    ClassFunction.inner H78.weightedNuSum H78.weightedNuSum =
      ((((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) : ℂ) := by
  classical
  set s : Finset (Fin (H78.hyp76.n + 1)) := Finset.univ.erase H78.ind1H with hs
  let coeff : Fin (H78.hyp76.n + 1) → ℂ := fun i =>
    H78.hyp76.zeta i (1 : L) /
      (H78.hyp76.zeta H78.zetaDistinct (1 : L) *
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))
  have he_ne : (H78.complementIndex : ℂ) ≠ 0 := by
    exact_mod_cast H78.complementIndex_pos.ne'
  have hinner :
      ClassFunction.inner H78.weightedNuSum H78.weightedNuSum =
        ∑ i ∈ s, ∑ j ∈ s,
          coeff i * star (coeff j) *
            ClassFunction.inner (H78.nu (H78.hyp76.zeta i))
              (H78.nu (H78.hyp76.zeta j)) := by
    rw [weightedNuSum, ← hs]
    change ClassFunction.inner
        (∑ i ∈ s, coeff i • H78.nu (H78.hyp76.zeta i))
        (∑ i ∈ s, coeff i • H78.nu (H78.hyp76.zeta i)) = _
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right]
    ring
  have hcollapse :
      (∑ i ∈ s, ∑ j ∈ s,
        coeff i * star (coeff j) *
          ClassFunction.inner (H78.nu (H78.hyp76.zeta i))
            (H78.nu (H78.hyp76.zeta j))) =
        ∑ i ∈ s,
          coeff i * star (coeff i) *
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hine : i ≠ H78.ind1H := Finset.ne_of_mem_erase (hs ▸ hi)
    rw [Finset.sum_eq_single i]
    · rw [H78.nu_isometry i i hine hine,
        horth i (by simpa [hs] using hi) i (by simpa [hs] using hi), if_pos rfl]
    · intro j hj hji
      rw [H78.nu_isometry i j hine (Finset.ne_of_mem_erase (hs ▸ hj)),
        horth i (by simpa [hs] using hi) j (by simpa [hs] using hj),
        if_neg (Ne.symm hji), mul_zero]
    · intro hnot
      exact False.elim (hnot hi)
  have hdiag :
      (∑ i ∈ s,
        coeff i * star (coeff i) *
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        (∑ i ∈ s,
          H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) /
          (H78.complementIndex : ℂ) ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hn_star :
        star (ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) :=
      Hypothesis71.ClassFunction.star_inner_self _
    have hn_ne : ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0 :=
      hnorm_ne i (by simpa [hs] using hi)
    simp only [coeff, hzeta_degree]
    rw [star_div₀, star_mul', hn_star]
    simp only [star_natCast]
    field_simp [he_ne, hn_ne]
  rw [hinner, hcollapse, hdiag, show
      (∑ i ∈ s,
          H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ) from by
        simpa [hs] using hdegree_sum]
  field_simp [he_ne]
  norm_num [Complex.ofReal_div, Complex.ofReal_sub]
  ring

/-- Source orthogonality and the kernel degree sum give the full orthogonal
expansion of `‖β‖²` in Peterfalvi (7.8.b). -/
theorem betaNormSq_eq_of_source_orthogonal
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (horth : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)
          else 0)
    (hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0)
    (hzeta_degree : H78.hyp76.zeta H78.zetaDistinct (1 : L) =
      (H78.complementIndex : ℂ))
    (hdegree_sum :
      (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ))
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.betaNormSq =
      2 +
        (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) *
          (hBD.a : ℝ) ^ 2 -
        2 * (hBD.a : ℝ) + H78.gammaNormSq hBD := by
  classical
  set s : Finset (Fin (H78.hyp76.n + 1)) := Finset.univ.erase H78.ind1H with hs
  have hzeta_mem : H78.zetaDistinct ∈ s := by
    simp [hs, H78.zetaDistinct_ne_ind1H]
  have hzeta_src_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.zetaDistinct) = 1 :=
    H78.zetaDistinct_inner_self_eq_one_of_irreducible hzeta_irr
  have horth_zeta : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta H78.zetaDistinct) =
        if i = H78.zetaDistinct then (1 : ℂ) else 0 := by
    intro i hi
    have hi_s : i ∈ s := by simpa [hs] using hi
    rw [horth i hi H78.zetaDistinct (by simpa [hs] using hzeta_mem)]
    by_cases hiz : i = H78.zetaDistinct
    · rw [if_pos hiz, if_pos hiz, hiz, hzeta_src_norm]
    · rw [if_neg hiz, if_neg hiz]
  have hzeta_one_ne_zero : H78.hyp76.zeta H78.zetaDistinct (1 : L) ≠ 0 := by
    rw [hzeta_degree]
    exact_mod_cast H78.complementIndex_pos.ne'
  exact H78.betaNormSq_eq_of_weightedNuSum_norm hBD
    (H78.zetaImage_inner_self_eq_one hzeta_src_norm)
    (H78.weightedNuSum_inner_zetaImage_eq_one horth_zeta hzeta_one_ne_zero)
    (H78.weightedNuSum_inner_self_eq_of_source_orthogonal
      horth hnorm_ne hzeta_degree hdegree_sum)

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09


