-- Prove2me | Definitions.Def_OAIQ091C003
-- name    : OAIQ091C003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T16:47:15.294335+00:00
-- url     : https://prove2.me/theorems/3d5e3b07-b07a-4544-a683-e055f0d82f55
-- title:
--   Definitions bundle OAIQ091C003 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 216 declarations of OpenAI's Lean: 57 definitions, 2 inductive types or structures and 157 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.complexAffineRadius`, `OAI.PositiveEinsteinFour.Geometry.complexInverseDistortion`, `OAI.PositiveEinsteinFour.Geometry.complexRadialDensity`, `OAI.PositiveEinsteinFour.Geometry.complexRadialMass`, `OAI.PositiveEinsteinFour.Geometry.fourIndicesEquiv`, `OAI.PositiveEinsteinFour.Geometry.h2SchwartzInverse`, `OAI.PositiveEinsteinFour.Geometry.hessianIntegral`, `OAI.PositiveEinsteinFour.Geometry.hodgeRangePair`, `OAI.PositiveEinsteinFour.Geometry.positivePowerExtension`, `OAI.PositiveEinsteinFour.Geometry.positivePowerInner`, `OAI.PositiveEinsteinFour.Geometry.positivePowerOuter`, `OAI.PositiveEinsteinFour.Geometry.roundNorth`, `OAI.PositiveEinsteinFour.Geometry.roundRadialMass`, `OAI.PositiveEinsteinFour.Geometry.scalarCompositionHessian`, `OAI.PositiveEinsteinFour.Geometry.scalarCompositionL2Multiply`, `OAI.PositiveEinsteinFour.Geometry.scalarKatoSquareRate`, `OAI.PositiveEinsteinFour.Geometry.scalarKatoTail`, `OAI.PositiveEinsteinFour.Geometry.scalarKatoTest`, `OAI.PositiveEinsteinFour.Geometry.scalarKatoTestRate`, `OAI.PositiveEinsteinFour.Geometry.scalarL2BoundedMultiplier`, `OAI.PositiveEinsteinFour.Geometry.scalarL4Product`, `OAI.PositiveEinsteinFour.Geometry.scalarNegativeTest`, `OAI.PositiveEinsteinFour.Geometry.scalarNonlinearTruncation`, `OAI.PositiveEinsteinFour.Geometry.scalarNonlinearTruncationDerivative`, `OAI.PositiveEinsteinFour.Geometry.weylGapEpsilon`, `OAI.PositiveEinsteinFour.HighestHessian.Equations`, `OAI.PositiveEinsteinFour.HighestHessian.collectedHessianForm`, `OAI.PositiveEinsteinFour.HighestHessian.freeCoordinates`, `OAI.PositiveEinsteinFour.HighestHessian.minusCoordinates`, `OAI.PositiveEinsteinFour.HighestHessian.rightQuaternion`, `OAI.PositiveEinsteinFour.Jacobi.complexJacobiFast`, `OAI.PositiveEinsteinFour.Jacobi.complexJacobiSlow`, `OAI.PositiveEinsteinFour.Jacobi.flatGreen`, `OAI.PositiveEinsteinFour.Jacobi.flatGreenValue`, `OAI.PositiveEinsteinFour.Jacobi.interiorMean`, `OAI.PositiveEinsteinFour.Jacobi.loss`, `OAI.PositiveEinsteinFour.Jacobi.lossFactor`, `OAI.PositiveEinsteinFour.Jacobi.radialLower`, `OAI.PositiveEinsteinFour.Jacobi.scaledFlatGreen`, `OAI.PositiveEinsteinFour.Jacobi.sineCotPolynomial` and 19 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `EinsteinFour_Algebra`, `EinsteinFour_BoundedAngularMeanValue`, `EinsteinFour_CurvatureForm`, `EinsteinFour_CurvatureTensors02`, `EinsteinFour_DeterminantCompression`, `EinsteinFour_FiniteExceptionalMeanValue`, `EinsteinFour_FiniteHodgeMultiplicity`, `EinsteinFour_FiniteHodgeTraceCancellation`, `EinsteinFour_FlatDirichletGreen`, `EinsteinFour_FlatDirichletGreenTrace`, `EinsteinFour_GeodesicGeometry04`, `EinsteinFour_GeodesicGeometry06`, `EinsteinFour_GeodesicGeometry12`, `EinsteinFour_GeodesicGeometry13`, `EinsteinFour_GeodesicGeometry14`, `EinsteinFour_HeatKernels10`, `EinsteinFour_HessianAssembly`, `EinsteinFour_HighestCoordinates`, `EinsteinFour_HighestLinear`, `EinsteinFour_HighestMinusCoordinates`, `EinsteinFour_HodgeTheory11`, `EinsteinFour_Jacobi`, `EinsteinFour_JacobiApproximation`, `EinsteinFour_JacobiDeterminant`, `EinsteinFour_LocalIncrementMeanValue`, `EinsteinFour_MetricDoubleCover`, `EinsteinFour_ModeAverageLimit`, `EinsteinFour_OrthogonalCompression`, `EinsteinFour_RadialCoefficient`, `EinsteinFour_RadialIntegrals`, `EinsteinFour_ScalarCompactExtremal`, `EinsteinFour_ScalarCompositionHessian`, `EinsteinFour_ScalarDirichlet`, `EinsteinFour_ScalarH1CompositionL2`, `EinsteinFour_ScalarIntegrableSeries`, `EinsteinFour_ScalarL2BoundedMultiplier`, `EinsteinFour_ScalarL2ClosedDomination`, `EinsteinFour_ScalarL4ProductConvergence`, `EinsteinFour_ScalarLocalL2Source`, `EinsteinFour_ScalarLpNormVariation`, `EinsteinFour_ScalarLpRelativeVariation`, `EinsteinFour_ScalarLpVariation`, `EinsteinFour_ScalarMinimizingSequence`, `EinsteinFour_ScalarNormalizer`, `EinsteinFour_ScalarRegularity06`, `EinsteinFour_ScalarRegularity07`, `EinsteinFour_SineEstimates`, `EinsteinFour_SineLogPolynomial`, `EinsteinFour_VolumeAssembly`, `EinsteinFour_VolumeConstants`, `EinsteinFour_WeylEstimates00`, `EinsteinFour_WeylEstimates01`, `EinsteinFour_WeylEstimates03`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C011` and `OAIQ091C012`; the statements `OAI_PositiveEinsteinFour_Energy_remove_energy_defects_from_spectral_bounds` and `OAI_PositiveEinsteinFour_QuarticEnergy_quartic_energy_bound_gradient`; the proof of `OAI_PositiveEinsteinFour_QuarticEnergy_quartic_energy_bound_gradient`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Algebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Algebraic final steps for positively curved Einstein four-manifolds

These are the linear-algebra and characteristic-number deductions used in
Sections 1 and 8 of *Positively curved Einstein four-manifolds* (2026).
The geometric hypotheses needed to apply them are kept explicit.
-/

namespace PositiveEinsteinFour

/-- The normalized eigenvalues of a trace-free symmetric three-by-three
matrix have the parameter range and cubic invariant used in Section 2.
Here `-r` is the least eigenvalue and the squared Hilbert--Schmidt norm is six.
This elementary form needs neither eigenvector choices nor a square root. -/
theorem normalized_eigenvalue_parameter
    (r s t : ℝ)
    (htrace : -r + s + t = 0)
    (hnorm : r ^ 2 + s ^ 2 + t ^ 2 = 6)
    (hs : -r ≤ s) (ht : -r ≤ t) :
    1 ≤ r ∧ r ≤ 2 ∧ s * t = r ^ 2 - 3 ∧
      ((-r) ^ 3 + s ^ 3 + t ^ 3) / 6 = (3 * r - r ^ 3) / 2 := by
  have ht_eq : t = r - s := by linarith
  subst t
  have hr_nonneg : 0 ≤ r := by linarith
  have hproduct : s * (r - s) = r ^ 2 - 3 := by nlinarith
  have hr_lower : 1 ≤ r := by
    have hpositive_product : 0 ≤ (s + r) * (r - s + r) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hr_upper : r ≤ 2 := by
    nlinarith [sq_nonneg (s - (r - s))]
  refine ⟨hr_lower, hr_upper, hproduct, ?_⟩
  have hcube : (-r) ^ 3 + s ^ 3 + (r - s) ^ 3 = -3 * r * (s * (r - s)) := by
    ring
  rw [hcube, hproduct]
  ring

end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FiniteExceptionalMeanValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous scalar curve with finitely many exceptional parameters
still obeys the ordinary mean value bound. -/
namespace PositiveEinsteinFour.Geometry
open Set

theorem image_sub_le_mul_sub_of_deriv_le_off_finite (E : Finset ℝ)
    {f : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ E → DifferentiableAt ℝ f x)
    (hb : ∀ x ∈ Ioo a b, x ∉ E → deriv f x ≤ C) :
    f b - f a ≤ C * (b - a) := by
  classical
  induction E using Finset.induction_on generalizing a b with
  | empty =>
    apply (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hf
      (fun x hx => (hd x (by simpa only [interior_Icc] using hx) (by simp)).differentiableWithinAt)
      (fun x hx => hb x (by simpa only [interior_Icc] using hx) (by simp))
      a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  | @insert t E ht ih =>
    by_cases hti : t ∈ Ioo a b
    · have hleft : f t - f a ≤ C * (t - a) := by
        apply ih hti.1.le (hf.mono (Icc_subset_Icc_right hti.2.le))
        · intro x hx hxE
          exact hd x ⟨hx.1, hx.2.trans hti.2⟩
            (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt hx.2, hxE⟩)
        · intro x hx hxE
          exact hb x ⟨hx.1, hx.2.trans hti.2⟩
            (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt hx.2, hxE⟩)
      have hright : f b - f t ≤ C * (b - t) := by
        apply ih hti.2.le (hf.mono (Icc_subset_Icc_left hti.1.le))
        · intro x hx hxE
          exact hd x ⟨hti.1.trans hx.1, hx.2⟩
            (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt hx.1, hxE⟩)
        · intro x hx hxE
          exact hb x ⟨hti.1.trans hx.1, hx.2⟩
            (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt hx.1, hxE⟩)
      linarith
    · apply ih hab hf
      · intro x hx hxE
        apply hd x hx
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => hti (h ▸ hx), hxE⟩
      · intro x hx hxE
        apply hb x hx
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => hti (h ▸ hx), hxE⟩

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_BoundedAngularMeanValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular distance starting at zero needs a derivative bound only between its extreme values. -/
namespace PositiveEinsteinFour.Geometry
open Set

theorem bounded_angle_le_of_deriv_le (f : ℝ → ℝ) (a b B C : ℝ) (E : Finset ℝ)
    (hab : a ≤ b) (hC : 0 ≤ C) (hf : ContinuousOn f (Icc a b)) (hfa : f a = 0)
    (hpos : ∀ t ∈ Icc a b, 0 ≤ f t) (hB : f b ≤ B)
    (hd : ∀ t ∈ Ioo a b, t ∉ E → 0 < f t → f t < B → DifferentiableAt ℝ f t)
    (hb : ∀ t ∈ Ioo a b, t ∉ E → 0 < f t → f t < B → deriv f t ≤ C) :
    f b ≤ C*(b-a) := by
  by_contra h
  have hstrict : C*(b-a) < f b := lt_of_not_ge h
  obtain ⟨y,hylo,hyhi⟩ := exists_between hstrict
  have hy0 : 0 < y := lt_of_le_of_lt (mul_nonneg hC (sub_nonneg.mpr hab)) hylo
  have hyB : y < B := hyhi.trans_le hB
  obtain ⟨t,ht,hty⟩ := intermediate_value_Icc hab hf ⟨by rw [hfa]; exact hy0.le,hyhi.le⟩
  let L : Set ℝ := Icc a b ∩ f ⁻¹' {y}
  have hLclosed : IsClosed L := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hLcompact : IsCompact L := isCompact_Icc.of_isClosed_subset hLclosed inter_subset_left
  obtain ⟨z,hz,hmin⟩ := hLcompact.exists_isMinOn ⟨t,ht,hty⟩ continuousOn_id
  have haz : a ≤ z := hz.1.1
  have hzb : z ≤ b := hz.1.2
  have hfz : f z = y := hz.2
  have hclosed : IsClosed (Icc a z ∩ f ⁻¹' {0}) :=
    (hf.mono (Icc_subset_Icc_right hzb)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact (Icc a z ∩ f ⁻¹' {0}) :=
    isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  obtain ⟨x,hx,hmax⟩ := hcompact.exists_isMaxOn ⟨a,⟨le_rfl,haz⟩,hfa⟩ continuousOn_id
  have hax : a ≤ x := hx.1.1
  have hxz : x ≤ z := hx.1.2
  have hfx : f x = 0 := hx.2
  have hreg (r : ℝ) (hr : r ∈ Ioo x z) : r ∈ Ioo a b ∧ 0 < f r ∧ f r < B := by
    have hra : a < r := hax.trans_lt hr.1
    have hrb : r < b := hr.2.trans_le hzb
    have hfr : 0 < f r := by
      apply lt_of_le_of_ne (hpos r ⟨hra.le,hrb.le⟩)
      intro heq
      have hh : r ≤ x := hmax ⟨⟨hra.le,hr.2.le⟩,heq.symm⟩
      exact (not_le_of_gt hr.1) hh
    have hfry : f r < y := by
      by_contra hn
      obtain ⟨k,hk,hky⟩ := intermediate_value_Icc hra.le
        (hf.mono (Icc_subset_Icc_right hrb.le)) ⟨by rw [hfa]; exact hy0.le,le_of_not_gt hn⟩
      have hzk : z ≤ k := hmin ⟨⟨hk.1,hk.2.trans hrb.le⟩,hky⟩
      exact (not_le_of_gt hr.2) (hzk.trans hk.2)
    exact ⟨⟨hra,hrb⟩,hfr,hfry.trans hyB⟩
  have hbound := image_sub_le_mul_sub_of_deriv_le_off_finite E hxz
    (hf.mono (Icc_subset_Icc hax hzb))
    (fun r hr he => hd r (hreg r hr).1 he (hreg r hr).2.1 (hreg r hr).2.2)
    (fun r hr he => hb r (hreg r hr).1 he (hreg r hr).2.1 (hreg r hr).2.2)
  rw [hfz,hfx,sub_zero] at hbound
  have hlength : C*(z-x) ≤ C*(b-a) := mul_le_mul_of_nonneg_left (by linarith) hC
  exact (not_le_of_gt hylo) (hbound.trans hlength)

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarDirichlet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive first mode of the scalar Dirichlet comparison matrix. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

theorem weighted_row_sum {I : Type*} [Fintype I]
    (L : Matrix I I ℝ) (w y : I → ℝ) (lam : ℝ)
    (heigen : L *ᵥ w = lam • w) :
    (∑ i, ∑ j, L i j * w i * w j * y i ^ 2) =
      lam * ∑ i, w i ^ 2 * y i ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : ∑ j, L i j * w j = lam * w i := by
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun heigen i
  calc
    _ = (w i * y i ^ 2) * ∑ j, L i j * w j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hi]; ring

/-- The scalar ground-state identity. It keeps the off-diagonal entries
explicit, so its sign applies directly to the tridiagonal reference. -/
theorem scalar_ground_state_identity {I : Type*} [Fintype I]
    (L : Matrix I I ℝ) (w y : I → ℝ) (lam : ℝ)
    (hsymm : L.IsHermitian) (heigen : L *ᵥ w = lam • w) :
    (∑ i, ∑ j, (-L i j * w i * w j) * (y i - y j) ^ 2) =
      2 * ((fun i => w i * y i) ⬝ᵥ (L *ᵥ fun i => w i * y i) -
        lam * ∑ i, w i ^ 2 * y i ^ 2) := by
  have hrow := weighted_row_sum L w y lam heigen
  have hcol : (∑ i, ∑ j, L i j * w i * w j * y j ^ 2) =
      lam * ∑ i, w i ^ 2 * y i ^ 2 := by
    rw [← hrow, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hs : L j i = L i j := congrFun (congrFun hsymm.eq i) j
    rw [hs]
    ring
  have hcross : (∑ i, ∑ j, L i j * w i * w j * y i * y j) =
      (fun i => w i * y i) ⬝ᵥ (L *ᵥ fun i => w i * y i) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    _ = -(∑ i, ∑ j, L i j * w i * w j * y i ^ 2) -
        (∑ i, ∑ j, L i j * w i * w j * y j ^ 2) +
        2 * (∑ i, ∑ j, L i j * w i * w j * y i * y j) := by
      simp only [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hrow, hcol, hcross]; ring

/-- A positive first eigenvector with positive eigenvalue proves positivity
of a symmetric scalar matrix with nonpositive off-diagonal entries. -/
theorem scalar_posDef_of_positive_mode {I : Type*} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℝ) (w : I → ℝ) (lam : ℝ)
    (hsymm : L.IsHermitian) (hoff : ∀ i j, i ≠ j → L i j ≤ 0)
    (hw : ∀ i, 0 < w i) (hlam : 0 < lam) (heigen : L *ᵥ w = lam • w) :
    L.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsymm
  intro x hx
  let y := fun i => x i / w i
  have hwy : (fun i => w i * y i) = x := by
    funext i
    exact mul_div_cancel₀ (x i) (hw i).ne'
  have hsum : (∑ i, w i ^ 2 * y i ^ 2) = ∑ i, x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [y]
    field_simp [(hw i).ne']
  have hnonneg : 0 ≤ ∑ i, ∑ j, (-L i j * w i * w j) * (y i - y j) ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hij : i = j
    · simp [hij]
    · exact mul_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr (hoff i j hij))
        (hw i).le) (hw j).le) (sq_nonneg _)
  have hid := scalar_ground_state_identity L w y lam hsymm heigen
  rw [hwy, hsum] at hid
  have hnorm : 0 < ∑ i, x i ^ 2 := by
    have hex : ∃ i, x i ≠ 0 := by
      by_contra! h
      exact hx (funext h)
    obtain ⟨i, hi⟩ := hex
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hp := mul_pos hlam hnorm
  simpa only [star_trivial] using (show 0 < x ⬝ᵥ (L *ᵥ x) by linarith)

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarNormalizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive scalar normalizer used in finite radial compression. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix
open scoped MatrixOrder

noncomputable section

theorem positive_square_root_eigenvector {N : ℕ}
    {G : Matrix (Fin N) (Fin N) ℝ} {w : Fin N → ℝ} {c : ℝ}
    (hG : G.PosSemidef) (hc : 0 < c)
    (heigen : (G * G) *ᵥ w = c ^ 2 • w) :
    G *ᵥ w = c • w := by
  have hK : (G + c • (1 : Matrix (Fin N) (Fin N) ℝ)).PosDef :=
    Matrix.PosDef.posSemidef_add hG (Matrix.PosDef.one.smul hc)
  let z := G *ᵥ w - c • w
  have hz : (G + c • (1 : Matrix (Fin N) (Fin N) ℝ)) *ᵥ z = 0 := by
    dsimp [z]
    simp only [Matrix.add_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [Matrix.mulVec_mulVec, heigen]
    module
  have hz0 : z = 0 := (Matrix.mulVec_injective_of_isUnit hK.isUnit)
    (by simpa only [Matrix.mulVec_zero] using hz)
  exact sub_eq_zero.mp hz0

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coordinate curvature is a four-linear form. This supplies
the multilinearity used to change normal frames without an independent
curvature-transformation assumption. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def fourIndicesEquiv : (Fin 4 → Fin 4) ≃ Fin 4 × (Fin 4 × (Fin 4 × Fin 4)) where
  toFun a := (a 0, a 1, a 2, a 3)
  invFun a := ![a.1, a.2.1, a.2.2.1, a.2.2.2]
  left_inv a := by funext i; fin_cases i <;> rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl

theorem sum_four_indices_p0 (F : (Fin 4 → Fin 4) → ℝ) :
    (∑ a, F a) = ∑ a, ∑ b, ∑ c, ∑ d, F ![a, b, c, d] := by
  calc
    _ = ∑ a : Fin 4 × (Fin 4 × (Fin 4 × Fin 4)), F (fourIndicesEquiv.symm a) :=
      (fourIndicesEquiv.symm.sum_comp F).symm
    _ = _ := by simp only [Fintype.sum_prod_type]; rfl

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The finite matrix certificates for the quadratic coupling estimate. -/

namespace PositiveEinsteinFour.Quadratic

noncomputable section

def kappaV (v b : ℝ) : ℝ :=
  (-41) * v ^ 3 +
    (237 / 4) * v ^ 2 * b +
    (879 / 4) * v ^ 2 +
    (101 / 2) * v * b ^ 2 +
    (-128) * v * b +
    (-379) * v +
    (23 / 2) * b ^ 3 +
    (-319 / 4) * b ^ 2 +
    (3461 / 36) * b +
    (2957 / 18)

def kappaB (v b : ℝ) : ℝ :=
  (79 / 4) * v ^ 3 +
    (101 / 2) * v ^ 2 * b +
    (-64) * v ^ 2 +
    (69 / 2) * v * b ^ 2 +
    (-319 / 2) * v * b +
    (3461 / 36) * v +
    61 * b ^ 3 +
    (-1059 / 4) * b ^ 2 +
    364 * b +
    (-4007 / 36)

end

end PositiveEinsteinFour.Quadratic
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The undetermined Hessian in concrete quaternion coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators


def freeCoordinates (c : Fin 50 → ℝ) : Fin 21 → ℝ :=
  ![c 21, c 24, c 26, c 29, c 31, c 34, c 35, c 36, c 37, c 38, c 39, c 40, c 41, c 42, c 43, c 44, c 45, c 46, c 47, c 48, c 49]


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact linear equations and their elementary eliminations. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators

/-- These are precisely the independent scalar trace and Bianchi equations. -/
structure Equations (c : Fin 50 → ℝ) : Prop where
  eq0 : c 0 + c 20 + c 35 + c 45 = 0
  eq1 : c 1 + c 21 + c 36 + c 46 = 0
  eq2 : c 2 + c 22 + c 37 + c 47 = 0
  eq3 : c 3 + c 23 + c 38 + c 48 = 0
  eq4 : c 4 + c 24 + c 39 + c 49 = 0
  eq5 : -c 5 - c 12 - c 18 = 0
  eq6 : c 0 - c 13 + c 17 = 0
  eq7 : c 2 + c 8 - c 15 = 0
  eq8 : c 3 - c 7 + c 10 = 0
  eq9 : -c 7 - c 11 - c 19 = 0
  eq10 : c 2 - c 14 + c 16 = 0
  eq11 : c 1 + c 9 - c 17 = 0
  eq12 : c 4 - c 6 + c 12 = 0
  eq17 : -c 20 - c 27 - c 33 = 0
  eq18 : c 5 - c 28 + c 32 = 0
  eq19 : c 7 + c 23 - c 30 = 0
  eq20 : c 8 - c 22 + c 25 = 0
  eq21 : -c 22 - c 26 - c 34 = 0
  eq22 : c 7 - c 29 + c 31 = 0
  eq23 : c 6 + c 24 - c 32 = 0
  eq24 : c 9 - c 21 + c 27 = 0
  eq29 : -c 25 - c 37 - c 43 = 0
  eq30 : c 10 - c 38 + c 42 = 0
  eq31 : c 12 + c 28 - c 40 = 0
  eq32 : c 13 - c 27 + c 35 = 0
  eq33 : -c 27 - c 36 - c 44 = 0
  eq34 : c 12 - c 39 + c 41 = 0
  eq35 : c 11 + c 29 - c 42 = 0
  eq36 : c 14 - c 26 + c 37 = 0


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestMinusCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate action of the three total minus rotations. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators

/-- Right quaternion multiplication, commuting with the fixed left frame. -/
def rightQuaternion (s : Fin 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![![0, -1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, -1, 0]],
    ![![0, 0, -1, 0], ![0, 0, 0, -1], ![1, 0, 0, 0], ![0, 1, 0, 0]],
    ![![0, 0, 0, -1], ![0, 0, 1, 0], ![0, -1, 0, 0], ![1, 0, 0, 0]]] s

def minusCoordinates (s : Fin 3) (c : Fin 21 → ℝ) : Fin 21 → ℝ :=
  ![
    ![-2 * c 1 - 2 * c 12 - 2 * c 20,
      2 * c 0 + 2 * c 7 + 2 * c 15,
      -c 3 + c 4 + c 13,
      c 2 + c 5 - c 8,
      -c 2 - c 5 + c 18,
      -c 3 + c 4 - c 13,
      2 * c 11,
      2 * c 12,
      2 * c 13,
      2 * c 14,
      2 * c 15,
      -c 6 + c 16,
      -c 7 + c 17,
      -c 8 + c 18,
      -c 9 + c 19,
      -c 10 + c 20,
      -2 * c 11,
      -2 * c 12,
      -2 * c 13,
      -2 * c 14,
      -2 * c 15],
    ![-2 * c 4,
      -2 * c 5,
      -c 1 - 2 * c 12 - c 20,
      c 0 + c 7,
      c 0 - c 17,
      c 1 - c 20,
      2 * c 9 - 2 * c 13,
      -2 * c 3 + 2 * c 13,
      2 * c 10 - 2 * c 12,
      -2 * c 6 - 2 * c 7 - 2 * c 15,
      2 * c 2 - 2 * c 8,
      -c 8 - c 18,
      c 2 - c 5 + c 18,
      -c 7 - c 17,
      -c 10 - c 20,
      c 3 + c 4 - c 13,
      -2 * c 13 - 2 * c 19,
      2 * c 4,
      -2 * c 12 - 2 * c 20,
      -2 * c 15 + 2 * c 16 + 2 * c 17,
      2 * c 5],
    ![2 * c 2,
      2 * c 3,
      -c 0 + c 7,
      -c 1 + c 10,
      -c 1 - c 20,
      c 0 + c 7 + 2 * c 15,
      2 * c 8 + 2 * c 14,
      -2 * c 2,
      2 * c 7 + 2 * c 15,
      2 * c 10 - 2 * c 11 - 2 * c 12,
      -2 * c 3,
      c 9 + c 19,
      -c 3 - c 4 + c 13,
      c 10 + c 20,
      -c 6 - c 7 - c 16 - c 17,
      c 2 - c 5 - c 8,
      2 * c 14 - 2 * c 18,
      -2 * c 5 + 2 * c 18,
      2 * c 15 - 2 * c 17,
      -2 * c 11 - 2 * c 12 - 2 * c 20,
      2 * c 4 - 2 * c 13]
  ] s

@[simp] theorem minusCoordinates_0_0 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 0 = -2 * c 1 - 2 * c 12 - 2 * c 20 := rfl

@[simp] theorem minusCoordinates_0_1 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 1 = 2 * c 0 + 2 * c 7 + 2 * c 15 := rfl

@[simp] theorem minusCoordinates_0_2 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 2 = -c 3 + c 4 + c 13 := rfl

@[simp] theorem minusCoordinates_0_3 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 3 = c 2 + c 5 - c 8 := rfl

@[simp] theorem minusCoordinates_0_4 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 4 = -c 2 - c 5 + c 18 := rfl

@[simp] theorem minusCoordinates_0_5 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 5 = -c 3 + c 4 - c 13 := rfl

@[simp] theorem minusCoordinates_0_6 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 6 = 2 * c 11 := rfl

@[simp] theorem minusCoordinates_0_7 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 7 = 2 * c 12 := rfl

@[simp] theorem minusCoordinates_0_8 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 8 = 2 * c 13 := rfl

@[simp] theorem minusCoordinates_0_9 (c : Fin 21 → ℝ) :
    minusCoordinates 0 c 9 = 2 * c 14 := rfl


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HessianAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assembly of the actual weighted Hessian square and its Green contributions. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators

/-- The first-derivative form obtained after all four Green calculations. -/
def collectedHessianForm (v b e B C E p2 : ℝ) : ℝ :=
  (-42 - 3 * b ^ 2 - (10 / 3) * v ^ 2) * e +
    75 * B + (25 / 3) * C - (100 / 3) * E + 5 * v ^ 2 * p2

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Matrix conjugation and the derivative-index change used at a single
spectral frame. All maps act on the actual matrix arrays; no smooth choice
of eigenvectors is involved. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix PositiveEinsteinFour.Geometry

noncomputable section

theorem orthogonal_sum_contraction (P : Mat4) (hP : P * Pᵀ = 1)
    (f : Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ j, ∑ k, (P j i * P k i) * f j k) = ∑ j, f j j := by
  have hp (j k : Fin 4) : (∑ i, P j i * P k i) = if j = k then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun N : Mat4 => N j k) hP
  calc
    _ = ∑ j, ∑ i, ∑ k, (P j i * P k i) * f j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, (P j i * P k i) * f j k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ k, (if j = k then 1 else 0) * f j k := by
      simp only [← Finset.sum_mul, hp]
    _ = _ := by simp

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The quadratic and radial scalar contractions are unchanged by the
pointwise spectral frame. These are identities on finite arrays. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix PositiveEinsteinFour.Geometry

noncomputable section

theorem orthogonal_square_sum (P : Mat4) (hP : P * Pᵀ = 1)
    (a : Fin 4 → ℝ) :
    (∑ i, (∑ j, P j i * a j) ^ 2) = ∑ j, a j ^ 2 := by
  have hp (j k : Fin 4) : (∑ i, P j i * P k i) = if j = k then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun N : Mat4 => N j k) hP
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ j, ∑ i, ∑ k, (P j i * P k i) * (a j * a k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ j, ∑ k, ∑ i, (P j i * P k i) * (a j * a k) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = _ := by simp only [← Finset.sum_mul, hp]; simp

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! All five Green integrals for the actual Weyl Hessian. The result has
only first derivatives and the constructed orthogonal-projection cost. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

section Integral

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

def hessianIntegral : C(Ω, ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM (μ := μ)).comp (ContinuousMap.toLp 1 μ ℝ)

end Integral

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Integrating the positive regularized cube root gives an energy
bound with an error tending to zero, without singular gradient limits. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem cubeRoot_regularization_error_le (v ε u : ℝ)
    (hv : 0 ≤ v) (hε : 0 < ε) (hu : 0 < u) (hsq : u ^ 2 = v ^ 2 + ε ^ 2) :
    2 * (u ^ (1 / 3 : ℝ)) ^ 2 - 2 * v * (u ^ (1 / 3 : ℝ)) ^ 2 -
        u ^ (1 / 3 : ℝ) * (2 * v ^ 2 * (1 - v) / u ^ (5 / 3 : ℝ)) ≤
      2 * ε ^ (2 / 3 : ℝ) := by
  have hu4 : 0 < u ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hu _
  have he4 : 0 < ε ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hε _
  have hf : (u ^ (1 / 3 : ℝ)) ^ 2 = u ^ 2 / u ^ (4 / 3 : ℝ) := by
    calc
      _ = u ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_mul_natCast hu.le]
        norm_num
      _ = _ := by
        simpa only [show (2 : ℝ) - 4 / 3 = 2 / 3 by norm_num,
          Real.rpow_two] using Real.rpow_sub hu 2 (4 / 3 : ℝ)
  have hr : u ^ (1 / 3 : ℝ) / u ^ (5 / 3 : ℝ) = (u ^ (4 / 3 : ℝ))⁻¹ := by
    rw [← Real.rpow_sub hu]
    rw [show (1 / 3 : ℝ) - 5 / 3 = -(4 / 3 : ℝ) by norm_num,
      Real.rpow_neg hu.le]
  have hid : 2 * (u ^ (1 / 3 : ℝ)) ^ 2 - 2 * v * (u ^ (1 / 3 : ℝ)) ^ 2 -
      u ^ (1 / 3 : ℝ) * (2 * v ^ 2 * (1 - v) / u ^ (5 / 3 : ℝ)) =
      2 * ε ^ 2 * (1 - v) / u ^ (4 / 3 : ℝ) := by
    rw [hf]
    calc
      _ = 2 * u ^ 2 / u ^ (4 / 3 : ℝ) - 2 * v * u ^ 2 / u ^ (4 / 3 : ℝ) -
          2 * v ^ 2 * (1 - v) * (u ^ (1 / 3 : ℝ) / u ^ (5 / 3 : ℝ)) := by ring
      _ = _ := by rw [hr, hsq]; ring
  have heu : ε ≤ u := by nlinarith [sq_nonneg v]
  have hpow : ε ^ (4 / 3 : ℝ) ≤ u ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow hε.le heu (by norm_num)
  have hb : ε ^ 2 / u ^ (4 / 3 : ℝ) ≤ ε ^ (2 / 3 : ℝ) := by
    calc
      _ ≤ ε ^ 2 / ε ^ (4 / 3 : ℝ) :=
        div_le_div_of_nonneg_left (sq_nonneg ε) he4 hpow
      _ = _ := by
        symm
        simpa only [show (2 : ℝ) - 4 / 3 = 2 / 3 by norm_num,
          Real.rpow_two] using Real.rpow_sub hε 2 (4 / 3 : ℝ)
  rw [hid]
  calc
    _ ≤ 2 * ε ^ 2 / u ^ (4 / 3 : ℝ) := by
      apply div_le_div_of_nonneg_right _ hu4.le
      nlinarith [mul_nonneg (sq_nonneg ε) hv]
    _ = 2 * (ε ^ 2 / u ^ (4 / 3 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal curvature and its covariant derivative depend on the first
frame direction through their Frobenius norms, not on the normal basis. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem directionalCurvature_sumFour_moveLast (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  calc
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        _ = ∑ b, ∑ d, ∑ c, f a b c d := by
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm
    _ = _ := Finset.sum_comm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The individual Weyl norms descend to each oriented frame component. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix QuaternionFrame
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem sumPair_product (F G : Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, F a b) * (∑ c, ∑ d, G c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, F a b * G c d := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_DeterminantCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The determinant comparison used when the first sine mode is split off
from a discrete Jacobi matrix. The complementary block need not commute with
the first block or with the curvature matrices at other times. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

/-- The trace form of the arithmetic-geometric mean estimate. -/
theorem det_le_exp_trace {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    A.det ≤ Real.exp (A.trace - Fintype.card n) := by
  calc
    A.det = ∏ i, hA.isHermitian.eigenvalues i := by
      simpa using hA.isHermitian.det_eq_prod_eigenvalues
    _ ≤ ∏ i, Real.exp (hA.isHermitian.eigenvalues i - 1) := by
      apply Finset.prod_le_prod
      · intro i _
        exact hA.eigenvalues_nonneg i
      · intro i _
        have h := Real.add_one_le_exp (hA.isHermitian.eigenvalues i - 1)
        linarith
    _ = Real.exp (A.trace - Fintype.card n) := by
      rw [← Real.exp_sum, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      congr 1
      simpa using hA.isHermitian.trace_eq_sum_eigenvalues.symm

theorem det_le_one_of_trace_le_card {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (htrace : A.trace ≤ Fintype.card n) :
    A.det ≤ 1 := by
  calc
    A.det ≤ Real.exp (A.trace - Fintype.card n) := det_le_exp_trace hA
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (sub_nonpos.mpr htrace)
    _ = 1 := Real.exp_zero

/-- Discarding the complementary modes costs no determinant when their
trace is at most their dimension. This is the finite-matrix step in the
upper radial comparison. -/
theorem det_fromBlocks_le_first {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {P : Matrix m m ℝ} {C : Matrix m n ℝ} {Q : Matrix n n ℝ}
    (hP : P.PosDef) (hA : (fromBlocks P C Cᴴ Q).PosSemidef)
    (htrace : Q.trace ≤ Fintype.card n) :
    (fromBlocks P C Cᴴ Q).det ≤ P.det := by
  let : Invertible P := hP.isUnit.invertible
  have hS : (Q - Cᴴ * P⁻¹ * C).PosSemidef :=
    (PosDef.fromBlocks₁₁ C Q hP).mp hA
  have hcost : 0 ≤ (Cᴴ * P⁻¹ * C).trace := by
    exact (hP.posSemidef.inv.conjTranspose_mul_mul_same C).trace_nonneg
  have hStrace : (Q - Cᴴ * P⁻¹ * C).trace ≤ Fintype.card n := by
    rw [trace_sub]
    linarith
  have hdet := det_le_one_of_trace_le_card hS hStrace
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  simpa using mul_le_mul_of_nonneg_left hdet hP.det_pos.le

/-- In a positive definite block matrix, the first compression is already
positive definite; no extra hypothesis on it is necessary. -/
theorem det_posDef_fromBlocks_le_first {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {P : Matrix m m ℝ} {C : Matrix m n ℝ} {Q : Matrix n n ℝ}
    (hA : (fromBlocks P C Cᴴ Q).PosDef)
    (htrace : Q.trace ≤ Fintype.card n) :
    (fromBlocks P C Cᴴ Q).det ≤ P.det := by
  have hP : P.PosDef := by
    convert hA.submatrix Sum.inl_injective using 1
    all_goals try with_reducible_and_instances rfl
    ext i j
    rfl
  exact det_fromBlocks_le_first hP hA.posSemidef htrace

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FiniteHodgeMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional multiplicity identity for a nonzero Hodge
eigenvalue, expressed through its actual codifferential image. -/

namespace PositiveEinsteinFour.Geometry

noncomputable section

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

def hodgeRangePair (C : V →ₗ[ℝ] W) (S : Module.End ℝ V) :
    V →ₗ[ℝ] C.range × C.range :=
  C.rangeRestrict.prod (C.rangeRestrict.comp S)

theorem hodgeRangePair_bijective (C : V →ₗ[ℝ] W) (A S : Module.End ℝ V)
    (κ : ℝ) (hκ : κ ≠ 0)
    (hS : ∀ u, S (S u) = u)
    (hCA : ∀ u, C (A u) = κ • C u)
    (hCSA : ∀ u, C (S (A u)) = 0)
    (hker : ∀ u, C u = 0 → A u = 0)
    (hsplit : ∀ u, A u + S (A (S u)) = κ • u) :
    Function.Bijective (hodgeRangePair C S) := by
  constructor
  · intro u v huv
    have h₁ : C u = C v := congrArg (fun z : C.range × C.range => z.1.val) huv
    have h₂ : C (S u) = C (S v) := congrArg (fun z : C.range × C.range => z.2.val) huv
    have h₃ : A (u - v) = 0 := hker _ (by rw [map_sub, h₁, sub_self])
    have h₄ : A (S (u - v)) = 0 := hker _ (by rw [map_sub, map_sub, h₂, sub_self])
    have h := hsplit (u - v)
    rw [h₃, h₄, map_zero, add_zero] at h
    exact sub_eq_zero.mp ((smul_eq_zero.mp h.symm).resolve_left hκ)
  · rintro ⟨u, v⟩
    obtain ⟨a, ha⟩ := u.property
    obtain ⟨b, hb⟩ := v.property
    refine ⟨κ⁻¹ • (A a + S (A b)), ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change C (κ⁻¹ • (A a + S (A b))) = u.val
      rw [map_smul, map_add, hCA, hCSA, add_zero, inv_smul_smul₀ hκ, ha]
    · apply Subtype.ext
      change C (S (κ⁻¹ • (A a + S (A b)))) = v.val
      rw [map_smul, map_add, hS, map_smul, map_add, hCSA, hCA,
        zero_add, inv_smul_smul₀ hκ, hb]

theorem finite_hodge_multiplicity [FiniteDimensional ℝ V]
    (C : V →ₗ[ℝ] W) (A S : Module.End ℝ V) (κ : ℝ) (hκ : κ ≠ 0)
    (hS : ∀ u, S (S u) = u)
    (hCA : ∀ u, C (A u) = κ • C u)
    (hCSA : ∀ u, C (S (A u)) = 0)
    (hker : ∀ u, C u = 0 → A u = 0)
    (hsplit : ∀ u, A u + S (A (S u)) = κ • u) :
    Module.finrank ℝ V = 2 * Module.finrank ℝ C.range := by
  let e := LinearEquiv.ofBijective (hodgeRangePair C S)
    (hodgeRangePair_bijective C A S κ hκ hS hCA hCSA hker hsplit)
  simpa only [Module.finrank_prod, two_mul] using e.finrank_eq

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FiniteHodgeTraceCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional trace cancellation used for a positive Hodge
eigenvalue. Its three identities are the exact/coexact differential identities. -/

namespace PositiveEinsteinFour.Geometry

theorem finite_hodge_trace_cancel {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (A S : Module.End ℝ V) (κ : ℝ) (hκ : κ ≠ 0)
    (hAA : A * A = κ • A) (hASA : A * S * A = 0)
    (hSA : S * A + A * S = κ • S) : LinearMap.trace ℝ V S = 0 := by
  have hzero : LinearMap.trace ℝ V (S * (A * A)) = 0 := by
    rw [← mul_assoc, LinearMap.trace_mul_cycle, hASA, map_zero]
  have htraceA : LinearMap.trace ℝ V (S * A) = 0 := by
    rw [hAA, mul_smul_comm, map_smul, smul_eq_mul] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hκ
  have he := congrArg (LinearMap.trace ℝ V) hSA
  rw [map_add, LinearMap.trace_mul_comm ℝ A S, htraceA, zero_add,
    map_smul, smul_eq_mul] at he
  exact (mul_eq_zero.mp he.symm).resolve_left hκ

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatDirichletGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit positive Green kernel for the flat discrete Dirichlet operator. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

def flatGreenValue (N j i : ℕ) : ℝ :=
  (min i j : ℕ) - (i : ℝ) * j / (N + 1)

def flatGreen (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => flatGreenValue N (j.val + 1) (i.val + 1)

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FlatDirichletGreenTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace and mesh limit of the flat Green matrix. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
open scoped _root_.Topology
noncomputable section

def scaledFlatGreen (t : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (t / (N + 1)) ^ 2 • flatGreen N

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stability and consistency for the kick-drift approximation of the
matrix Jacobi equation. The estimates use operator bounds, so no two
curvature matrices are required to commute. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Position and backward velocity both converge once the uniform mesh
estimate is available. This applies to matrices as a finite-dimensional
normed space, without any commutation assumption. -/
theorem converges_of_inverse_mesh_error
    {x v : ℕ → E} {X V : E} {C : ℝ}
    (herror : ∀ᶠ N in atTop,
      ‖x N - X‖ + ‖v N - V‖ ≤ C / N) :
    Tendsto x atTop (nhds X) ∧ Tendsto v atTop (nhds V) := by
  have hsum : Tendsto (fun N => ‖x N - X‖ + ‖v N - V‖) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => by positivity) herror
      (tendsto_const_div_atTop_nhds_zero_nat C)
  constructor
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun _ => le_add_of_nonneg_right
      (norm_nonneg _)) hsum
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun _ => le_add_of_nonneg_left
      (norm_nonneg _)) hsum

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrthogonalCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Determinant compression after an orthogonal change of basis. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

/-- Complete orthonormal columns to an orthogonal matrix while keeping
each prescribed column in its original position. -/
theorem orthogonal_extension {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (W : Matrix (m ⊕ n) m ℝ) (hW : Wᴴ * W = 1) :
    ∃ U : Matrix (m ⊕ n) (m ⊕ n) ℝ,
      U * Uᴴ = 1 ∧ ∀ i j, U i (Sum.inl j) = W i j := by
  let v : m ⊕ n → EuclideanSpace ℝ (m ⊕ n) :=
    Sum.elim (fun j => WithLp.toLp 2 (fun i => W i j)) (fun _ => 0)
  have hw : Orthonormal ℝ (fun j : m => v (Sum.inl j)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have h := congrFun (congrFun hW i) j
    simpa [v, Matrix.mul_apply, Matrix.conjTranspose_apply, PiLp.inner_apply,
      RCLike.inner_apply, Matrix.one_apply, mul_comm] using h
  let s : Set (m ⊕ n) := Set.range Sum.inl
  have hs : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, a, rfl⟩ ⟨j, b, rfl⟩
    simpa only [Set.domRestrict_apply, Subtype.ext_iff, Sum.inl.injEq] using
      (orthonormal_iff_ite.mp hw a b)
  obtain ⟨b, hb⟩ := hs.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (m ⊕ n)) = Fintype.card (m ⊕ n))
  let a := EuclideanSpace.basisFun (m ⊕ n) ℝ
  refine ⟨a.toBasis.toMatrix b, a.toMatrix_orthonormalBasis_self_mul_conjTranspose b, ?_⟩
  intro i j
  change a.repr (b (Sum.inl j)) i = W i j
  rw [hb (Sum.inl j) ⟨j, rfl⟩]
  rfl

theorem trace_sum_blocks {m n : Type*} [Fintype m] [Fintype n]
    (B : Matrix (m ⊕ n) (m ⊕ n) ℝ) :
    B.trace = B.toBlocks₁₁.trace + B.toBlocks₂₂.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type,
    Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

/-- The determinant loss depends on the first compression and total trace,
not on the choice of an orthonormal basis of its complement. -/
theorem det_le_orthogonal_compression {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A U : Matrix (m ⊕ n) (m ⊕ n) ℝ}
    (hA : A.PosDef) (hU : U * Uᴴ = 1)
    (htrace : A.trace ≤ Fintype.card m + Fintype.card n)
    (hfirst : (Uᴴ * A * U).toBlocks₁₁.trace = Fintype.card m) :
    A.det ≤ (Uᴴ * A * U).toBlocks₁₁.det := by
  have hdetU : U.det * Uᴴ.det = 1 := by
    rw [← Matrix.det_mul, hU, Matrix.det_one]
  have hunit : IsUnit U := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    rw [hz, zero_mul] at hdetU
    exact zero_ne_one hdetU
  let B := Uᴴ * A * U
  have hB : B.PosDef := hA.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit hunit)
  have htrB : B.trace = A.trace := by
    dsimp [B]
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  have hdetB : B.det = A.det := by
    dsimp [B]
    rw [Matrix.det_mul, Matrix.det_mul]
    calc
      Uᴴ.det * A.det * U.det = A.det * (U.det * Uᴴ.det) := by ring
      _ = A.det := by rw [hdetU, mul_one]
  have hcross : B.toBlocks₂₁ = B.toBlocks₁₂ᴴ := by
    ext i j
    exact congrFun (congrFun hB.isHermitian.eq (Sum.inl j)) (Sum.inr i)
  have hblocks : fromBlocks B.toBlocks₁₁ B.toBlocks₁₂ B.toBlocks₁₂ᴴ B.toBlocks₂₂ = B := by
    rw [← hcross, Matrix.fromBlocks_toBlocks]
  have hcomplement : B.toBlocks₂₂.trace ≤ Fintype.card n := by
    have ht := trace_sum_blocks B
    change B.toBlocks₁₁.trace = _ at hfirst
    linarith
  have hbound := det_posDef_fromBlocks_le_first
    (hblocks.symm ▸ hB) hcomplement
  rwa [hblocks, hdetB] at hbound

/-- An orthonormal family of columns is enough to apply the determinant
comparison; the complementary basis is constructed, not assumed. -/
theorem det_le_isometric_compression {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix (m ⊕ n) (m ⊕ n) ℝ} (W : Matrix (m ⊕ n) m ℝ)
    (hA : A.PosDef) (hW : Wᴴ * W = 1)
    (htrace : A.trace ≤ Fintype.card m + Fintype.card n)
    (hfirst : (Wᴴ * A * W).trace = Fintype.card m) :
    A.det ≤ (Wᴴ * A * W).det := by
  obtain ⟨U, hU, hUW⟩ := orthogonal_extension W hW
  have heq : (Uᴴ * A * U).toBlocks₁₁ = Wᴴ * A * W := by
    ext i j
    simp [Matrix.toBlocks₁₁, Matrix.mul_apply, hUW]
  have h := det_le_orthogonal_compression hA hU htrace (heq ▸ hfirst)
  rwa [heq] at h

/-- Reindexing version for a matrix whose ambient coordinates need not
already separate the distinguished columns from their complement. -/
theorem det_le_isometric_compression_of_card {I m n : Type*}
    [Fintype I] [Fintype m] [Fintype n]
    [DecidableEq I] [DecidableEq m] [DecidableEq n]
    (hcard : Fintype.card I = Fintype.card m + Fintype.card n)
    {A : Matrix I I ℝ} (W : Matrix I m ℝ)
    (hA : A.PosDef) (hW : Wᴴ * W = 1)
    (htrace : A.trace ≤ Fintype.card I)
    (hfirst : (Wᴴ * A * W).trace = Fintype.card m) :
    A.det ≤ (Wᴴ * A * W).det := by
  let e : m ⊕ n ≃ I := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let A' := A.submatrix e e
  let W' := W.submatrix e id
  have hgram : W'ᴴ * W' = Wᴴ * W := by
    simp only [W', Matrix.conjTranspose_submatrix]
    exact Matrix.submatrix_mul_equiv Wᴴ W id e id
  have hcompression : W'ᴴ * A' * W' = Wᴴ * A * W := by
    simp only [W', A', Matrix.conjTranspose_submatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl
  have htr : A'.trace = A.trace := by
    exact e.sum_comp (fun i => A i i)
  have h := det_le_isometric_compression W' (hA.submatrix e.injective)
    (hgram.trans hW) (by rw [htr]; simpa [hcard] using htrace)
    (by rw [hcompression]; exact hfirst)
  simpa only [A', Matrix.det_submatrix_equiv_self, hcompression] using h

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarH1CompositionL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded scalar multipliers on real L², including convergence when the
multiplier converges almost everywhere and the multiplied vector converges
strongly.  This is the analytic closure step in the scalar H¹ chain rule. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped _root_.Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def scalarCompositionL2Multiply (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    {C : ℝ} (hC : ∀ x, |a x| ≤ C) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  ((Lp.memLp f).of_le_mul (ha.mul (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun x => by
      simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul] using
        mul_le_mul_of_nonneg_right (hC x) (abs_nonneg (f x)))).toLp _

theorem scalarCompositionL2Multiply_coe (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    {C : ℝ} (hC : ∀ x, |a x| ≤ C) (f : Lp ℝ 2 μ) :
    scalarCompositionL2Multiply a ha hC f =ᵐ[μ] fun x => a x * f x :=
  MemLp.coeFn_toLp _

theorem scalarCompositionL2Multiply_norm_le (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    {C : ℝ} (hC : ∀ x, |a x| ≤ C) (f : Lp ℝ 2 μ) :
    ‖scalarCompositionL2Multiply a ha hC f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarCompositionL2Multiply_coe a ha hC f] with x hx
  rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)

theorem scalarL2_norm_sq (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Almost-everywhere convergence of uniformly bounded multipliers is strong
on each fixed L² vector. -/
theorem scalarCompositionL2Multiply_tendsto_fixed {a : ℕ → X → ℝ} {b : X → ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : 0 ≤ C) (haC : ∀ n x, |a n x| ≤ C) (hbC : ∀ x, |b x| ≤ C)
    (hab : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    (f : Lp ℝ 2 μ) :
    Tendsto (fun n => scalarCompositionL2Multiply (a n) (ha n) (haC n) f) atTop
      (𝓝 (scalarCompositionL2Multiply b hb hbC f)) := by
  let q : ℕ → Lp ℝ 2 μ := fun n =>
    scalarCompositionL2Multiply (a n) (ha n) (haC n) f - scalarCompositionL2Multiply b hb hbC f
  have hq (n : ℕ) : q n =ᵐ[μ] fun x => (a n x - b x) * f x := by
    filter_upwards [Lp.coeFn_sub (scalarCompositionL2Multiply (a n) (ha n) (haC n) f)
      (scalarCompositionL2Multiply b hb hbC f), scalarCompositionL2Multiply_coe (a n) (ha n) (haC n) f,
      scalarCompositionL2Multiply_coe b hb hbC f] with x hsub hx hy
    simpa only [q, Pi.sub_apply, hx, hy, sub_mul] using hsub
  have hi : Integrable (fun x => (2 * C) ^ 2 * f x ^ 2) μ :=
    (Lp.memLp f).integrable_sq.const_mul _
  have hd := tendsto_integral_of_dominated_convergence
    (fun x => (2 * C) ^ 2 * f x ^ 2)
    (fun n => ((ha n).sub hb).mul (Lp.aestronglyMeasurable f) |>.pow 2)
    hi (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      have hbound : |a n x - b x| ≤ 2 * C :=
        (abs_sub (a n x) (b x)).trans (by linarith [haC n x, hbC x])
      have hs : (a n x - b x) ^ 2 ≤ (2 * C) ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hbound
      exact mul_le_mul_of_nonneg_right hs (sq_nonneg _))
    (f := fun _ => (0 : ℝ)) (by
      filter_upwards [hab] with x hx
      have h0 : Tendsto (fun n => (a n x - b x) * f x) atTop (𝓝 0) := by
        simpa only [sub_self, zero_mul] using (hx.sub_const (b x)).mul_const (f x)
      simpa only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply,
        zero_pow (by decide : (2 : ℕ) ≠ 0)] using! h0.pow 2)
  have hs : Tendsto (fun n => ‖q n‖ ^ 2) atTop (𝓝 0) := by
    convert hd using 1
    · funext n
      rw [scalarL2_norm_sq]
      exact integral_congr_ae ((hq n).fun_comp fun r : ℝ => r ^ 2)
    · simp
  have hn : Tendsto (fun n => ‖q n‖) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
      Real.sqrt_zero] using h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- Both factors may move: bounded multiplier convergence and strong L²
convergence imply strong convergence of their product. -/
theorem scalarCompositionL2Multiply_tendsto {a : ℕ → X → ℝ} {b : X → ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : 0 ≤ C) (haC : ∀ n x, |a n x| ≤ C) (hbC : ∀ x, |b x| ≤ C)
    (hab : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    {f : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ} (hfg : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => scalarCompositionL2Multiply (a n) (ha n) (haC n) (f n)) atTop
      (𝓝 (scalarCompositionL2Multiply b hb hbC g)) := by
  have heq (n : ℕ) : scalarCompositionL2Multiply (a n) (ha n) (haC n) (f n) =
      scalarCompositionL2Multiply (a n) (ha n) (haC n) (f n - g) +
        scalarCompositionL2Multiply (a n) (ha n) (haC n) g := by
    apply Lp.ext
    filter_upwards [scalarCompositionL2Multiply_coe (a n) (ha n) (haC n) (f n),
      scalarCompositionL2Multiply_coe (a n) (ha n) (haC n) (f n - g),
      scalarCompositionL2Multiply_coe (a n) (ha n) (haC n) g, Lp.coeFn_sub (f n) g,
      Lp.coeFn_add (scalarCompositionL2Multiply (a n) (ha n) (haC n) (f n - g))
        (scalarCompositionL2Multiply (a n) (ha n) (haC n) g)] with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.sub_apply, Pi.add_apply] at h₄ h₅
    rw [h₁, h₅, h₂, h₃, h₄]
    ring
  have hzero : Tendsto (fun n => scalarCompositionL2Multiply (a n) (ha n) (haC n) (f n - g))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => scalarCompositionL2Multiply_norm_le (a n) (ha n) (haC n) (f n - g))
    simpa using (tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hfg))
  simpa only [heq, zero_add] using
    hzero.add (scalarCompositionL2Multiply_tendsto_fixed ha hb hC haC hbC hab g)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarLpVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation of the scalar p-moment along bounded directions.
The base function need only belong to Lp, including at its zero set. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Set Filter
open scoped _root_.Topology ENNReal

noncomputable section

theorem scalarMoment_point_derivative {p : ℝ} (hp : 2 < p)
    (f b t : ℝ) :
    HasDerivAt (fun s : ℝ => |f + s * b| ^ p)
      (p * |f + t * b| ^ (p - 2) * (f + t * b) * b) t := by
  have hlin : HasDerivAt (fun s : ℝ => f + s * b) b t := by
    simpa only [one_mul, zero_add, Pi.add_apply, id_eq] using!
      (hasDerivAt_const t f).add ((hasDerivAt_id t).mul_const b)
  simpa only [Function.comp_def] using
    (hasDerivAt_abs_rpow (f + t * b) (by linarith : 1 < p)).comp t hlin

theorem scalarMoment_derivative_bound {p B : ℝ} (hp : 2 < p) (hB : 0 ≤ B)
    {f b t : ℝ} (hb : |b| ≤ B) (ht : |t| ≤ 1) :
    ‖p * |f + t * b| ^ (p - 2) * (f + t * b) * b‖ ≤
      (p * B) * (|f| + B) ^ (p - 1) := by
  have hpow : |f + t * b| ^ (p - 2) * |f + t * b| =
      |f + t * b| ^ (p - 1) := by
    rw [← Real.rpow_add_one' (abs_nonneg _) (by linarith : p - 2 + 1 ≠ 0)]
    congr 1
    ring
  have hbase : |f + t * b| ≤ |f| + B :=
    (abs_add_le _ _).trans (add_le_add le_rfl
      ((abs_mul t b).le.trans ((mul_le_mul ht hb (abs_nonneg b) zero_le_one).trans_eq
        (one_mul B))))
  calc
    ‖p * |f + t * b| ^ (p - 2) * (f + t * b) * b‖ =
        p * |f + t * b| ^ (p - 1) * |b| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_pos (by linarith : 0 < p),
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      rw [mul_assoc p, hpow]
    _ ≤ p * (|f| + B) ^ (p - 1) * B := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) hbase (by linarith)) (by linarith)
      · exact hb
      · exact abs_nonneg b
      · exact mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
    _ = (p * B) * (|f| + B) ^ (p - 1) := by ring

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- A bounded measurable direction differentiates the p-moment of an arbitrary
Lp function.  No nonvanishing or regularity assumption is placed on the latter. -/
theorem scalarLpMoment_hasDerivAt {p : ℝ} (hp : 2 < p) {f b : X → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) (hb : AEStronglyMeasurable b μ)
    {B : ℝ} (hB : 0 ≤ B) (hbBound : ∀ᵐ x ∂μ, |b x| ≤ B) :
    Integrable (fun x => |f x| ^ (p - 2) * f x * b x) μ ∧
      HasDerivAt (fun t : ℝ => ∫ x, |f x + t * b x| ^ p ∂μ)
        (p * ∫ x, |f x| ^ (p - 2) * f x * b x ∂μ) 0 := by
  let F (t : ℝ) (x : X) := |f x + t * b x| ^ p
  let G (t : ℝ) (x : X) := p * |f x + t * b x| ^ (p - 2) * (f x + t * b x) * b x
  let H (x : X) := (p * B) * (|f x| + B) ^ (p - 1)
  have hp0 : 0 < p := by linarith
  have hpowMeas {q : ℝ} (hq : 0 ≤ q) {h : X → ℝ}
      (hh : AEStronglyMeasurable h μ) :
      AEStronglyMeasurable (fun x => |h x| ^ q) μ := by
    have hc : Continuous (fun r : ℝ => |r| ^ q) :=
      continuous_abs.rpow_const (fun _ => Or.inr hq)
    exact hc.comp_aestronglyMeasurable hh
  have hFm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) μ := by
    exact Eventually.of_forall fun t => hpowMeas hp0.le
      (hf.aestronglyMeasurable.add (hb.const_mul t))
  have hFi : Integrable (F 0) μ := by
    simpa only [F, zero_mul, add_zero, Real.norm_eq_abs,
      ENNReal.toReal_ofReal hp0.le] using hf.integrable_norm_rpow'
  have hGm : AEStronglyMeasurable (G 0) μ := by
    simpa only [G, zero_mul, add_zero, Pi.mul_apply] using!
      (((hpowMeas (by linarith : 0 ≤ p - 2) hf.aestronglyMeasurable).const_mul p).mul
        hf.aestronglyMeasurable).mul hb
  have hbaseLp : MemLp (fun x => |f x| + B) (ENNReal.ofReal p) μ := by
    simpa only [Real.norm_eq_abs, Pi.add_apply] using! hf.norm.add (memLp_const B)
  have hbaseInt : Integrable (fun x => ‖|f x| + B‖ ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hbaseLp.integrable_norm_rpow'
  have hlessInt : Integrable (fun x => (|f x| + B) ^ (p - 1)) μ := by
    have hi := integrable_norm_rpow_of_le hbaseLp.aestronglyMeasurable
      (by linarith : 0 ≤ p - 1) hp0.le (by linarith : p - 1 ≤ p) hbaseInt
    simpa only [Real.norm_of_nonneg (add_nonneg (abs_nonneg _) hB)] using hi
  have hHi : Integrable H μ := hlessInt.const_mul (p * B)
  have hbound : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (-1 : ℝ) 1, ‖G t x‖ ≤ H x := by
    filter_upwards [hbBound] with x hx t ht
    exact scalarMoment_derivative_bound hp hB hx (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)
  have hdiff : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => F s x) (G t x) t :=
    Eventually.of_forall fun x t _ => scalarMoment_point_derivative hp (f x) (b x) t
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by constructor <;> norm_num))
    hFm hFi hGm hbound hHi hdiff
  have hi : Integrable (fun x => |f x| ^ (p - 2) * f x * b x) μ := by
    have hscaled := h.1.const_mul p⁻¹
    convert hscaled using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [G, zero_mul, add_zero]
    field_simp [ne_of_gt hp0]
  refine ⟨hi, ?_⟩
  have heq : (fun x => G 0 x) = fun x => p * (|f x| ^ (p - 2) * f x * b x) := by
    funext x
    dsimp [G]
    simp only [zero_mul, add_zero]
    ring
  simpa only [heq, integral_const_mul] using h.2

/-- Lp-space version, ready for a weak variational equation. -/
theorem scalarLpMoment_hasDerivAt_lp {p : ℝ} (hp : 2 < p)
    (f : Lp ℝ (ENNReal.ofReal p) μ) {b : X → ℝ}
    (hb : AEStronglyMeasurable b μ) {B : ℝ} (hB : 0 ≤ B)
    (hbBound : ∀ᵐ x ∂μ, |b x| ≤ B) :
    HasDerivAt (fun t : ℝ => ∫ x, |f x + t * b x| ^ p ∂μ)
      (p * ∫ x, |f x| ^ (p - 2) * f x * b x ∂μ) 0 :=
  (scalarLpMoment_hasDerivAt hp (Lp.memLp f) hb hB hbBound).2

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarLpNormVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squared Lp norm at a normalized function has the expected first
variation, including for sign-changing or merely Lp representatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Set Filter
open scoped _root_.Topology ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The ordinary real Lp norm as an integral of the actual representative. -/
theorem scalarLp_norm_eq_moment {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (f : Lp ℝ (ENNReal.ofReal p) μ) :
    ‖f‖ = (∫ x, |f x| ^ p ∂μ) ^ p⁻¹ := by
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
      ENNReal.ofReal_ne_top (Lp.aestronglyMeasurable f)]
  simp only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs]
  all_goals exact Lp.aestronglyMeasurable f

theorem scalarLp_moment_eq_norm_rpow {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (f : Lp ℝ (ENNReal.ofReal p) μ) :
    (∫ x, |f x| ^ p ∂μ) = ‖f‖ ^ p := by
  rw [scalarLp_norm_eq_moment hp f,
    Real.rpow_inv_rpow (integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)) hp.ne']

theorem scalarLp_norm_sq_eq_moment {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (f : Lp ℝ (ENNReal.ofReal p) μ) :
    ‖f‖ ^ 2 = (∫ x, |f x| ^ p ∂μ) ^ (2 / p) := by
  rw [scalarLp_moment_eq_norm_rpow hp f, ← Real.rpow_mul (norm_nonneg f)]
  have he : p * (2 / p) = 2 := by field_simp [hp.ne']
  rw [he, Real.rpow_two]

theorem scalarLp_add_smul_moment {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (f b : Lp ℝ (ENNReal.ofReal p) μ) (t : ℝ) :
    (∫ x, |(f + t • b) x| ^ p ∂μ) = ∫ x, |f x + t * b x| ^ p ∂μ := by
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f (t • b), Lp.coeFn_smul t b] with x hsum hsmul
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hsum hsmul
  rw [hsum, hsmul]

variable [IsFiniteMeasure μ]

/-- At Lp norm one, the squared norm differentiates to twice the nonlinear
pairing against a bounded measurable direction. -/
theorem scalarLpNormSq_hasDerivAt {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 < p) (f b : Lp ℝ (ENNReal.ofReal p) μ) (hf : ‖f‖ = 1)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ, |b x| ≤ B) :
    HasDerivAt (fun t : ℝ => ‖f + t • b‖ ^ 2)
      (2 * ∫ x, |f x| ^ (p - 2) * f x * b x ∂μ) 0 := by
  have hp0 : 0 < p := by linarith
  have hd := scalarLpMoment_hasDerivAt_lp hp f (Lp.aestronglyMeasurable b) hB hb
  have hz : (∫ x, |f x + (0 : ℝ) * b x| ^ p ∂μ) = 1 := by
    simp only [zero_mul, add_zero]
    rw [scalarLp_moment_eq_norm_rpow hp0 f, hf, Real.one_rpow]
  have hpow := hd.rpow_const (p := 2 / p) (Or.inl (by rw [hz]; norm_num))
  have heq : (fun t : ℝ => ‖f + t • b‖ ^ 2) =
      fun t => (∫ x, |f x + t * b x| ^ p ∂μ) ^ (2 / p) := by
    funext t
    rw [scalarLp_norm_sq_eq_moment hp0, scalarLp_add_smul_moment]
  rw [← heq] at hpow
  convert hpow using 1
  all_goals try with_reducible_and_instances rfl
  rw [hz, Real.one_rpow, mul_one]
  field_simp [hp0.ne']

/-- A continuous representative of the direction is sufficient; no regularity
or pointwise sign is required of the normalized Lp function. -/
theorem scalarLpNormSq_hasDerivAt_continuous [TopologicalSpace X]
    [OpensMeasurableSpace X] [CompactSpace X] {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p)
    (f b : Lp ℝ (ENNReal.ofReal p) μ) (hf : ‖f‖ = 1)
    (v : C(X, ℝ)) (hb : (b : X → ℝ) =ᵐ[μ] v) :
    HasDerivAt (fun t : ℝ => ‖f + t • b‖ ^ 2)
      (2 * ∫ x, |f x| ^ (p - 2) * f x * v x ∂μ) 0 := by
  have hbound : ∀ᵐ x ∂μ, |b x| ≤ ‖v‖ := by
    filter_upwards [hb] with x hx
    rw [hx]
    exact v.norm_coe_le_norm x
  have hd := scalarLpNormSq_hasDerivAt hp f b hf (norm_nonneg v) hbound
  have hi : (∫ x, |f x| ^ (p - 2) * f x * b x ∂μ) =
      ∫ x, |f x| ^ (p - 2) * f x * v x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hb] with x hx
    rw [hx]
  rwa [hi] at hd

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricDoubleCover
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric and Euler reductions for an actual two-sheeted cover.
The raw metric facts are the pullback/local-isometry and geodesic-lifting
consequences of Petersen, §1.3.3 and Proposition 5.6.3. The minimum-distance
formula, two-point fiber count, antipodal quotient and parity obstruction
are derived here. -/

namespace PositiveEinsteinFour

open EinsteinFour
open scoped Manifold ContDiff ENNReal

noncomputable section

universe u v

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace FourSpace M] [ChartedSpace FourSpace N]
  [IsManifold I4 ∞ M] [IsManifold I4 ∞ N]

/-- Raw data of a Riemannian two-sheeted cover. `distance_lift` is the
endpoint of a lift of a minimizing base geodesic from the specified point;
the other distance inequality is length preservation under projection. -/
structure MetricDoubleCover (g : SmoothMetric M) (h : SmoothMetric N) where
  projection : N → M
  covering : IsCoveringMap projection
  surjective : Function.Surjective projection
  deck : N → N
  involutive : Function.Involutive deck
  free : ∀ x, deck x ≠ x
  fibers : ∀ x y, projection x = projection y ↔ x = y ∨ x = deck y
  deck_distance : ∀ x y, scaledEDistance h 1 (deck x) (deck y) = scaledEDistance h 1 x y
  distance_down : ∀ x y, scaledEDistance g 1 (projection x) (projection y) ≤
    scaledEDistance h 1 x y
  distance_lift : ∀ x y, ∃ z, projection z = projection y ∧
    scaledEDistance h 1 x z ≤ scaledEDistance g 1 (projection x) (projection y)

end
end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ModeAverageLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence of the normalized scalar-mode curvature average. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def interiorMean (f : ℝ → E) (N : ℕ) : E :=
  (1 / ((N : ℝ) + 1)) • ∑ i : Fin N, f ((i.val + 1) / ((N : ℝ) + 1))

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Jacobi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar determinant loss in the radial comparison, using the three
eigenvalues of the averaged normal Jacobi curvature matrix. -/

namespace PositiveEinsteinFour.Jacobi

noncomputable section

def loss (β a b c : ℝ) : ℝ := 1 - (1 - β * a) * (1 - β * b) * (1 - β * c)

def lossFactor (β : ℝ) : ℝ := min 1 (β ^ 2 * max 1 (3 - β))

theorem loss_identity {a b c : ℝ} (htrace : a + b + c = 0) (β : ℝ) :
    loss β a b c = β ^ 2 / 2 * (a ^ 2 + b ^ 2 + c ^ 2) + β ^ 3 * (a * b * c) := by
  have hc : c = -a - b := by linarith
  rw [hc]
  unfold loss
  ring

theorem loss_one_negative {β r a b : ℝ}
    (hβ : 0 ≤ β) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hab : a + b = r)
    (hβa : β * a ≤ 1) (hβb : β * b ≤ 1) :
    lossFactor β / 6 * ((-r) ^ 2 + a ^ 2 + b ^ 2) ≤ loss β (-r) a b := by
  let N := r ^ 2 + a ^ 2 + b ^ 2
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hgap : 0 ≤ N - 6 * a * b := by
    dsimp [N]
    rw [← hab]
    nlinarith only [sq_nonneg (a - b)]
  have hprod := mul_nonneg (mul_nonneg (pow_nonneg hβ 3) hr) hgap
  have hfirst : β ^ 2 / 6 * (3 - β * r) * N ≤ loss β (-r) a b := by
    rw [loss_identity (by linarith)]
    dsimp [N] at *
    nlinarith only [hprod]
  have hβr : β * r ≤ 2 := by
    calc
      β * r = β * a + β * b := by rw [← hab]; ring
      _ ≤ 2 := by linarith
  have hβr' : β * r ≤ β := by simpa using mul_le_mul_of_nonneg_left hr1 hβ
  have hmax : max 1 (3 - β) ≤ 3 - β * r := max_le (by linarith) (by linarith)
  have hfactor : lossFactor β ≤ β ^ 2 * (3 - β * r) := by
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left hmax (sq_nonneg β))
  have hscaled := mul_le_mul_of_nonneg_right hfactor (div_nonneg hN (by norm_num : (0 : ℝ) ≤ 6))
  calc
    lossFactor β / 6 * ((-r) ^ 2 + a ^ 2 + b ^ 2) = lossFactor β * (N / 6) := by
      dsimp [N]
      ring
    _ ≤ (β ^ 2 * (3 - β * r)) * (N / 6) := hscaled
    _ = β ^ 2 / 6 * (3 - β * r) * N := by ring
    _ ≤ loss β (-r) a b := hfirst

theorem other_eigenvalues_nonneg {a b c : ℝ}
    (htrace : a + b + c = 0) (ha : a < 0) (hprod : a * b * c < 0) :
    0 ≤ b ∧ 0 ≤ c := by
  constructor
  · by_contra hb
    have hb' : b < 0 := lt_of_not_ge hb
    have hc : 0 < c := by linarith
    have hp := mul_pos (mul_pos_of_neg_of_neg ha hb') hc
    linarith
  · by_contra hc
    have hc' : c < 0 := lt_of_not_ge hc
    have hb : 0 < b := by linarith
    have hp := mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos ha hb) hc'
    linarith

/-- The full determinant-loss bound before the first conjugate point. The
semidefinite compression is expressed by `β*a, β*b, β*c ≤ 1`. No positive
definiteness or inversion at its singular endpoint is required. -/
theorem preconjugate_loss {β a b c : ℝ}
    (hβ : 0 ≤ β) (htrace : a + b + c = 0)
    (ha : -1 ≤ a) (hb : -1 ≤ b) (hc : -1 ≤ c)
    (hβa : β * a ≤ 1) (hβb : β * b ≤ 1) (hβc : β * c ≤ 1) :
    lossFactor β / 6 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ loss β a b c := by
  by_cases hprod : 0 ≤ a * b * c
  · have hmax : max (1 : ℝ) (3 - β) ≤ 3 := max_le (by norm_num) (by linarith)
    have hfactor : lossFactor β ≤ 3 * β ^ 2 := by
      calc
        _ ≤ β ^ 2 * max 1 (3 - β) := min_le_right _ _
        _ ≤ β ^ 2 * 3 := mul_le_mul_of_nonneg_left hmax (sq_nonneg β)
        _ = _ := by ring
    have hN : 0 ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 6 := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hfactor hN
    have hp := mul_nonneg (pow_nonneg hβ 3) hprod
    rw [loss_identity htrace]
    nlinarith only [hscaled, hp]
  · have hprod' : a * b * c < 0 := lt_of_not_ge hprod
    by_cases haneg : a < 0
    · obtain ⟨hb0, hc0⟩ := other_eigenvalues_nonneg htrace haneg hprod'
      simpa only [neg_neg] using loss_one_negative hβ (neg_nonneg.mpr haneg.le)
        (by linarith : -a ≤ 1) hb0 hc0 (by linarith : b + c = -a) hβb hβc
    · by_cases hbneg : b < 0
      · have hp : b * a * c < 0 := by nlinarith only [hprod']
        obtain ⟨ha0, hc0⟩ := other_eigenvalues_nonneg (by linarith) hbneg hp
        have h := loss_one_negative hβ (neg_nonneg.mpr hbneg.le)
          (by linarith : -b ≤ 1) ha0 hc0 (by linarith : a + c = -b) hβa hβc
        simp only [neg_neg] at h
        unfold loss at *
        nlinarith only [h]
      · have ha0 : 0 ≤ a := le_of_not_gt haneg
        have hb0 : 0 ≤ b := le_of_not_gt hbneg
        have hcneg : c < 0 := by
          by_contra h
          exact hprod (mul_nonneg (mul_nonneg ha0 hb0) (le_of_not_gt h))
        have h := loss_one_negative hβ (neg_nonneg.mpr hcneg.le)
          (by linarith : -c ≤ 1) ha0 hb0 (by linarith : a + b = -c) hβa hβb
        simp only [neg_neg] at h
        unfold loss at *
        nlinarith only [h]

/-- The eigenvalue box and trace condition give the global squared-norm cap. -/
theorem norm_sq_le_six {a b c : ℝ} (htrace : a + b + c = 0)
    (ha : a ∈ Set.Icc (-1 : ℝ) 2) (hb : b ∈ Set.Icc (-1 : ℝ) 2)
    (hc : c ∈ Set.Icc (-1 : ℝ) 2) : a ^ 2 + b ^ 2 + c ^ 2 ≤ 6 := by
  have h1 := mul_nonneg (by linarith [ha.1] : 0 ≤ a + 1) (by linarith [ha.2] : 0 ≤ 2 - a)
  have h2 := mul_nonneg (by linarith [hb.1] : 0 ≤ b + 1) (by linarith [hb.2] : 0 ≤ 2 - b)
  have h3 := mul_nonneg (by linarith [hc.1] : 0 ≤ c + 1) (by linarith [hc.2] : 0 ≤ 2 - c)
  nlinarith

/-- After conjugacy the truncated determinant is zero, and the same bound
follows from the norm cap. -/
theorem postconjugate_loss {β a b c : ℝ}
    (htrace : a + b + c = 0)
    (ha : a ∈ Set.Icc (-1 : ℝ) 2) (hb : b ∈ Set.Icc (-1 : ℝ) 2)
    (hc : c ∈ Set.Icc (-1 : ℝ) 2) :
    lossFactor β / 6 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 1 := by
  have hN := norm_sq_le_six htrace ha hb hc
  have hfactor : lossFactor β ≤ 1 := min_le_left _ _
  have h0 : 0 ≤ lossFactor β := le_min (by norm_num)
    (mul_nonneg (sq_nonneg β) (le_trans (by norm_num) (le_max_left _ _)))
  nlinarith [mul_le_mul_of_nonneg_left hN h0]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the discrete Jacobi comparison to its determinant limit. -/

namespace PositiveEinsteinFour.Jacobi

open Filter
open scoped Matrix.Norms.Frobenius

noncomputable section

/-- A finite determinant compression remains valid in the limit, including
when the limiting three-dimensional compression is singular. -/
theorem compression_comparison_limit
    {a b : ℕ → ℝ} {P : ℕ → Matrix (Fin 3) (Fin 3) ℝ}
    {D d : ℝ} {Q : Matrix (Fin 3) (Fin 3) ℝ}
    (hd : 0 < d) (ha : Tendsto a atTop (nhds D)) (hb : Tendsto b atTop (nhds d))
    (hP : Tendsto P atTop (nhds Q))
    (hcomp : ∀ᶠ (N : ℕ) in atTop, a N / b N ≤ (P N).det) :
    D ≤ d * Q.det := by
  have hc : Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => A.det) :=
    continuous_id.matrix_det
  have hlim := le_of_tendsto_of_tendsto (ha.div hb hd.ne') ((hc.tendsto Q).comp hP) hcomp
  have hm := (div_le_iff₀ hd).mp hlim
  simpa only [mul_comm] using hm

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_VolumeConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational integrations for the two volume margins. -/

namespace PositiveEinsteinFour.VolumeConstants

open MeasureTheory intervalIntegral

noncomputable section

def sineLower (z : ℝ) : ℝ :=
  (157 / 50) * z - (22 / 7) ^ 3 * z ^ 3 / 6 +
    (157 / 50) ^ 5 * z ^ 5 / 120 - (22 / 7) ^ 7 * z ^ 7 / 5040

def initialFactor (u : ℝ) : ℝ := u ^ 4 * (3 + 5 * u ^ 2 + 6 * u ^ 4)

def upperIntegrand (u : ℝ) : ℝ :=
  (9 * (157 / 50) / 48) * initialFactor u * (1 - u ^ 2 / 2) * sineLower u ^ 3

def upperIntegrandMiddle (u : ℝ) : ℝ :=
  (9 * (157 / 50) / 48) * initialFactor u * (1 - u ^ 2 / 2) * sineLower (1 - u) ^ 3

def upperIntegrandEnd (u : ℝ) : ℝ :=
  (9 * (157 / 50) / 48) * (15 / 16) * (1 - u ^ 2 / 2) * sineLower (1 - u) ^ 3

def lowerIntegrand (u : ℝ) : ℝ :=
  ((157 / 50) ^ 3 / 27) * u ^ 2 * (u ^ 4 / 2 + u ^ 6 / 3) * sineLower u

def lowerIntegrandEnd (u : ℝ) : ℝ :=
  ((157 / 50) ^ 3 / 27) * u ^ 2 * (u ^ 4 / 2 + u ^ 6 / 3) * sineLower (1 - u)

def polynomial (coefficients : List ℝ) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range coefficients.length, coefficients[i]! * u ^ i

theorem integral_polynomial (coefficients : List ℝ) (a b : ℝ) :
    (∫ u in a..b, polynomial coefficients u) =
      ∑ i ∈ Finset.range coefficients.length,
        coefficients[i]! * ((b ^ (i + 1) - a ^ (i + 1)) / (i + 1)) := by
  unfold polynomial
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul, integral_pow]
  · intro i _
    exact (continuous_const.mul (continuous_id.pow i)).intervalIntegrable a b

def coefficients0 : List ℝ :=
  [0,
   0,
   0,
   0,
   0,
   0,
   0,
   (5468158809 / 100000000),
   0,
   (-14166629531997 / 68600000000),
   0,
   (960982998880232655221241 / 2941225000000000000000),
   0,
   (-2477790121534872143891522759 / 6053041050000000000000000),
   0,
   (76070849162427929784227247232305837661 / 111224629293750000000000000000000000),
   0,
   (-80687966312912830364670348804097846493713 / 76300095695512500000000000000000000000),
   0,
   (530141759701830330658619390139064143457643230547203 / 467338086135014062500000000000000000000000000000),
   0,
   (-265926664095500074079744225037118360727066339277055199 / 320593927088619646875000000000000000000000000000000),
   0,
   (57912062546271973038629068001560058927500211952690629 / 137397397323694134375000000000000000000000000000000),
   0,
   (-3617417489337778371115590425933961819909557256209842614427 / 24246999596602936822626562500000000000000000000000000000),
   0,
   (18568015271215163475908534489261176616615783849 / 519578562784348646199140625000000000000000000),
   0,
   (-138076171696324940676707316696759149 / 25978928139217432309957031250000000),
   0,
   (18589427859976498174242032 / 48493999193205873645253125)]

theorem expansion0 (u : ℝ) :
    upperIntegrand u = polynomial coefficients0 u := by
  norm_num [upperIntegrand, upperIntegrandMiddle, upperIntegrandEnd,
    lowerIntegrand, lowerIntegrandEnd, sineLower, initialFactor,
    polynomial, coefficients0, Finset.sum_range_succ]
  ring

/-- Row 1 of the manuscript's rational integration table. -/
theorem row1_lower : (11869 / 1000000 : ℝ) <
    ∫ u in 0..(1 / 2), upperIntegrand u := by
  simp_rw [expansion0]
  rw [integral_polynomial]
  norm_num [coefficients0, Finset.sum_range_succ]

def coefficients1 : List ℝ :=
  [0,
   0,
   0,
   0,
   (-32489970050190226244209188999117595886053789407385573 / 24246999596602936822626562500000000000000000000000000000),
   (39389572331865754212924541821980430988558211658197939 / 230923805681932731644062500000000000000000000000000000),
   (-152936525363829791007727599337777151344567622471072087143 / 20783142511373945847965625000000000000000000000000000000),
   (52061702753007143404015587128584733858388662129066470157 / 461847611363865463288125000000000000000000000000000000),
   (-24391004001114758205199076583149934460520552086295020363 / 106036441384560948203906250000000000000000000000000000),
   (1954653378050289458355988027950510969623711762630020421053 / 5195785627843486461991406250000000000000000000000000000),
   (-26843904298836167711169111905063343332592953802349848664987 / 24246999596602936822626562500000000000000000000000000000),
   (162139240686560090735418213131435830559670829413517458725999 / 72740998789808810467879687500000000000000000000000000000),
   (-2307294752003582332093707053016855909378667029264630127441 / 692771417045798194932187500000000000000000000000000000),
   (2572448629749606021828455535732249164553694393137624018397 / 494836726461284424951562500000000000000000000000000000),
   (-14426411231325546714139805283267159458888082602741475858301 / 1731928542614495487330468750000000000000000000000000000),
   (60682404315382983161608184047903399481512287013623567902657 / 5195785627843486461991406250000000000000000000000000000),
   (-5282691316468325282346798056085760195748097405324196320431 / 384873009469887886073437500000000000000000000000000000),
   (224494830751632054320491601109078021362234779451764131863753 / 14548199757961762093575937500000000000000000000000000000),
   (-1307399041882766705252843759033326644088873688511690966454039 / 72740998789808810467879687500000000000000000000000000000),
   (62213129667690217032603070753221733826545861970423961978629 / 3463857085228990974660937500000000000000000000000000000),
   (-35677710229844493624828371300172083855725026056682170094301 / 2597892813921743230995703125000000000000000000000000000),
   (8194743680512969938273255563742137338227631386612751739597 / 865964271307247743665234375000000000000000000000000000),
   (-363914503632345455411306898659774561733247341962402614427 / 55421713363663855594575000000000000000000000000000000),
   (16691172251190693473637668766996268331885966680568664228001 / 6927714170457981949321875000000000000000000000000000000),
   (32511890503421938312615959633467697256066277967603416470157 / 14548199757961762093575937500000000000000000000000000000),
   (-33412981094452468942693484890459928269159539190703385795191 / 8082333198867645607542187500000000000000000000000000000),
   (1613787159729359519663161326713429788482468325433 / 519578562784348646199140625000000000000000000),
   (-729332223509038268924896822786344887036615783849 / 519578562784348646199140625000000000000000000),
   (3532761101059370151190735414253858723 / 8659642713072477436652343750000000),
   (-1953234462551031103925521283303240851 / 25978928139217432309957031250000000),
   (18589427859976498174242032 / 2309238056819327316440625),
   (-18589427859976498174242032 / 48493999193205873645253125)]

theorem expansion1 (u : ℝ) :
    upperIntegrandMiddle u = polynomial coefficients1 u := by
  norm_num [upperIntegrand, upperIntegrandMiddle, upperIntegrandEnd,
    lowerIntegrand, lowerIntegrandEnd, sineLower, initialFactor,
    polynomial, coefficients1, Finset.sum_range_succ]
  ring

/-- Row 2 of the manuscript's rational integration table. -/
theorem row2_lower : (30175 / 1000000 : ℝ) <
    ∫ u in (1 / 2)..(5 / 8), upperIntegrandMiddle u := by
  simp_rw [expansion1]
  rw [integral_polynomial]
  norm_num [coefficients1, Finset.sum_range_succ]

def coefficients2 : List ℝ :=
  [(-32489970050190226244209188999117595886053789407385573 / 77590398709129397832405000000000000000000000000000000000),
   (39389572331865754212924541821980430988558211658197939 / 738956178182184741261000000000000000000000000000000000),
   (-356743592615435544930550367824816294484370939801143584757 / 155180797418258795664810000000000000000000000000000000000),
   (155791212535702772669917515967534397265280404270617431081 / 4433737069093108447566000000000000000000000000000000000),
   (-574700220350325047622048992701852865238307666538197939 / 8445213464939254185840000000000000000000000000000000),
   (1305581025262950893639229265028575823094965488552056759389 / 22168685345465542237830000000000000000000000000000000000),
   (-336896449182978664276684501647455334078990413689191412177 / 1477912356364369482522000000000000000000000000000000000),
   (9106184846534048812325211986432936440196628956699380383199 / 17242310824250977296090000000000000000000000000000000000),
   (-775557342241476680933613385153163213287386313406065119349 / 1477912356364369482522000000000000000000000000000000000),
   (3889162346550773817734450119794652399999323973490706136939 / 6207231896730351826592400000000000000000000000000000000),
   (-9403272631258636634972783818271965826999320055046177694723 / 7389561781821847412610000000000000000000000000000000000),
   (196252529469126031412969099618934712302533490077103426793 / 126678201974088812787600000000000000000000000000000000),
   (-24805360272892371479370044363588957989847563618422691713673 / 22168685345465542237830000000000000000000000000000000000),
   (1458816547731135009969246850652721399268036735783418758697 / 1477912356364369482522000000000000000000000000000000000),
   (-7490641635676162569615536056516960857748910979236924445259 / 6207231896730351826592400000000000000000000000000000000),
   (917498110852759420068370732071346826928765905679821695823 / 1055651683117406773230000000000000000000000000000000000),
   (-146640273705864590036332759068743356506591961450614204809 / 3448462164850195459218000000000000000000000000000000000),
   (-3439660289225623498428112210713894071575619226464769399313 / 7389561781821847412610000000000000000000000000000000000),
   (68474399625964999233273697376225564396784205973 / 158347752467611015984500000000000000000000000),
   (-77424115974951411284889015440513800687401753761 / 369478089091092370630500000000000000000000000),
   (3474669138996943594396229064253858723 / 55421713363663855594575000000000000),
   (-4538183091931597056894714211040895319 / 387951993545646989162025000000000000),
   (1161839241248531135890127 / 923695222727730926576250),
   (-1161839241248531135890127 / 19397599677282349458101250)]

theorem expansion2 (u : ℝ) :
    upperIntegrandEnd u = polynomial coefficients2 u := by
  norm_num [upperIntegrand, upperIntegrandMiddle, upperIntegrandEnd,
    lowerIntegrand, lowerIntegrandEnd, sineLower, initialFactor,
    polynomial, coefficients2, Finset.sum_range_succ]
  ring

/-- Row 3 of the manuscript's rational integration table. -/
theorem row3_lower : (39518 / 1000000 : ℝ) <
    ∫ u in (5 / 8)..1, upperIntegrandEnd u := by
  simp_rw [expansion2]
  rw [integral_polynomial]
  norm_num [coefficients2, Finset.sum_range_succ]

theorem upper_margin : (3 / 40 : ℝ) <
    (∫ u in (0 : ℝ)..(1 / 2), upperIntegrand u) +
    (∫ u in (1 / 2 : ℝ)..(5 / 8), upperIntegrandMiddle u) +
    (∫ u in (5 / 8 : ℝ)..1, upperIntegrandEnd u) := by
  linarith [row1_lower, row2_lower, row3_lower]

end

end PositiveEinsteinFour.VolumeConstants

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RadialCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison of the piecewise polynomial integration weight with the exact
Jacobi determinant-loss coefficient. The variable is `u = t / pi`. -/

namespace PositiveEinsteinFour.Jacobi

open VolumeConstants

noncomputable section

def radialLower (u : ℝ) : ℝ :=
  if u ≤ 5 / 8 then initialFactor u else 15 / 16

theorem small_parameter_bound {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 25 / 64) :
    x ^ 2 * (3 + 5 * x + 6 * x ^ 2) ≤ lossFactor (x / (1 - x)) := by
  have hden : 0 < 1 - x := by linarith
  have hcap : x ^ 2 * (3 + 5 * x + 6 * x ^ 2) ≤ 1 := by
    calc
      _ ≤ (25 / 64 : ℝ) ^ 2 * (3 + 5 * (25 / 64) + 6 * (25 / 64) ^ 2) := by
        gcongr
      _ ≤ 1 := by norm_num
  have hid : (1 - x) ^ 3 *
      ((x / (1 - x)) ^ 2 * (3 - x / (1 - x)) - x ^ 2 * (3 + 5 * x + 6 * x ^ 2)) =
      x ^ 5 * (3 - 2 * x) * (2 - 3 * x) := by
    field_simp [ne_of_gt hden]
    ring
  have hpos : 0 ≤ x ^ 5 * (3 - 2 * x) * (2 - 3 * x) := by
    apply mul_nonneg
    · exact mul_nonneg (pow_nonneg hx _) (by linarith)
    · linarith
  have hdiff : x ^ 2 * (3 + 5 * x + 6 * x ^ 2) ≤
      (x / (1 - x)) ^ 2 * (3 - x / (1 - x)) := by
    have hproduct : 0 ≤ (1 - x) ^ 3 *
        ((x / (1 - x)) ^ 2 * (3 - x / (1 - x)) - x ^ 2 * (3 + 5 * x + 6 * x ^ 2)) := by
      rwa [hid]
    have h := nonneg_of_mul_nonneg_right hproduct (pow_pos hden 3)
    linarith
  apply le_min hcap
  exact hdiff.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _))

theorem large_parameter_bound {β : ℝ} (hβ : 25 / 39 ≤ β) :
    (15 / 16 : ℝ) ≤ lossFactor β := by
  have hβ0 : 0 ≤ β := by linarith
  apply le_min (by norm_num)
  by_cases hβ1 : 1 ≤ β
  · have hs : 1 ≤ β ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) (3 - β)) (sq_nonneg β)
    nlinarith only [hs, hm]
  · have hβ1' : β ≤ 1 := (lt_of_not_ge hβ1).le
    have hs : β ^ 2 ≤ β := by nlinarith
    have hbr : β * (25 / 39) ≤ 25 / 39 := by linarith
    have hcoef : 0 ≤ 3 * (β + 25 / 39) - β ^ 2 - β * (25 / 39) - (25 / 39) ^ 2 := by
      nlinarith
    have hp := mul_nonneg (sub_nonneg.mpr hβ) hcoef
    have hcubic : (15 / 16 : ℝ) ≤ β ^ 2 * (3 - β) := by nlinarith only [hp]
    exact hcubic.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _))

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SineEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analytic comparison underlying the rational radial integrals. The
alternating seventh-degree sine bound is proved by successive derivatives,
then compared with the exact rational polynomial used in `VolumeConstants`. -/

namespace PositiveEinsteinFour.VolumeConstants

noncomputable section

theorem nonneg_of_derivative {f d : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (d x) x)
    (hd0 : ∀ x, 0 ≤ x → 0 ≤ d x) (hf0 : 0 ≤ f 0) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
    · intro x _
      exact (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      exact hd0 x hx.le
  exact hf0.trans (hmono (by simp) hx hx)

theorem cos_fourth_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have hd (t : ℝ) : HasDerivAt (fun z => 1 - z ^ 2 / 2 + z ^ 4 / 24 - Real.cos z)
      (Real.sin t - t + t ^ 3 / 6) t := by
    convert (((hasDerivAt_const t (1 : ℝ)).sub
      (((hasDerivAt_id t).pow 2).div_const 2)).add
      (((hasDerivAt_id t).pow 4).div_const 24)).sub (Real.hasDerivAt_cos t) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (try simp only [id_eq]; ring)
  have h := nonneg_of_derivative hd (fun t ht => by linarith [Real.sin_ge_sub_cube ht])
    (by norm_num) hx
  linarith

theorem sin_fifth_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have hd (t : ℝ) : HasDerivAt (fun z => z - z ^ 3 / 6 + z ^ 5 / 120 - Real.sin z)
      (1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t) t := by
    convert (((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 3).div_const 6)).add
      (((hasDerivAt_id t).pow 5).div_const 120)).sub (Real.hasDerivAt_sin t) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (try simp only [id_eq]; ring)
  have h := nonneg_of_derivative hd (fun t ht => by linarith [cos_fourth_upper ht])
    (by norm_num) hx
  linarith

theorem cos_sixth_lower {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have hd (t : ℝ) : HasDerivAt
      (fun z => Real.cos z - (1 - z ^ 2 / 2 + z ^ 4 / 24 - z ^ 6 / 720))
      (t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t) t := by
    convert (Real.hasDerivAt_cos t).sub ((((hasDerivAt_const t (1 : ℝ)).sub
      (((hasDerivAt_id t).pow 2).div_const 2)).add
      (((hasDerivAt_id t).pow 4).div_const 24)).sub
      (((hasDerivAt_id t).pow 6).div_const 720)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (try simp only [id_eq]; ring)
  have h := nonneg_of_derivative hd (fun t ht => by linarith [sin_fifth_upper ht])
    (by norm_num) hx
  linarith

theorem sin_seventh_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  have hd (t : ℝ) : HasDerivAt
      (fun z => Real.sin z - (z - z ^ 3 / 6 + z ^ 5 / 120 - z ^ 7 / 5040))
      (Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)) t := by
    convert (Real.hasDerivAt_sin t).sub ((((hasDerivAt_id t).sub
      (((hasDerivAt_id t).pow 3).div_const 6)).add
      (((hasDerivAt_id t).pow 5).div_const 120)).sub
      (((hasDerivAt_id t).pow 7).div_const 5040)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (try simp only [id_eq]; ring)
  have h := nonneg_of_derivative hd (fun t ht => by linarith [cos_sixth_lower ht])
    (by norm_num) hx
  linarith

/-- The lower polynomial in the paper is below the sine of the true angle. -/
theorem sineLower_le_sin {z : ℝ} (hz : 0 ≤ z) : sineLower z ≤ Real.sin (Real.pi * z) := by
  have hpi0 : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hpi1 : Real.pi ≤ (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hsmall : (157 / 50 : ℝ) * z ≤ Real.pi * z := mul_le_mul_of_nonneg_right hpi0 hz
  have hlarge : Real.pi * z ≤ (22 / 7 : ℝ) * z := mul_le_mul_of_nonneg_right hpi1 hz
  have hpoly : sineLower z = (157 / 50 * z) - (22 / 7 * z) ^ 3 / 6 +
      (157 / 50 * z) ^ 5 / 120 - (22 / 7 * z) ^ 7 / 5040 := by
    unfold sineLower
    ring
  rw [hpoly]
  calc
    _ ≤ (Real.pi * z) - (Real.pi * z) ^ 3 / 6 +
        (Real.pi * z) ^ 5 / 120 - (Real.pi * z) ^ 7 / 5040 := by
      gcongr
    _ ≤ Real.sin (Real.pi * z) := sin_seventh_lower (mul_nonneg Real.pi_pos.le hz)

/-- Positivity of the same lower polynomial on the half interval used in the
reflection argument. -/
theorem sineLower_linear {z : ℝ} (hz : 0 ≤ z) (hz2 : z ≤ 1 / 2) :
    (9 / 5) * z ≤ sineLower z := by
  have hsquare : z ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
  have hsix : z ^ 6 ≤ (1 / 64 : ℝ) := by
    have h := pow_le_pow_left₀ (sq_nonneg z) hsquare 3
    nlinarith only [h]
  have hcoefficient : (9 / 5 : ℝ) ≤
      157 / 50 - (22 / 7) ^ 3 * z ^ 2 / 6 +
        (157 / 50) ^ 5 * z ^ 4 / 120 - (22 / 7) ^ 7 * z ^ 6 / 5040 := by
    nlinarith only [hsquare, hsix, pow_nonneg hz 4]
  have h := mul_le_mul_of_nonneg_left hcoefficient hz
  unfold sineLower
  nlinarith only [h]

theorem sineLower_nonneg {z : ℝ} (hz : 0 ≤ z) (hz2 : z ≤ 1 / 2) :
    0 ≤ sineLower z := (by positivity : 0 ≤ (9 / 5 : ℝ) * z).trans (sineLower_linear hz hz2)

/-- Reflection makes the positive polynomial bound available on all of [0,1]. -/
theorem reflected_sineLower {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ sineLower (min u (1 - u)) ∧
      sineLower (min u (1 - u)) ≤ Real.sin (Real.pi * u) := by
  by_cases hh : u ≤ 1 / 2
  · rw [min_eq_left (by linarith)]
    exact ⟨sineLower_nonneg hu hh, sineLower_le_sin hu⟩
  · rw [min_eq_right (by linarith)]
    have hnonneg : 0 ≤ 1 - u := by linarith
    refine ⟨sineLower_nonneg hnonneg (by linarith), ?_⟩
    have h := sineLower_le_sin hnonneg
    rwa [mul_sub, mul_one, Real.sin_pi_sub] at h

end

end PositiveEinsteinFour.VolumeConstants

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RadialIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two analytic integral margins in the volume comparison. All numerical
bounds here follow from exact polynomial integrals and the proved sine bound;
no numerical integration or decimal error premise is used. -/

namespace PositiveEinsteinFour.VolumeConstants

open MeasureTheory

noncomputable section

def upperKernel (u : ℝ) : ℝ :=
  (9 * Real.pi / 48) * initialFactor u * (1 - u ^ 2 / 2) * Real.sin (Real.pi * u) ^ 3

def upperKernelEnd (u : ℝ) : ℝ :=
  (9 * Real.pi / 48) * (15 / 16) * (1 - u ^ 2 / 2) * Real.sin (Real.pi * u) ^ 3

theorem upper_comparison {u z A : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hA : 0 ≤ A)
    (hz0 : 0 ≤ sineLower z) (hz : sineLower z ≤ Real.sin (Real.pi * u)) :
    (9 * (157 / 50) / 48) * A * (1 - u ^ 2 / 2) * sineLower z ^ 3 ≤
      (9 * Real.pi / 48) * A * (1 - u ^ 2 / 2) * Real.sin (Real.pi * u) ^ 3 := by
  have hpi : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hw : 0 ≤ 1 - u ^ 2 / 2 := by nlinarith
  gcongr

theorem sine_reflected_bound {u : ℝ} (hu : 1 / 2 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ sineLower (1 - u) ∧ sineLower (1 - u) ≤ Real.sin (Real.pi * u) := by
  have h := reflected_sineLower (by linarith : 0 ≤ u) hu1
  rwa [min_eq_right (by linarith)] at h

theorem upper_integral_first :
    (∫ u in (0 : ℝ)..(1 / 2), upperIntegrand u) ≤
      ∫ u in (0 : ℝ)..(1 / 2), upperKernel u := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; unfold upperIntegrand initialFactor sineLower; fun_prop)
    (by apply Continuous.intervalIntegrable; unfold upperKernel initialFactor; fun_prop)
  intro u hu
  have hsin := sineLower_le_sin hu.1
  have hnonneg := sineLower_nonneg hu.1 hu.2
  exact upper_comparison hu.1 (by linarith [hu.2])
    (by unfold initialFactor; positivity) hnonneg hsin

theorem upper_integral_middle :
    (∫ u in (1 / 2 : ℝ)..(5 / 8), upperIntegrandMiddle u) ≤
      ∫ u in (1 / 2 : ℝ)..(5 / 8), upperKernel u := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; unfold upperIntegrandMiddle initialFactor sineLower; fun_prop)
    (by apply Continuous.intervalIntegrable; unfold upperKernel initialFactor; fun_prop)
  intro u hu
  have hsin := sine_reflected_bound hu.1 (by linarith [hu.2])
  exact upper_comparison (by linarith [hu.1]) (by linarith [hu.2])
    (by unfold initialFactor; positivity) hsin.1 hsin.2

theorem upper_integral_end :
    (∫ u in (5 / 8 : ℝ)..1, upperIntegrandEnd u) ≤
      ∫ u in (5 / 8 : ℝ)..1, upperKernelEnd u := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; unfold upperIntegrandEnd sineLower; fun_prop)
    (by apply Continuous.intervalIntegrable; unfold upperKernelEnd; fun_prop)
  intro u hu
  have hsin := sine_reflected_bound (by linarith [hu.1]) hu.2
  exact upper_comparison (by linarith [hu.1]) hu.2 (by norm_num) hsin.1 hsin.2

/-- The actual upper-volume deficit coefficient exceeds the constant required
by the classification argument. The two pieces are precisely the integral
of the manuscript's piecewise weight. -/
theorem analytic_upper_margin : (3 / 40 : ℝ) <
    (∫ u in (0 : ℝ)..(5 / 8), upperKernel u) +
      ∫ u in (5 / 8 : ℝ)..1, upperKernelEnd u := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := upperKernel) (μ := volume)
    (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) (c := (5 / 8 : ℝ))
    (by apply Continuous.intervalIntegrable; unfold upperKernel initialFactor; fun_prop)
    (by apply Continuous.intervalIntegrable; unfold upperKernel initialFactor; fun_prop)
  linarith [upper_margin, upper_integral_first, upper_integral_middle, upper_integral_end]

end

end PositiveEinsteinFour.VolumeConstants

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_VolumeAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration of the radial determinant deficit using the radial
comparison and polar volume formula. -/

namespace PositiveEinsteinFour.VolumeConstants

open MeasureTheory

noncomputable section

theorem integral_sine_cube :
    (∫ u in (0 : ℝ)..1, Real.sin (Real.pi * u) ^ 3) = 4 / (3 * Real.pi) := by
  have hd (u : ℝ) : HasDerivAt
      (fun z => -Real.cos (Real.pi * z) / Real.pi +
        Real.cos (Real.pi * z) ^ 3 / (3 * Real.pi))
      (Real.sin (Real.pi * u) ^ 3) u := by
    have hc := ((hasDerivAt_id u).const_mul Real.pi).cos
    refine ((hc.neg.div_const Real.pi).add
      ((hc.pow 3).div_const (3 * Real.pi))).congr_deriv ?_
    · simp only [id_eq]
      field_simp [Real.pi_ne_zero]
      norm_num only [Nat.reduceSub, Nat.cast_ofNat]
      linear_combination (-3) * Real.sin (Real.pi * u) *
        Real.sin_sq_add_cos_sq (Real.pi * u)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp [Real.cos_pi]
  ring

/-- Endpoint values have no effect on the volume integral. This form only
requires the radial estimate on the open comparison intervals. -/
theorem volume_ratio_upper_of_radial_comparison_open {D : ℝ → ℝ} {V s : ℝ}
    (hs : 0 ≤ s)
    (hD0 : IntervalIntegrable D volume 0 (5 / 8))
    (hD1 : IntervalIntegrable D volume (5 / 8) 1)
    (hpolar : V ≤ (3 * Real.pi / 4) *
      ((∫ u in (0 : ℝ)..(5 / 8), D u) + ∫ u in (5 / 8 : ℝ)..1, D u))
    (hfirst : ∀ u ∈ Set.Ioo (0 : ℝ) (5 / 8),
      D u ≤ Real.sin (Real.pi * u) ^ 3 - (4 / (3 * Real.pi)) * s * upperKernel u)
    (hlast : ∀ u ∈ Set.Ioo (5 / 8 : ℝ) 1,
      D u ≤ Real.sin (Real.pi * u) ^ 3 - (4 / (3 * Real.pi)) * s * upperKernelEnd u) :
    V ≤ 1 - (3 / 40) * s := by
  have hsin0 : IntervalIntegrable (fun u => Real.sin (Real.pi * u) ^ 3)
      volume 0 (5 / 8) := by apply Continuous.intervalIntegrable; fun_prop
  have hsin1 : IntervalIntegrable (fun u => Real.sin (Real.pi * u) ^ 3)
      volume (5 / 8) 1 := by apply Continuous.intervalIntegrable; fun_prop
  have hk0 : IntervalIntegrable upperKernel volume 0 (5 / 8) := by
    apply Continuous.intervalIntegrable
    unfold upperKernel initialFactor
    fun_prop
  have hk1 : IntervalIntegrable upperKernelEnd volume (5 / 8) 1 := by
    apply Continuous.intervalIntegrable
    unfold upperKernelEnd
    fun_prop
  have h0 := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 5 / 8)
    hD0 (hsin0.sub (hk0.const_mul ((4 / (3 * Real.pi)) * s))) hfirst
  have h1 := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (5 / 8 : ℝ) ≤ 1)
    hD1 (hsin1.sub (hk1.const_mul ((4 / (3 * Real.pi)) * s))) hlast
  rw [intervalIntegral.integral_sub hsin0 (hk0.const_mul _),
    intervalIntegral.integral_const_mul] at h0
  rw [intervalIntegral.integral_sub hsin1 (hk1.const_mul _),
    intervalIntegral.integral_const_mul] at h1
  have hsum := intervalIntegral.integral_add_adjacent_intervals hsin0 hsin1
  rw [integral_sine_cube] at hsum
  have hnormalize : (3 * Real.pi / 4) * (4 / (3 * Real.pi)) = 1 := by
    field_simp [Real.pi_ne_zero]
  have hb := mul_le_mul_of_nonneg_left (add_le_add h0 h1)
    (show 0 ≤ 3 * Real.pi / 4 by positivity)
  have hmargin := mul_le_mul_of_nonneg_left analytic_upper_margin.le hs
  have hidentity (a b c d : ℝ) :
      (3 * Real.pi / 4) * ((a - (4 / (3 * Real.pi)) * s * b) +
        (c - (4 / (3 * Real.pi)) * s * d)) =
      (3 * Real.pi / 4) * (a + c) -
        ((3 * Real.pi / 4) * (4 / (3 * Real.pi))) * s * (b + d) := by ring
  rw [hidentity, hsum, hnormalize] at hb
  linarith only [hpolar, hb, hmargin]


end

end PositiveEinsteinFour.VolumeConstants

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The tautological orientation on the actual determinant-sign cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Matrix Set Filter _root_.Topology
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem bool_orientation_change (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (s : Bool) :
    (if 0 < a then s else !s) = decide (0 < a * b) ↔ s = decide (0 < b) := by
  rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hb with hb | hb
  · have hp := mul_pos_of_neg_of_neg ha hb
    cases s <;> simp [not_lt.mpr ha.le, not_lt.mpr hb.le, hp]
  · have hp := mul_neg_of_neg_of_pos ha hb
    cases s <;> simp [not_lt.mpr ha.le, hb, not_lt.mpr hp.le]
  · have hp := mul_neg_of_pos_of_neg ha hb
    cases s <;> simp [ha, not_lt.mpr hb.le, not_lt.mpr hp.le]
  · have hp := mul_pos ha hb
    cases s <;> simp [ha, hb, hp]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The sharp upper normalization needed by the polar volume estimate.
Arbitrarily fine ball covers with nearly optimal total Lebesgue measure
bound the unnormalized fourth Hausdorff measure. Only the upper bound is
needed; no isodiametric inequality or equality case is used. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal _root_.Topology

noncomputable section

theorem ball_normalization_product :
    ENNReal.ofReal (32 / Real.pi ^ 2) * ENNReal.ofReal (Real.pi ^ 2 / 2) = 16 := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h : (32 / Real.pi ^ 2) * (Real.pi ^ 2 / 2) = 16 := by field_simp; ring
  rw [h]
  norm_num

end
end PositiveEinsteinFour.Geometry
end


section

/-! Before the first conjugate point the Jacobi determinant is positive.
The proof removes the initial zero by `dslope`, then uses continuity and
invertibility on the whole closed interval. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix Set
open scoped _root_.Topology Matrix.Norms.L2Operator

noncomputable section

theorem positive_of_continuousOn_nonzero (f : ℝ → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hf : ContinuousOn f (Icc 0 t)) (hzero : 0 < f 0)
    (hne : ∀ s ∈ Icc 0 t, f s ≠ 0) : 0 < f t := by
  by_contra hnot
  have hle : f t ≤ 0 := le_of_not_gt hnot
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc' ht hf ⟨hle, hzero.le⟩
  exact hne s hs hfs

end
end PositiveEinsteinFour.Jacobi

end


section

/-! Rational Brezis--Kato tests with bounded derivatives.  Their exact
algebra relates the tested Dirichlet form to the square test, uniformly as
the truncation parameter tends to zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

def scalarKatoTest (lam s : ℝ) : ℝ := s ^ 3 / (1 + lam * s ^ 2)

def scalarKatoTestRate (lam s : ℝ) : ℝ :=
  s ^ 2 * (3 + lam * s ^ 2) / (1 + lam * s ^ 2) ^ 2

def scalarKatoSquareRate (lam s : ℝ) : ℝ :=
  s * (2 + lam * s ^ 2) / ((1 + lam * s ^ 2) * Real.sqrt (1 + lam * s ^ 2))

theorem scalarKato_den_pos {lam : ℝ} (hlam : 0 < lam) (s : ℝ) : 0 < 1 + lam * s ^ 2 :=
  add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hlam.le (sq_nonneg s))

theorem scalarKatoTest_smooth {lam : ℝ} (hlam : 0 < lam) : ContDiff ℝ ∞ (scalarKatoTest lam) := by
  exact (contDiff_id.pow 3).div
    (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2)))
    (fun s => (scalarKato_den_pos hlam s).ne')

theorem scalarKatoTestRate_nonneg {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    0 ≤ scalarKatoTestRate lam s := by
  unfold scalarKatoTestRate
  positivity

theorem scalarKatoTestRate_le {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    scalarKatoTestRate lam s ≤ 3 / lam := by
  unfold scalarKatoTestRate
  apply (div_le_div_iff₀ (sq_pos_of_pos (scalarKato_den_pos hlam s)) hlam).mpr
  have hx : 0 ≤ lam * s ^ 2 := mul_nonneg hlam.le (sq_nonneg s)
  nlinarith [sq_nonneg (lam * s ^ 2)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth nonpositive test detecting the negative set, with nonnegative
bounded derivative. It is admissible in the actual H1 closure. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter
open scoped _root_.Topology ContDiff NNReal

noncomputable section

def scalarNegativeTest (r : ℝ) : ℝ := -Real.smoothTransition (-r)

theorem scalarNegativeTest_smooth : ContDiff ℝ ∞ scalarNegativeTest :=
  (Real.smoothTransition.contDiff.comp contDiff_id.neg).neg

theorem scalarNegativeTest_nonpos (r : ℝ) : scalarNegativeTest r ≤ 0 :=
  neg_nonpos.mpr (Real.smoothTransition.nonneg _)

theorem scalarNegativeTest_eq_zero {r : ℝ} (hr : 0 ≤ r) : scalarNegativeTest r = 0 := by
  rw [scalarNegativeTest, Real.smoothTransition.zero_of_nonpos (neg_nonpos.mpr hr), neg_zero]

theorem scalarNegativeTest_neg {r : ℝ} (hr : r < 0) : scalarNegativeTest r < 0 :=
  neg_neg_of_pos (Real.smoothTransition.pos_of_pos (neg_pos.mpr hr))

theorem scalarNegativeTest_monotone : Monotone scalarNegativeTest := by
  intro a b hab
  exact neg_le_neg (Real.smoothTransition.monotone (neg_le_neg hab))

theorem scalarNegativeTest_deriv_nonneg (r : ℝ) : 0 ≤ deriv scalarNegativeTest r :=
  scalarNegativeTest_monotone.deriv_nonneg

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth bounded-derivative approximations of the subcritical power
s ↦ |s|^q s, for 0 < q < 2. Their derivative growth is uniformly quadratic. -/

namespace PositiveEinsteinFour.Geometry

open Filter
open scoped _root_.Topology ContDiff

noncomputable section

def scalarNonlinearTruncation (q ε s : ℝ) : ℝ :=
  s * (s ^ 2 + ε) ^ (q / 2) / (1 + ε * s ^ 2)

def scalarNonlinearTruncationDerivative (q ε s : ℝ) : ℝ :=
  (s ^ 2 + ε) ^ (q / 2) / (1 + ε * s ^ 2) *
    (1 + q * s ^ 2 / (s ^ 2 + ε) - 2 * ε * s ^ 2 / (1 + ε * s ^ 2))

theorem scalarNonlinearTruncation_smooth (q : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (scalarNonlinearTruncation q ε) := by
  have ha : ContDiff ℝ ∞ (fun s : ℝ => s ^ 2 + ε) := by fun_prop
  have hb : ContDiff ℝ ∞ (fun s : ℝ => 1 + ε * s ^ 2) := by fun_prop
  exact (contDiff_id.mul (ha.rpow_const_of_ne (fun s => ne_of_gt (by positivity)))).div hb
    (fun s => ne_of_gt (by positivity))

theorem scalarNonlinearTruncation_power_bound {q ε : ℝ}
    (hq : 0 < q) (hq2 : q < 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    (s ^ 2 + ε) ^ (q / 2) ≤ 1 + s ^ 2 := by
  by_cases hs : s ^ 2 + ε ≤ 1
  · exact (Real.rpow_le_one (by positivity) hs (by positivity)).trans
      (le_add_of_nonneg_right (sq_nonneg _))
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hs)
      (show q / 2 ≤ 1 by linarith)
    rw [Real.rpow_one] at h
    linarith

theorem scalarNonlinearTruncation_bracket_bound {q ε : ℝ}
    (hq : 0 < q) (hq2 : q < 2) (hε : 0 < ε) (s : ℝ) :
    |1 + q * s ^ 2 / (s ^ 2 + ε) - 2 * ε * s ^ 2 / (1 + ε * s ^ 2)| ≤ 5 := by
  have ha : 0 < s ^ 2 + ε := by positivity
  have hb : 0 < 1 + ε * s ^ 2 := by positivity
  have hA0 : 0 ≤ q * s ^ 2 / (s ^ 2 + ε) := by positivity
  have hA : q * s ^ 2 / (s ^ 2 + ε) ≤ q := (div_le_iff₀ ha).mpr (by nlinarith)
  have hB0 : 0 ≤ 2 * ε * s ^ 2 / (1 + ε * s ^ 2) := by positivity
  have hB : 2 * ε * s ^ 2 / (1 + ε * s ^ 2) ≤ 2 :=
    (div_le_iff₀ hb).mpr (by nlinarith)
  apply abs_le.mpr
  constructor <;> linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compactly supported smooth extension of the power on a positive
bounded interval. This is used only after the weak solution is positive. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter Metric
open scoped _root_.Topology ContDiff NNReal

noncomputable section

def positivePowerInner (a : ℝ) (ha : 0 < a) : ContDiffBump (0 : ℝ) where
  rIn := a / 4
  rOut := a / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def positivePowerOuter (B : ℝ) (hB : 0 ≤ B) : ContDiffBump (0 : ℝ) where
  rIn := B + 1
  rOut := B + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def positivePowerExtension (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B) (t : ℝ) : ℝ :=
  positivePowerOuter B hB t * (1 - positivePowerInner a ha t) * t ^ q

theorem positivePowerExtension_smooth (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B) :
    ContDiff ℝ ∞ (positivePowerExtension a B q ha hB) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t = 0
  · subst t
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hone := (positivePowerInner a ha).eventuallyEq_one
    filter_upwards [hone] with s hs
    simp only [positivePowerExtension, hs, Pi.one_apply, sub_self, mul_zero, zero_mul]
  · exact (((positivePowerOuter B hB).contDiff.contDiffAt.mul
      (contDiffAt_const.sub (positivePowerInner a ha).contDiff.contDiffAt)).mul
        (contDiffAt_id.rpow_const_of_ne ht))

theorem positivePowerExtension_compact (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B) :
    HasCompactSupport (positivePowerExtension a B q ha hB) :=
  ((positivePowerOuter B hB).hasCompactSupport.mul_right).mul_right

theorem positivePowerExtension_eq (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    {t : ℝ} (hat : a ≤ t) (htB : t ≤ B) :
    positivePowerExtension a B q ha hB t = t ^ q := by
  have ht : 0 < t := ha.trans_le hat
  have hinner : positivePowerInner a ha t = 0 := by
    apply ContDiffBump.zero_of_le_dist
    change a / 2 ≤ dist t 0
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    linarith
  have houter : positivePowerOuter B hB t = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    change dist t 0 ≤ B + 1
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    linarith
  simp only [positivePowerExtension, hinner, houter, sub_zero, one_mul]

theorem positivePowerExtension_deriv (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    {t : ℝ} (hat : a ≤ t) (htB : t ≤ B) :
    deriv (positivePowerExtension a B q ha hB) t = q * t ^ (q - 1) := by
  have ht : 0 < t := ha.trans_le hat
  have he : positivePowerExtension a B q ha hB =ᶠ[𝓝 t] (fun s : ℝ => s ^ q) := by
    filter_upwards [Ioo_mem_nhds (show a / 2 < t by linarith)
      (show t < B + 1 by linarith)] with s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hi : positivePowerInner a ha s = 0 := by
      apply ContDiffBump.zero_of_le_dist
      change a / 2 ≤ dist s 0
      rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
      exact hs.1.le
    have ho : positivePowerOuter B hB s = 1 := by
      apply ContDiffBump.one_of_mem_closedBall
      change dist s 0 ≤ B + 1
      rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
      exact hs.2.le
    simp only [positivePowerExtension, hi, ho, sub_zero, one_mul]
  exact ((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).congr_of_eventuallyEq he).deriv

end
end PositiveEinsteinFour.Geometry
end


section

/-! Dominated convergence for the two regularized moments in the Weyl
gap argument. All bounds are uniform in the smoothing parameter. -/
namespace PositiveEinsteinFour.Geometry
open MeasureTheory Filter Set
open scoped _root_.Topology
noncomputable section

def weylGapEpsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem weylGapEpsilon_pos (n : ℕ) : 0 < weylGapEpsilon n := by
  unfold weylGapEpsilon
  positivity

theorem weylGapEpsilon_le_one (n : ℕ) : weylGapEpsilon n ≤ 1 := by
  unfold weylGapEpsilon
  exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem weylGapEpsilon_tendsto : Tendsto weylGapEpsilon atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

end
end PositiveEinsteinFour.Geometry
end


section

/-! The L² tail absorption in the rational Brezis--Kato estimate.  All
constants are independent of the rational truncation parameter. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped _root_.Topology ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def scalarKatoTail (V : X → ℝ) (n : ℕ) (x : X) : ℝ := max (V x - n) 0

theorem scalarKatoTail_memLp {V : X → ℝ} (hV : MemLp V 2 μ) (n : ℕ) :
    MemLp (scalarKatoTail V n) 2 μ := by
  have hc : Continuous (fun r : ℝ => max (r - (n : ℝ)) 0) := by fun_prop
  apply hV.of_le (hc.comp_aestronglyMeasurable hV.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    exact max_le (by linarith [le_abs_self (V x), Nat.cast_nonneg (α := ℝ) n]) (abs_nonneg _)

theorem scalarKatoTail_small {V : X → ℝ} (hV : MemLp V 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, Real.sqrt (∫ x, scalarKatoTail V n x ^ 2 ∂μ) < ε := by
  have hd := tendsto_integral_of_dominated_convergence (fun x => V x ^ 2)
    (fun n => (scalarKatoTail_memLp hV n).aestronglyMeasurable.pow 2)
    hV.integrable_sq (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb : scalarKatoTail V n x ≤ |V x| :=
        max_le (by linarith [le_abs_self (V x), Nat.cast_nonneg (α := ℝ) n]) (abs_nonneg _)
      change scalarKatoTail V n x ^ 2 ≤ V x ^ 2
      simpa only [scalarKatoTail, sq_abs] using
        (sq_le_sq₀ (le_max_right _ _) (abs_nonneg _)).2 hb)
    (f := fun _ => (0 : ℝ)) (Eventually.of_forall fun x => by
      obtain ⟨N, hN⟩ := exists_nat_gt (V x)
      change Tendsto (fun n => scalarKatoTail V n x ^ 2) atTop (𝓝 0)
      apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hv : V x ≤ (n : ℝ) := hN.le.trans (by exact_mod_cast hn)
      simp only [scalarKatoTail, max_eq_right (sub_nonpos.mpr hv), zero_pow (by decide : 2 ≠ 0)])
  have hs : Tendsto (fun n => Real.sqrt (∫ x, scalarKatoTail V n x ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa only [integral_zero, Real.sqrt_zero, Function.comp_def] using!
      Real.continuous_sqrt.continuousAt.tendsto.comp hd
  obtain ⟨n, hn⟩ := (hs.eventually (gt_mem_nhds hε)).exists
  exact ⟨n, hn⟩

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Canceling the radial cubic measure against the actual exponential
Jacobian leaves the determinant of the normal Jacobi tensor itself. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem radial_cubic_cancel (a r : ℝ) (hr : 0 < r) :
    ENNReal.ofReal (r ^ 3) * ENNReal.ofReal |a / r ^ 3| = ENNReal.ofReal |a| := by
  rw [← ENNReal.ofReal_mul (pow_pos hr 3).le]
  congr 1
  rw [abs_div, abs_of_pos (pow_pos hr 3)]
  field_simp

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Choice and verification of the large parameter in the exponential
barrier on an annulus where the radial differential does not vanish. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem scalar_barrier_parameter {η B c₀ : ℝ} (hη : 0 < η)
    (hB : 0 ≤ B) (hc₀ : 0 ≤ c₀) : ∃ k : ℝ, 0 < k ∧ c₀ < k ^ 2 * η - k * B := by
  let k := (B + c₀ + 1) / η + 1
  have hk : 1 < k := by
    dsimp [k]
    have hdiv : 0 < (B + c₀ + 1) / η := div_pos (by linarith) hη
    linarith
  have hmul : k * η = B + c₀ + 1 + η := by
    dsimp [k]
    field_simp [ne_of_gt hη]
  refine ⟨k, lt_trans zero_lt_one hk, ?_⟩
  have hpos : 0 < c₀ + 1 + η := by linarith
  have hprod := mul_lt_mul_of_pos_right hk hpos
  have heq : k ^ 2 * η - k * B = k * (c₀ + 1 + η) := by
    calc
      _ = k * (k * η - B) := by ring
      _ = _ := by rw [hmul]; ring
  rw [heq]
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine smooth global radial function that agrees with squared
Euclidean chart distance on the inner ball. Outside that ball its value
stays above the inner squared radius, so it can localize a Hopf barrier. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M]

theorem scalarRadialBlend_lower {u v t w : ℝ} (hu : t ≤ u) (hv : t ≤ v)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) : t ≤ v + w * (u - v) := by
  have ha := mul_nonneg hw (sub_nonneg.mpr hu)
  have hb := mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hv)
  nlinarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The critical L4 estimate for the first derivatives of an H2 distribution.
The compactly supported Gagliardo--Nirenberg estimate is extended by cutoffs;
Schwartz approximation is then taken through the actual L2 Bessel inverse. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter Set FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)

theorem h2_schwartz_eLpNorm (f : 𝓢(V, ℂ)) :
    eLpNorm f 2 volume = ENNReal.ofReal ‖f.toLp 2 volume‖ := by
  rw [ofReal_norm]
  exact (Lp.enorm_toLp (f.memLp 2 volume)).symm

theorem h2_L2_injective :
    Function.Injective (fun f : L2 => (f : 𝓢'(V, ℂ))) :=
  LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))

def h2SchwartzInverse (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ
    (fun x : V => (Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ)))) f

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strong L4 continuity of the first derivative of the Bessel inverse.
The existing H2 gradient estimate gives membership; the closed graph theorem
upgrades this to the strong convergence needed in nonlinear second derivatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local instance instFactLeENNRealOfNat_solutions : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarCompactExtremal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Hilbert-space extremal argument used for the scalar Sobolev
quotient. Compactness provides a convergent image sequence; the
parallelogram identity forces an extremizing sequence itself to converge. -/

namespace PositiveEinsteinFour.Geometry

open Filter Set
open scoped _root_.Topology

noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalar_extremizing_sequence_cauchy (T : H →L[ℝ] E) (hT : 0 < ‖T‖)
    (u : ℕ → H) (hu : ∀ n, ‖u n‖ ≤ 1) (y : E)
    (hlim : Tendsto (fun n => T (u n)) atTop (𝓝 y)) (hy : ‖y‖ = ‖T‖) :
    CauchySeq u := by
  have hfst : Tendsto (fun nm : ℕ × ℕ => T (u nm.1)) atTop (𝓝 y) := by
    rw [← prod_atTop_atTop_eq]
    exact hlim.comp tendsto_fst
  have hsnd : Tendsto (fun nm : ℕ × ℕ => T (u nm.2)) atTop (𝓝 y) := by
    rw [← prod_atTop_atTop_eq]
    exact hlim.comp tendsto_snd
  have hsum : Tendsto (fun nm : ℕ × ℕ => ‖T (u nm.1 + u nm.2)‖ / ‖T‖)
      atTop (𝓝 2) := by
    have h := (hfst.add hsnd).norm.div_const ‖T‖
    have hv : ‖y + y‖ / ‖T‖ = 2 := by
      rw [← two_smul ℝ y, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hy]
      field_simp
    simpa only [map_add, hv] using h
  have hbound (nm : ℕ × ℕ) :
      ‖u nm.1 - u nm.2‖ ^ 2 ≤ 4 - (‖T (u nm.1 + u nm.2)‖ / ‖T‖) ^ 2 := by
    have hm : ‖T (u nm.1 + u nm.2)‖ / ‖T‖ ≤ ‖u nm.1 + u nm.2‖ :=
      (div_le_iff₀ hT).mpr (by simpa only [mul_comm] using T.le_opNorm (u nm.1 + u nm.2))
    have hm2 := (sq_le_sq₀ (div_nonneg (norm_nonneg _) hT.le) (norm_nonneg _)).mpr hm
    have h1 := (sq_le_sq₀ (norm_nonneg (u nm.1)) (by norm_num : (0 : ℝ) ≤ 1)).mpr (hu nm.1)
    have h2 := (sq_le_sq₀ (norm_nonneg (u nm.2)) (by norm_num : (0 : ℝ) ≤ 1)).mpr (hu nm.2)
    have hpar := parallelogram_law_with_norm ℝ (u nm.1) (u nm.2)
    nlinarith
  have hzero : Tendsto (fun nm : ℕ × ℕ => ‖u nm.1 - u nm.2‖ ^ 2)
      atTop (𝓝 0) := by
    have hb := (tendsto_const_nhds (x := (4 : ℝ))).sub (hsum.pow 2)
    norm_num at hb
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun nm => sq_nonneg _) (fun nm => by simpa only [map_add] using hbound nm)
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hzero
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero, dist_eq_norm] using hnorm

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarL4ProductConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong convergence of the quadratic gradient term in the local H2
chain rule. The coefficient is bounded and converges almost everywhere;
the two first-derivative factors converge in L4. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped ENNReal NNReal _root_.Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

local instance instHolderTripleOfNatENNReal_solutions : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
  constructor
  change ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ + ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0) : ℝ≥0∞)⁻¹
  rw [← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
    ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ← ENNReal.coe_add]
  norm_num

local instance localInst_r09fffd_1 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
def scalarL4Product : Lp ℝ 4 μ →L[ℝ] Lp ℝ 4 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ 4 4 2

theorem scalarL4Product_coe (f g : Lp ℝ 4 μ) :
    scalarL4Product (μ := μ) f g =ᵐ[μ] fun x => f x * g x :=
  (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder f g

theorem scalarL4Product_tendsto {f g : ℕ → Lp ℝ 4 μ} {F G : Lp ℝ 4 μ}
    (hf : Tendsto f atTop (𝓝 F)) (hg : Tendsto g atTop (𝓝 G)) :
    Tendsto (fun n => scalarL4Product (μ := μ) (f n) (g n)) atTop (𝓝 (scalarL4Product (μ := μ) F G)) := by
  let B : Lp ℝ 4 μ →L[ℝ] Lp ℝ 4 μ →L[ℝ] Lp ℝ 2 μ := scalarL4Product (μ := μ)
  have hB : Continuous (fun z : Lp ℝ 4 μ × Lp ℝ 4 μ => B z.1 z.2) := B.continuous₂
  have hp : Tendsto (fun n => (f n, g n)) atTop (𝓝 (F, G)) := hf.prodMk_nhds hg
  simpa only [Function.comp_def] using! (hB.tendsto (F, G)).comp hp

theorem scalarL4Product_coefficient_tendsto {a : ℕ → X → ℝ} {b : X → ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : 0 ≤ C) (haC : ∀ n x, |a n x| ≤ C) (hbC : ∀ x, |b x| ≤ C)
    (hab : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    {f g : ℕ → Lp ℝ 4 μ} {F G : Lp ℝ 4 μ}
    (hf : Tendsto f atTop (𝓝 F)) (hg : Tendsto g atTop (𝓝 G)) :
    Tendsto (fun n => scalarCompositionL2Multiply (a n) (ha n) (haC n)
        (scalarL4Product (μ := μ) (f n) (g n))) atTop
      (𝓝 (scalarCompositionL2Multiply b hb hbC (scalarL4Product (μ := μ) F G))) :=
  scalarCompositionL2Multiply_tendsto ha hb hC haC hbC hab (scalarL4Product_tendsto hf hg)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarCompositionHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonlinear Hessian candidate and its strong L2 continuity. This is
the two-term chain rule, with L4 first derivatives and L2 second derivatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped ENNReal ContDiff _root_.Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem secondDerivative_continuous (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    Continuous (deriv (deriv φ)) :=
  ((contDiff_infty_iff_deriv.mp hφ).2).continuous_deriv (by first | simp | exact_mod_cast le_top)

local instance instFactLeENNRealOfNat_solutions_1_r09fffd_1 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
def scalarCompositionHessian (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {C₁ C₂ : ℝ} (h₁ : ∀ s, |deriv φ s| ≤ C₁) (h₂ : ∀ s, |deriv (deriv φ) s| ≤ C₂)
    (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (g₁ g₂ : Lp ℝ 4 μ) (h : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  scalarCompositionL2Multiply (fun x => deriv (deriv φ) (u x))
    ((secondDerivative_continuous φ hφ).comp_aestronglyMeasurable hu)
    (fun x => h₂ (u x)) (scalarL4Product (μ := μ) g₁ g₂) +
  scalarCompositionL2Multiply (fun x => deriv φ (u x))
    ((hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable hu)
    (fun x => h₁ (u x)) h

theorem scalarCompositionHessian_coe (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {C₁ C₂ : ℝ} (h₁ : ∀ s, |deriv φ s| ≤ C₁) (h₂ : ∀ s, |deriv (deriv φ) s| ≤ C₂)
    (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (g₁ g₂ : Lp ℝ 4 μ) (h : Lp ℝ 2 μ) :
    scalarCompositionHessian φ hφ h₁ h₂ u hu g₁ g₂ h =ᵐ[μ]
      fun x => deriv (deriv φ) (u x) * g₁ x * g₂ x + deriv φ (u x) * h x := by
  let A := scalarCompositionL2Multiply (fun x => deriv (deriv φ) (u x))
    ((secondDerivative_continuous φ hφ).comp_aestronglyMeasurable hu)
    (fun x => h₂ (u x)) (scalarL4Product (μ := μ) g₁ g₂)
  let B := scalarCompositionL2Multiply (fun x => deriv φ (u x))
    ((hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable hu) (fun x => h₁ (u x)) h
  filter_upwards [Lp.coeFn_add A B,
    scalarCompositionL2Multiply_coe _ _ (fun x => h₂ (u x)) (scalarL4Product (μ := μ) g₁ g₂),
    scalarCompositionL2Multiply_coe _ _ (fun x => h₁ (u x)) h,
    scalarL4Product_coe g₁ g₂] with x hs ha hb hg
  change (A + B) x = _
  rw [hs, Pi.add_apply, ha, hb, hg]
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarL2BoundedMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded scalar coefficient acts continuously and linearly on L2.
This permits passage of local coordinate gradient bounds through H1 closure. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def scalarL2BoundedMultiplier (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    {C : ℝ} (hC : ∀ x, |a x| ≤ C) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := scalarCompositionL2Multiply a ha hC
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [scalarCompositionL2Multiply_coe a ha hC (f + g),
          scalarCompositionL2Multiply_coe a ha hC f,
          scalarCompositionL2Multiply_coe a ha hC g,
          Lp.coeFn_add f g,
          Lp.coeFn_add (scalarCompositionL2Multiply a ha hC f)
            (scalarCompositionL2Multiply a ha hC g)] with x hfg hf hg he hs
        simp only [Pi.add_apply] at he hs
        rw [hfg, he, hs, hf, hg]
        ring
      map_smul' := by
        intro r f
        apply Lp.ext
        filter_upwards [scalarCompositionL2Multiply_coe a ha hC (r • f),
          scalarCompositionL2Multiply_coe a ha hC f, Lp.coeFn_smul r f,
          Lp.coeFn_smul r (scalarCompositionL2Multiply a ha hC f)] with x hr hf he hs
        simp only [Pi.smul_apply, smul_eq_mul] at he hs
        simp only [RingHom.id_apply]
        rw [hr, he, hs, hf]
        ring }
    C (fun f => scalarCompositionL2Multiply_norm_le a ha hC f)

theorem scalarL2BoundedMultiplier_coe (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    {C : ℝ} (hC : ∀ x, |a x| ≤ C) (f : Lp ℝ 2 μ) :
    scalarL2BoundedMultiplier a ha hC f =ᵐ[μ] fun x => a x * f x :=
  scalarCompositionL2Multiply_coe a ha hC f

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarL2ClosedDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing finite coordinate domination inequalities through a dense H1 map. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped BigOperators

noncomputable section

variable {X E D : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalarL2_closed_domination (A : E →L[ℝ] Lp ℝ 2 μ)
    (B : Fin 4 → E →L[ℝ] Lp ℝ 2 μ) (C : ℝ) (f : D → E)
    (hd : DenseRange f)
    (hb : ∀ a, |A (f a)| ≤ C • ∑ i, |B i (f a)|) (u : E) :
    |A u| ≤ C • ∑ i, |B i u| := by
  have hA : Continuous (fun u => |A u|) := A.continuous.sup A.continuous.neg
  have hB (i : Fin 4) : Continuous (fun u => |B i u|) :=
    (B i).continuous.sup (B i).continuous.neg
  have hc : IsClosed {u : E | |A u| ≤ C • ∑ i, |B i u|} :=
    isClosed_le hA ((continuous_finsetSum _ (fun i _ => hB i)).const_smul C)
  exact hd.induction_on u hc hb

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarLocalL2Source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact-test forcing with an L2 localization gives a genuine order-zero
Sobolev source, without requiring a smooth right-hand side. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)

theorem scalar_localize_memSobolev_zero_of_L2_source (U : Set V)
    (u : T) (f : V → ℂ)
    (htest : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ U → u φ = ∫ x, φ x * f x)
    (ψ : S) (hc : HasCompactSupport (ψ : V → ℂ))
    (hs : tsupport (ψ : V → ℂ) ⊆ U)
    (hmem : MemLp (fun x => ψ x * f x) 2 (volume : Measure V)) :
    MemSobolev 0 2 (smulLeftCLM ℂ ψ u) := by
  let F : Lp ℂ 2 (volume : Measure V) := hmem.toLp (fun x => ψ x * f x)
  apply memSobolev_zero_iff.mpr
  refine ⟨F, ?_⟩
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ ψ φ) = _
  have hcompact : HasCompactSupport (SchwartzMap.smulLeftCLM ℂ ψ φ : V → ℂ) := by
    rw [SchwartzMap.smulLeftCLM_apply ψ.hasTemperateGrowth]
    exact hc.smul_right
  have hsupport : tsupport (SchwartzMap.smulLeftCLM ℂ ψ φ : V → ℂ) ⊆ U := by
    intro x hx
    exact hs ((SchwartzMap.tsupport_smulLeftCLM_subset (ψ : V → ℂ) φ hx).2)
  rw [htest _ hcompact hsupport, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hmem.coeFn_toLp] with x hx
  change (SchwartzMap.smulLeftCLM ℂ ψ φ) x * f x = φ x * F x
  rw [SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth, hx]
  simp only [smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarLpRelativeVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First variation along a direction dominated by the original Lp function.
This covers rational truncations of a Sobolev minimizer without boundedness
of the minimizer or a separate extension of its Euler equation. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Set Filter
open scoped _root_.Topology ENNReal

noncomputable section

theorem scalarRelativeMoment_point_derivative {p : ℝ} (hp : 2 < p)
    (f b t : ℝ) :
    HasDerivAt (fun s : ℝ => |f + s * b| ^ p)
      (p * |f + t * b| ^ (p - 2) * (f + t * b) * b) t := by
  have hlin : HasDerivAt (fun s : ℝ => f + s * b) b t := by
    simpa only [one_mul, zero_add, Pi.add_apply, id_eq] using!
      (hasDerivAt_const t f).add ((hasDerivAt_id t).mul_const b)
  simpa only [Function.comp_def] using
    (hasDerivAt_abs_rpow (f + t * b) (by linarith : 1 < p)).comp t hlin

theorem scalarRelativeMoment_bound {p B : ℝ} (hp : 2 < p) (hB : 0 ≤ B)
    {f b t : ℝ} (hb : |b| ≤ B * |f|) (ht : |t| ≤ 1) :
    ‖p * |f + t * b| ^ (p - 2) * (f + t * b) * b‖ ≤
      (p * B * (1 + B) ^ (p - 1)) * |f| ^ p := by
  have hbase : |f + t * b| ≤ (1 + B) * |f| := by
    calc
      _ ≤ |f| + |t| * |b| := by simpa only [abs_mul] using abs_add_le f (t * b)
      _ ≤ |f| + B * |f| := add_le_add le_rfl
        ((mul_le_mul_of_nonneg_right ht (abs_nonneg b)).trans (by simpa using hb))
      _ = _ := by ring
  have hpow : |f + t * b| ^ (p - 2) * |f + t * b| = |f + t * b| ^ (p - 1) := by
    rw [← Real.rpow_add_one' (abs_nonneg _) (by linarith : p - 2 + 1 ≠ 0)]
    congr 1
    ring
  calc
    _ = p * |f + t * b| ^ (p - 1) * |b| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_pos (by linarith : 0 < p),
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      rw [mul_assoc p, hpow]
    _ ≤ p * ((1 + B) * |f|) ^ (p - 1) * (B * |f|) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) hbase (by linarith)) (by linarith)
      · exact hb
      · exact abs_nonneg _
      · exact mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (abs_nonneg _)]
      have hf : |f| ^ (p - 1) * |f| = |f| ^ p := by
        rw [← Real.rpow_add_one' (abs_nonneg _) (by linarith : p - 1 + 1 ≠ 0)]
        congr 1
        ring
      calc
        _ = (p * B * (1 + B) ^ (p - 1)) * (|f| ^ (p - 1) * |f|) := by ring
        _ = _ := by rw [hf]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem scalarLpRelativeMoment_hasDerivAt {p : ℝ} (hp : 2 < p) {f b : X → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) (hb : AEStronglyMeasurable b μ)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ᵐ x ∂μ, |b x| ≤ B * |f x|) :
    Integrable (fun x => |f x| ^ (p - 2) * f x * b x) μ ∧
      HasDerivAt (fun t : ℝ => ∫ x, |f x + t * b x| ^ p ∂μ)
        (p * ∫ x, |f x| ^ (p - 2) * f x * b x ∂μ) 0 := by
  let F (t : ℝ) (x : X) := |f x + t * b x| ^ p
  let G (t : ℝ) (x : X) := p * |f x + t * b x| ^ (p - 2) * (f x + t * b x) * b x
  let H (x : X) := (p * B * (1 + B) ^ (p - 1)) * |f x| ^ p
  have hp0 : 0 < p := by linarith
  have hpowMeas {q : ℝ} (hq : 0 ≤ q) {h : X → ℝ}
      (hh : AEStronglyMeasurable h μ) :
      AEStronglyMeasurable (fun x => |h x| ^ q) μ :=
    (continuous_abs.rpow_const (fun _ => Or.inr hq)).comp_aestronglyMeasurable hh
  have hFm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) μ :=
    Eventually.of_forall fun t => hpowMeas hp0.le
      (hf.aestronglyMeasurable.add (hb.const_mul t))
  have hFi : Integrable (F 0) μ := by
    simpa only [F, zero_mul, add_zero, Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le]
      using hf.integrable_norm_rpow'
  have hGm : AEStronglyMeasurable (G 0) μ := by
    simpa only [G, zero_mul, add_zero, Pi.mul_apply] using!
      (((hpowMeas (by linarith : 0 ≤ p - 2) hf.aestronglyMeasurable).const_mul p).mul
        hf.aestronglyMeasurable).mul hb
  have hHi : Integrable H μ := by
    apply Integrable.const_mul
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using hf.integrable_norm_rpow'
  have hbound' : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (-1 : ℝ) 1, ‖G t x‖ ≤ H x := by
    filter_upwards [hbound] with x hx t ht
    exact scalarRelativeMoment_bound hp hB hx (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)
  have hdiff : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => F s x) (G t x) t :=
    Eventually.of_forall fun x t _ => scalarRelativeMoment_point_derivative hp (f x) (b x) t
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by constructor <;> norm_num))
    hFm hFi hGm hbound' hHi hdiff
  have hi : Integrable (fun x => |f x| ^ (p - 2) * f x * b x) μ := by
    have hscaled := h.1.const_mul p⁻¹
    convert hscaled using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [G, zero_mul, add_zero]
    field_simp [ne_of_gt hp0]
  refine ⟨hi, ?_⟩
  have heq : (fun x => G 0 x) = fun x => p * (|f x| ^ (p - 2) * f x * b x) := by
    funext x
    dsimp [G]
    simp only [zero_mul, add_zero]
    ring
  simpa only [heq, integral_const_mul] using h.2

/-- The squared norm derivative used to test a homogeneous energy minimum
with a rational truncation of the minimizer itself. -/
theorem scalarLpRelativeNormSq_hasDerivAt {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 < p) (f b : Lp ℝ (ENNReal.ofReal p) μ) (hf : ‖f‖ = 1)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ᵐ x ∂μ, |b x| ≤ B * |f x|) :
    HasDerivAt (fun t : ℝ => ‖f + t • b‖ ^ 2)
      (2 * ∫ x, |f x| ^ (p - 2) * f x * b x ∂μ) 0 := by
  have hp0 : 0 < p := by linarith
  have hd := (scalarLpRelativeMoment_hasDerivAt hp (Lp.memLp f)
    (Lp.aestronglyMeasurable b) hB hbound).2
  have hz : (∫ x, |f x + (0 : ℝ) * b x| ^ p ∂μ) = 1 := by
    simp only [zero_mul, add_zero]
    rw [scalarLp_moment_eq_norm_rpow hp0 f, hf, Real.one_rpow]
  have hpow := hd.rpow_const (p := 2 / p) (Or.inl (by rw [hz]; norm_num))
  have heq : (fun t : ℝ => ‖f + t • b‖ ^ 2) =
      fun t => (∫ x, |f x + t * b x| ^ p ∂μ) ^ (2 / p) := by
    funext t
    rw [scalarLp_norm_sq_eq_moment hp0]
    congr 1
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f (t • b), Lp.coeFn_smul t b] with x hsum hsmul
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hsum hsmul
    rw [hsum, hsmul]
  rw [← heq] at hpow
  convert hpow using 1
  all_goals try with_reducible_and_instances rfl
  rw [hz, Real.one_rpow, mul_one]
  field_simp [hp0.ne']

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarMinimizingSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong convergence of a minimizing sequence once its actual Lp values
converge.  This is the Hilbert-space closure step for taking absolute values. -/

namespace PositiveEinsteinFour.Geometry

open Filter
open scoped _root_.Topology

noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalar_energy_minimizing_sequence_cauchy (T : H →L[ℝ] E) (m : ℝ)
    (hmin : ∀ v : H, m * ‖T v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (u : ℕ → H) (y : E) (hy : ‖y‖ = 1)
    (hlim : Tendsto (fun n => T (u n)) atTop (𝓝 y))
    (henergy : Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 m)) : CauchySeq u := by
  have hf : Tendsto (fun nm : ℕ × ℕ => T (u nm.1)) atTop (𝓝 y) := by
    rw [← prod_atTop_atTop_eq]
    exact hlim.comp tendsto_fst
  have hs : Tendsto (fun nm : ℕ × ℕ => T (u nm.2)) atTop (𝓝 y) := by
    rw [← prod_atTop_atTop_eq]
    exact hlim.comp tendsto_snd
  have hef : Tendsto (fun nm : ℕ × ℕ => ‖u nm.1‖ ^ 2) atTop (𝓝 m) := by
    rw [← prod_atTop_atTop_eq]
    exact henergy.comp tendsto_fst
  have hes : Tendsto (fun nm : ℕ × ℕ => ‖u nm.2‖ ^ 2) atTop (𝓝 m) := by
    rw [← prod_atTop_atTop_eq]
    exact henergy.comp tendsto_snd
  have hsum : Tendsto (fun nm : ℕ × ℕ => ‖T (u nm.1 + u nm.2)‖) atTop (𝓝 2) := by
    have hy2 : ‖y + y‖ = 2 := by
      rw [← two_smul ℝ y, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hy, mul_one]
    simpa only [map_add, hy2] using (hf.add hs).norm
  have hb : Tendsto (fun nm : ℕ × ℕ =>
      2 * ‖u nm.1‖ ^ 2 + 2 * ‖u nm.2‖ ^ 2 - m * ‖T (u nm.1 + u nm.2)‖ ^ 2)
      atTop (𝓝 0) := by
    convert (hef.const_mul 2 |>.add (hes.const_mul 2)).sub ((hsum.pow 2).const_mul m) using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  have hz : Tendsto (fun nm : ℕ × ℕ => ‖u nm.1 - u nm.2‖ ^ 2) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun _ => sq_nonneg _)
    intro nm
    have hp := parallelogram_law_with_norm ℝ (u nm.1) (u nm.2)
    have hm := hmin (u nm.1 + u nm.2)
    nlinarith
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hz
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero, dist_eq_norm] using hnorm

theorem scalar_energy_minimizing_sequence_limit [CompleteSpace H] (T : H →L[ℝ] E) (m : ℝ)
    (hmin : ∀ v : H, m * ‖T v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (u : ℕ → H) (y : E) (hy : ‖y‖ = 1)
    (hlim : Tendsto (fun n => T (u n)) atTop (𝓝 y))
    (henergy : Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 m)) :
    ∃ w : H, T w = y ∧ ‖w‖ ^ 2 = m ∧ Tendsto u atTop (𝓝 w) := by
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete
    (scalar_energy_minimizing_sequence_cauchy T m hmin u y hy hlim henergy)
  exact ⟨w, tendsto_nhds_unique (T.continuous.tendsto w |>.comp hw) hlim,
    tendsto_nhds_unique (hw.norm.pow 2) henergy, hw⟩

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Fourth-power integrability transfers through compact chart reconstruction
and the closed coordinate-to-frame domination inequality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter Function
open scoped Manifold ContDiff ENNReal BigOperators

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem scalarL2_memLp_four_of_domination (a : Lp ℝ 2 μ)
    (b : Fin 4 → Lp ℝ 2 μ) (C : ℝ)
    (h : |a| ≤ C • ∑ j, |b j|) (hb : ∀ j, MemLp (b j : X → ℝ) 4 μ) :
    MemLp (a : X → ℝ) 4 μ := by
  have hm : MemLp (fun x => C * ∑ j, |b j x|) 4 μ := by
    have hs : MemLp (fun x => ∑ j : Fin 4, |b j x|) 4 μ := by
      simpa only [Finset.sum_apply, Pi.abs_apply] using
        (memLp_finsetSum Finset.univ (fun j _ => (hb j).abs))
    exact hs.const_mul C
  apply hm.mono' (Lp.aestronglyMeasurable a)
  have hh := (Lp.coeFn_le _ _).mpr h
  have hall : ∀ᵐ x ∂μ, ∀ j : Fin 4, |b j| x = |b j x| :=
    eventually_all.mpr (fun j => Lp.coeFn_abs (b j))
  filter_upwards [hh, Lp.coeFn_abs a, Lp.coeFn_smul C (∑ j, |b j|),
    Lp.coeFn_finsetSum Finset.univ (fun j => |b j|), hall] with x hx ha hc hs hbs
  rw [ha, hc] at hx
  simp only [Pi.smul_apply, smul_eq_mul] at hx
  rw [hs] at hx
  simp only [Finset.sum_apply] at hx
  simpa only [Real.norm_eq_abs, hbs] using hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normalization and the actual energy minimum for the subcritical scalar
Sobolev quotient.  The constant function gives the upper bound one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

theorem scalar_normalize_extremal
    {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : H →L[ℝ] E) (hT : 0 < ‖T‖) (x : H)
    (hx : ‖x‖ = 1) (hTx : ‖T x‖ = ‖T‖) :
    ∃ w : H, ‖T w‖ = 1 ∧ 0 < ‖w‖ ^ 2 ∧
      ∀ v : H, ‖w‖ ^ 2 * ‖T v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  let w := ‖T‖⁻¹ • x
  have hw : ‖w‖ = ‖T‖⁻¹ := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT), hx, mul_one]
  have hTw : ‖T w‖ = 1 := by
    simp only [w, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hT), hTx, inv_mul_cancel₀ (ne_of_gt hT)]
  refine ⟨w, hTw, by rw [hw]; positivity, fun v => ?_⟩
  have hb : ‖T‖⁻¹ * ‖T v‖ ≤ ‖v‖ := by
    have h := mul_le_mul_of_nonneg_left (T.le_opNorm v) (inv_nonneg.mpr hT.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hT), one_mul] using h
  calc
    ‖w‖ ^ 2 * ‖T v‖ ^ 2 = (‖T‖⁻¹ * ‖T v‖) ^ 2 := by rw [hw]; ring
    _ ≤ ‖v‖ ^ 2 := (sq_le_sq₀ (by positivity) (norm_nonneg v)).mpr hb

end
end PositiveEinsteinFour.Geometry
end


section

/-! The subcritical nonlinear chain rule on the actual H1 closure. Smooth
bounded-derivative truncations converge strongly in the value and all four
weak derivatives, using L8 values and L4 gradients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

theorem nonlinear_square_rpow (q s : ℝ) :
    (s ^ 2) ^ (q / 2) = |s| ^ q := by
  rw [← sq_abs, ← Real.rpow_natCast_mul (abs_nonneg s)]
  congr 1
  ring

theorem nonlinear_value_bound {q ε : ℝ}
    (hq : 0 < q) (hq2 : q < 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    |scalarNonlinearTruncation q ε s| ≤ |s| * (1 + s ^ 2) := by
  have hp : 0 ≤ (s ^ 2 + ε) ^ (q / 2) := Real.rpow_nonneg (by positivity) _
  rw [scalarNonlinearTruncation, abs_div, abs_mul, abs_of_nonneg hp,
    abs_of_pos (show 0 < 1 + ε * s ^ 2 by positivity)]
  apply (div_le_iff₀ (by positivity)).mpr
  calc
    _ ≤ |s| * (1 + s ^ 2) :=
      mul_le_mul_of_nonneg_left (scalarNonlinearTruncation_power_bound hq hq2 hε hε1 s)
        (abs_nonneg _)
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (by nlinarith [sq_nonneg s])

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarIntegrableSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute integral convergence makes a pointwise scalar series integrable. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter ENNReal
open scoped ENNReal _root_.Topology

theorem scalar_integrable_series {X ι : Type*} [MeasurableSpace X] [Countable ι]
    {μ : Measure X} {F : ι → X → ℝ} {f : X → ℝ}
    (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂μ))
    (hf : ∀ x, HasSum (fun i => F i x) (f x)) : Integrable f μ := by
  classical
  have hm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun s : Finset ι => (integrable_finsetSum s (fun i _ => hF i)).aestronglyMeasurable)
      (Eventually.of_forall hf)
  have he (i : ι) : (∫⁻ x, ‖F i x‖ₑ ∂μ) = ‖∫ x, ‖F i x‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF i).norm, coe_nnreal_eq, coe_nnnorm]
    simp only [coe_nnnorm, Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg (fun x => abs_nonneg (F i x)))]
  have hne : (∑' i, ∫⁻ x, ‖F i x‖ₑ ∂μ) ≠ ∞ := by
    rw [funext he]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hs.abs)
  refine ⟨hm, lt_of_le_of_lt (lintegral_mono (g := fun x => ∑' i, ‖F i x‖ₑ)
    (fun x => ?_)) ?_⟩
  · rw [← (hf x).tsum_eq]
    exact enorm_tsum_le_tsum_enorm
  · rw [lintegral_tsum (fun i => (hF i).aestronglyMeasurable.enorm)]
    exact hne.lt_top

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HeatKernels10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Counting a fixed eigenvalue in the actual finite eigenspace indexing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff NNReal

noncomputable section

theorem tsum_eigenvalue_finrank {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) :
    (∑' μ : A.Eigenvalues,
      if μ.val = 1 then (Module.finrank ℝ (A.eigenspace μ.val) : ℝ) else 0) =
        (Module.finrank ℝ (A.eigenspace 1) : ℝ) := by
  classical
  by_cases h : A.HasEigenvalue 1
  · let μ : A.Eigenvalues := ⟨1, h⟩
    rw [tsum_eq_single μ]
    · simp only [μ, Module.End.Eigenvalues.val_mk, ↓reduceIte]
      rfl
    · intro ν hν
      have hn : ν.val ≠ 1 := fun he => hν (Subtype.ext he)
      simp only [hn, ↓reduceIte]
  · have hz : A.eigenspace 1 = ⊥ := not_ne_iff.mp h
    have he : ∀ μ : A.Eigenvalues, μ.val ≠ 1 := by
      intro μ hm
      apply μ.property
      change A.eigenspace μ.val = ⊥
      rw [hm]
      exact hz
    simp only [he, ↓reduceIte, tsum_zero]
    change 0 = (Module.finrank ℝ (A.eigenspace 1) : ℝ)
    rw [hz, finrank_bot, Nat.cast_zero]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The squared-norm error needed to pass the L2 column comparison
to the actual diagonal heat trace. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter
open scoped _root_.Topology

noncomputable section

variable {V : Type*} [NormedAddCommGroup V]

theorem heat_norm_square_error_bound (x y : V) (a b : ℝ)
    (ha : ‖x‖ ≤ a) (hb : ‖x - y‖ ≤ b) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ (2 * a + b) * b := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans hb
  have hy : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    have h := norm_sub_norm_le y x
    rw [norm_sub_rev] at h
    linarith
  have hsum : ‖x‖ + ‖y‖ ≤ 2 * a + b := by linarith
  calc
    _ = |‖x‖ - ‖y‖| * (‖x‖ + ‖y‖) := by
      rw [← abs_of_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y)), ← abs_mul]
      congr 1
      ring
    _ ≤ b * (2 * a + b) := mul_le_mul ((abs_norm_sub_norm_le x y).trans hb) hsum
      (add_nonneg (norm_nonneg x) (norm_nonneg y)) hb0
    _ = _ := by ring

theorem heat_norm_square_error_tendsto (x y : ℝ → V) (C D T : ℝ) (hT : 0 < T)
    (hx : ∀ t ∈ Ioc 0 T, ‖x t‖ ≤ C / t)
    (hy : ∀ t ∈ Ioc 0 T, ‖x t - y t‖ ≤ D * t ^ 2) :
    Tendsto (fun t => ‖x t‖ ^ 2 - ‖y t‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => 2 * C * D * t + D ^ 2 * t ^ 4)
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => 2 * C * D * t + D ^ 2 * t ^ 4) := by fun_prop
    simpa only [mul_zero, zero_pow (by norm_num : 4 ≠ 0), add_zero] using
      hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply squeeze_zero_norm' _ hlim
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < T :=
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht htT
  rw [Real.norm_eq_abs]
  calc
    _ ≤ (2 * (C / t) + D * t ^ 2) * (D * t ^ 2) :=
      heat_norm_square_error_bound (x t) (y t) _ _ (hx t ⟨ht, htT.le⟩) (hy t ⟨ht, htT.le⟩)
    _ = _ := by field_simp [(show 0 < t from ht).ne']

end
end PositiveEinsteinFour.Geometry
end


section

/-! Passing the normal-column L2 error to each signed Gram entry. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter
open scoped _root_.Topology

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem heat_inner_error_bound (x y z w : V) (a b c d : ℝ)
    (ha : ‖x‖ ≤ a) (hb : ‖x - y‖ ≤ b) (hc : ‖z‖ ≤ c) (hd : ‖z - w‖ ≤ d) :
    ‖inner ℝ x z - inner ℝ y w‖ ≤ b * c + (a + b) * d := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans hb
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  have hy : ‖y‖ ≤ a + b := by
    have hh := norm_sub_norm_le y x
    rw [norm_sub_rev] at hh
    linarith
  have he : inner ℝ x z - inner ℝ y w = inner ℝ (x - y) z + inner ℝ y (z - w) := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ ‖inner ℝ (x - y) z‖ + ‖inner ℝ y (z - w)‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ * ‖z‖ + ‖y‖ * ‖z - w‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ b * c + (a + b) * d := add_le_add
      (mul_le_mul hb hc (norm_nonneg z) hb0)
      (mul_le_mul hy hd (norm_nonneg (z - w)) ((norm_nonneg y).trans hy))

theorem heat_inner_error_tendsto (x y z w : ℝ → V) (C₁ C₂ D T : ℝ) (hT : 0 < T)
    (hx : ∀ t ∈ Ioc 0 T, ‖x t‖ ≤ C₁ / t)
    (hz : ∀ t ∈ Ioc 0 T, ‖z t‖ ≤ C₂ / t)
    (hxy : ∀ t ∈ Ioc 0 T, ‖x t - y t‖ ≤ D * t ^ 2)
    (hzw : ∀ t ∈ Ioc 0 T, ‖z t - w t‖ ≤ D * t ^ 2) :
    Tendsto (fun t => inner ℝ (x t) (z t) - inner ℝ (y t) (w t)) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => (D * C₂ + C₁ * D) * t + D ^ 2 * t ^ 4)
      (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun t : ℝ => (D * C₂ + C₁ * D) * t + D ^ 2 * t ^ 4) := by fun_prop
    simpa only [mul_zero, zero_pow (by norm_num : 4 ≠ 0), add_zero] using
      hcont.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht htT
  calc
    _ ≤ (D * t ^ 2) * (C₂ / t) + (C₁ / t + D * t ^ 2) * (D * t ^ 2) :=
      heat_inner_error_bound (x t) (y t) (z t) (w t) _ _ _ _
        (hx t ⟨ht, htT.le⟩) (hxy t ⟨ht, htT.le⟩) (hz t ⟨ht, htT.le⟩) (hzw t ⟨ht, htT.le⟩)
    _ = _ := by field_simp [(show 0 < t from ht).ne']; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform control of signed Gram sums from the actual column estimates. -/

namespace PositiveEinsteinFour.Geometry

open Set
open scoped BigOperators

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem heat_inner_error_uniform (x y z w : V) (C D t : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hx : ‖x‖ ≤ C / t) (hz : ‖z‖ ≤ C / t)
    (hxy : ‖x - y‖ ≤ D * t ^ 2) (hzw : ‖z - w‖ ≤ D * t ^ 2) :
    ‖inner ℝ x z - inner ℝ y w‖ ≤ 2 * C * D + D ^ 2 := by
  calc
    _ ≤ (D * t ^ 2) * (C / t) + (C / t + D * t ^ 2) * (D * t ^ 2) :=
      heat_inner_error_bound x y z w _ _ _ _ hx hxy hz hzw
    _ = 2 * C * D * t + D ^ 2 * t ^ 4 := by field_simp [ht.1.ne']; ring
    _ ≤ 2 * C * D + D ^ 2 := by
      have hpow : t ^ 4 ≤ 1 := pow_le_one₀ ht.1.le ht.2
      exact add_le_add
        (mul_le_of_le_one_right (by positivity) ht.2)
        (mul_le_of_le_one_right (sq_nonneg D) hpow)

theorem heat_signed_gram_error_uniform {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (x y : ι → V) (C D t : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hx : ∀ l, ‖x l‖ ≤ C / t) (hxy : ∀ l, ‖x l - y l‖ ≤ D * t ^ 2) :
    ‖(∑ l, ∑ m, A l m * inner ℝ (x l) (x m)) -
      (∑ l, ∑ m, A l m * inner ℝ (y l) (y m))‖ ≤
      (∑ l, ∑ m, ‖A l m‖) * (2 * C * D + D ^ 2) := by
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ l, ∑ m, ‖A l m * (inner ℝ (x l) (x m) - inner ℝ (y l) (y m))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_sum_le _ _)
    _ ≤ ∑ l, ∑ m, ‖A l m‖ * (2 * C * D + D ^ 2) := by
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro m _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (heat_inner_error_uniform (x l) (y l) (x m) (y m) C D t hC hD ht
          (hx l) (hx m) (hxy l) (hxy m)) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform squared-norm errors for finite families of actual heat columns. -/
namespace PositiveEinsteinFour.Geometry
open Set
open scoped BigOperators
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem heat_norm_square_error_uniform (x y : V) (C D t : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hx : ‖x‖ ≤ C / t) (hxy : ‖x - y‖ ≤ D * t ^ 2) :
    ‖‖x‖ ^ 2 - ‖y‖ ^ 2‖ ≤ 2 * C * D + D ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using
    heat_inner_error_uniform x y x y C D t hC hD ht hx hx hxy hxy

theorem heat_sum_norm_square_error_uniform {ι : Type*} [Fintype ι]
    (x y : ι → V) (C D t : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hx : ∀ l, ‖x l‖ ≤ C / t) (hxy : ∀ l, ‖x l - y l‖ ≤ D * t ^ 2) :
    ‖(∑ l, ‖x l‖ ^ 2) - (∑ l, ‖y l‖ ^ 2)‖ ≤
      (Fintype.card ι : ℝ) * (2 * C * D + D ^ 2) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ l, ‖‖x l‖ ^ 2 - ‖y l‖ ^ 2‖ := norm_sum_le _ _
    _ ≤ ∑ _ : ι, (2 * C * D + D ^ 2) := Finset.sum_le_sum fun l _ =>
      heat_norm_square_error_uniform (x l) (y l) C D t hC hD ht (hx l) (hxy l)
    _ = _ := by simp [mul_add]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SineLogPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit comparison function for the lower-volume sine remainder. -/
namespace PositiveEinsteinFour.Jacobi
noncomputable section

def sineLogPolynomial (x : ℝ) : ℝ := x ^ 2 / 6 + x ^ 4 / 180 + x ^ 6 / 2835
def sineCotPolynomial (x : ℝ) : ℝ := 1 - x ^ 2 / 3 - x ^ 4 / 45 - 2 * x ^ 6 / 945
def sineLogRate (x : ℝ) : ℝ := x / 3 + x ^ 3 / 45 + 2 * x ^ 5 / 945
def sineLogResidual (x : ℝ) : ℝ := x ^ 7 / 525 + 4 * x ^ 9 / 42525 + 4 * x ^ 11 / 893025

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Exact radial mass for the round Jacobi determinant. Cutting strictly
before pi strictly decreases this mass. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory Set
open scoped ENNReal
noncomputable section

def roundRadialMass (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioc (0 : ℝ) c, ENNReal.ofReal (Real.sin r ^ 3)

theorem roundRadialMass_formula (c : ℝ) (hc : c ∈ Icc (0 : ℝ) Real.pi) :
    roundRadialMass c = ENNReal.ofReal
      (2 / 3 - Real.cos c + Real.cos c ^ 3 / 3) := by
  have hi : IntegrableOn (fun r => Real.sin r ^ 3) (Ioc (0 : ℝ) c) :=
    (Real.continuous_sin.pow 3).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hn : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) c)), 0 ≤ Real.sin r ^ 3 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hr.1.le (hr.2.trans hc.2)) 3
  rw [roundRadialMass, ← ofReal_integral_eq_lintegral_ofReal hi hn,
    ← intervalIntegral.integral_of_le hc.1, integral_sin_pow_three, Real.cos_zero]
  congr 1
  ring

theorem roundRadialMass_pi : roundRadialMass Real.pi = ENNReal.ofReal (4 / 3 : ℝ) := by
  rw [roundRadialMass_formula _ ⟨Real.pi_pos.le, le_rfl⟩, Real.cos_pi]
  norm_num

theorem roundRadialMass_le_pi (c : ℝ) (hc : c ≤ Real.pi) :
    roundRadialMass c ≤ roundRadialMass Real.pi :=
  lintegral_mono_set (Ioc_subset_Ioc_right hc)

theorem roundRadialMass_lt_pi (c : ℝ) (hc : c ∈ Ico (0 : ℝ) Real.pi) :
    roundRadialMass c < roundRadialMass Real.pi := by
  rw [roundRadialMass_formula c ⟨hc.1, hc.2.le⟩, roundRadialMass_pi]
  have hlo : -1 < Real.cos c := by
    simpa only [Real.cos_pi] using
      Real.strictAntiOn_cos ⟨hc.1, hc.2.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hc.2
  have hhi := Real.cos_le_one c
  have hpos : 0 < (Real.cos c + 1) ^ 2 * (2 - Real.cos c) :=
    mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : 0 < (4 / 3 : ℝ))).mpr
  nlinarith only [hpos]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Explicit polar coordinates on the actual round four-sphere. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped BigOperators
noncomputable section

def roundNorth : RoundSphere4 := ⟨EuclideanSpace.single 0 1, by simp⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sphere map is continuous at both poles as well as in the ordinary
polar chart; the south-pole bound uses the proved common endpoint. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Bundle Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem roundPolarAngle_continuous :
    Continuous (fun p : RoundSphere4 => Real.arccos (p.val 0)) := by
  fun_prop

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness upgrades the local sphere map to a genuine covering away
from the common antipodal value. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section

theorem roundSphere_compact : IsCompact {v : EuclideanSpace ℝ (Fin 5) | ‖v‖ = 1} := by
  simpa only [Metric.sphere, dist_zero_right] using
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 5)) 1)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two scalar Jacobi factors for Ricci-normalized complex curvature. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour
noncomputable section

def complexJacobiSlow (t : ℝ) : ℝ := Real.sqrt 2 * Real.sin (t / Real.sqrt 2)
def complexJacobiFast (t : ℝ) : ℝ := Real.sin (Real.sqrt 2 * t) / Real.sqrt 2

end
end PositiveEinsteinFour.Jacobi
end


section

/-! Exact radial volume of the Ricci-normalized complex Jacobi solution. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi MeasureTheory Set
open scoped ENNReal
noncomputable section

def complexRadialDensity (t : ℝ) : ℝ := complexJacobiSlow t ^ 2 * complexJacobiFast t

theorem complexRadialDensity_continuous : Continuous complexRadialDensity := by
  unfold complexRadialDensity complexJacobiSlow complexJacobiFast
  fun_prop

def complexRadialMass (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioc (0 : ℝ) c, ENNReal.ofReal (complexRadialDensity r)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_LocalIncrementMeanValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A mean-value bound requiring only local one-sided increment inequalities. -/
namespace PositiveEinsteinFour.Geometry
open Set Filter
open scoped _root_.Topology

theorem sub_le_of_local_increment (f : ℝ → ℝ) (a b C : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hlocal : ∀ x ∈ Ico a b, ∀ᶠ y in 𝓝[>] x,
      f y - f x ≤ C * (y-x)) :
    f b - f a ≤ C * (b-a) := by
  let B : ℝ → ℝ := fun x => f a + C * (x-a)
  have hB : Continuous B := continuous_const.add (continuous_const.mul
    (continuous_id.sub continuous_const))
  have hderiv (x : ℝ) : HasDerivAt B C x := by
    simpa only [mul_one,B,id_eq] using! (((hasDerivAt_id x).sub_const a).const_mul C).const_add (f a)
  have hbound := image_le_of_liminf_slope_right_le_deriv_boundary hf
    (show f a ≤ B a by simp [B]) hB.continuousOn
    (fun x _ => (hderiv x).hasDerivWithinAt) (fun x hx r hr => ?_)
  · have h := hbound ⟨hab,le_rfl⟩
    dsimp [B] at h
    linarith
  · apply Filter.Eventually.frequently
    filter_upwards [hlocal x hx,self_mem_nhdsWithin] with y hy hxy
    have hd : 0 < y-x := sub_pos.mpr hxy
    have hs : slope f x y ≤ C := by
      rw [slope_def_field]
      exact (div_le_iff₀ hd).mpr hy
    exact hs.trans_lt hr

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The exact logarithm of the standard projective affine chart, in the
Ricci-three normal coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Set
noncomputable section

def complexAffineRadius (z : EuclideanSpace ℂ (Fin 2)) : ℝ :=
  Real.sqrt 2 * Real.arctan ‖z‖

end
end PositiveEinsteinFour.Geometry
end


section

/-! The ordinary affine logarithm is differentiable away from its center. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi
noncomputable section

theorem complexAffineRadius_pos {z : EuclideanSpace ℂ (Fin 2)} (hz : z ≠ 0) :
    0 < complexAffineRadius z :=
  mul_pos (by positivity) (Real.arctan_pos.mpr (norm_pos_iff.mpr hz))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Cauchy--Schwarz for the horizontal part of a projective velocity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem complex_real_inner_mul_self (z a : ℂ) :
    inner ℝ z (a*z) = ‖z‖^2 * a.re := by
  change ((a*z)*star z).re = _
  rw [mul_assoc,Complex.star_def,Complex.mul_conj',← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A nontrivial complex sine/cosine combination has at most one zero in a quadrant. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
noncomputable section

theorem complex_trigonometric_zeros_subsingleton (a b : ℂ) (hab : a ≠ 0 ∨ b ≠ 0) :
    {t : ℝ | t ∈ Ioo 0 (Real.pi/2) ∧
      (Real.cos t : ℂ)*a + (Real.sin t : ℂ)*b = 0}.Subsingleton := by
  have hc (t : ℝ) (ht : t ∈ Ioo 0 (Real.pi/2)) : (Real.cos t : ℂ) ≠ 0 := by
    exact_mod_cast (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,ht.1],ht.2⟩).ne'
  have heq (t : ℝ) (ht : t ∈ Ioo 0 (Real.pi/2))
      (hz : (Real.cos t : ℂ)*a + (Real.sin t : ℂ)*b = 0) :
      a + (Real.tan t : ℂ)*b = 0 := by
    calc
      _ = (Real.cos t : ℂ)⁻¹ * ((Real.cos t : ℂ)*a + (Real.sin t : ℂ)*b) := by
        rw [Real.tan_eq_sin_div_cos,Complex.ofReal_div]
        rw [mul_add,← mul_assoc,inv_mul_cancel₀ (hc t ht),one_mul]
        ring
      _ = 0 := by rw [hz,mul_zero]
  intro s hs t ht
  by_cases hb : b = 0
  · have ha := (hab.resolve_right (by simpa using hb))
    have h := heq s hs.1 hs.2
    rw [hb,mul_zero,add_zero] at h
    exact (ha h).elim
  have hdiff : ((Real.tan s : ℂ)-(Real.tan t : ℂ))*b = 0 := by
    linear_combination heq s hs.1 hs.2 - heq t ht.1 ht.2
  have htan : Real.tan s = Real.tan t := by
    have h := sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right hb)
    exact_mod_cast h
  exact Real.injOn_tan ⟨by linarith [hs.1.1,Real.pi_pos],hs.1.2⟩
    ⟨by linarith [ht.1.1,Real.pi_pos],ht.1.2⟩ htan

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Arbitrarily sharp inverse metric bounds on neighborhoods of every actual point. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def complexInverseDistortion (δ : ℝ) : ℝ := (Real.sqrt 2)⁻¹ * Real.sqrt (1+δ) * (1 / Real.sqrt (1-δ))

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


