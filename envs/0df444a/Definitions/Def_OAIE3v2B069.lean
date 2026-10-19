-- Prove2me | Definitions.Def_OAIE3v2B069
-- name    : OAIE3v2B069
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:16:04.660157+00:00
-- url     : https://prove2.me/theorems/c4ea774a-ac3c-4448-83ed-8accac3bd0b5
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 70 of 311
-- statement:
--   Definitions bundle 70 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B040`, `OAIE3v2B041`, `OAIE3v2B042`, `OAIE3v2B046` of this split.
--
--   Modules: `Estimates/CyclicProgressionHom.lean`, `Estimates/FastCoefficientBlocks.lean`, `Estimates/FiniteDependentPMFBind.lean`, `Estimates/FreePrimitiveCriterion.lean`, `Estimates/LieTreeMultidegree.lean`, `Estimates/NativeGraphSmallDifference.lean`, `Estimates/RelativeFiberSlicePatch.lean`, `Estimates/RelativePatchAmplification.lean`, `Estimates/RepresentativeWindowPatch.lean`, `Estimates/TranslationShearExponentialOver.lean`, `Estimates/WeightedTranslationShearExponential.lean`, `FixedDensity/OrderedRemoval.lean`, `Fourier/QuarticBohrProgression.lean`, `Geometry/CyclicProgressionCoordinates.lean`, `Geometry/LieCoordinateHeight.lean`, `Geometry/TopSupportSubstitution.lean`, `Lattices/AffineCoefficientSubspace.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/ResidueBoxSliceCoordinateDisintegration.lean`, `Lattices/ResidueSliceNormalizedCell.lean`, `Linear/BasisGradedCoordinateBasis.lean`, `Linear/BasisProjectionRealification.lean`, `Linear/GradeProjectionRemainder.lean`, `Linear/QuotientProjectionCoordinates.lean`, `Linear/WeightedLieUpperSpan.lean`, `Nilpotent/BCHNonlinearRemainder.lean`, `Nilpotent/BCHOuterGridChangeBasis.lean`, `Nilpotent/BCHSubgroupGridExistence.lean`, `Nilpotent/LieBCHContinuity.lean`, `Nilpotent/LinearBCHAbelian.lean`, `Polynomial/LieCoordinatePolynomials.lean`, `Polynomial/MajorTranslationPolynomialSymbolDegree.lean`, `Polynomial/PolynomialIntegerInputs.lean`, `Polynomial/PolynomialShearFactorialIntegrality.lean`, `Polynomial/PolynomialShearRealGroup.lean`, `Polynomial/PolynomialTranslationExponentialSeries.lean`, `Polynomial/PolynomialTranslationSeries.lean`, `Polynomial/WeightedLinearPolynomialRestriction.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B040
import Definitions.Def_OAIE3v2B041
import Definitions.Def_OAIE3v2B042
import Definitions.Def_OAIE3v2B046

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuarticBohrProgression
namespace OAI

section

open scoped BigOperators Matrix Pointwise

namespace Erdos3.BohrProgression

open Erdos3.BohrLattice.BoxCertificate
open Erdos3.BohrLattice.MinkowskiSecondBox

noncomputable section

namespace CyclicCenteredGAP

lemma coeff_sub_abs_le_two_mul {N : ℕ} (Q : CyclicCenteredGAP N)
    (x y : Q.Param) (i : Fin Q.rank) :
    |Q.coeff x i - Q.coeff y i| ≤ (2 * Q.radius i : ℕ) := by
  calc
    |Q.coeff x i - Q.coeff y i| ≤
        |Q.coeff x i| + |Q.coeff y i| := abs_sub _ _
    _ ≤ (Q.radius i : ℤ) + Q.radius i :=
      add_le_add (Q.coeff_abs_le x i) (Q.coeff_abs_le y i)
    _ = (2 * Q.radius i : ℕ) := by push_cast; ring

end CyclicCenteredGAP

noncomputable def bohrSuccessiveCertificate {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R) :
    SuccessiveProductCertificate
      (Submodule.span ℤ (Set.range (bohrLatticeBasis Gamma hN))).toAddSubgroup
      (fun _ => R)
      (minkowskiSecondConstant (Gamma.card + 1) *
        |(Matrix.of (bohrLatticeBasis Gamma hN)).det| *
          (∏ _i : Fin (Gamma.card + 1), R)⁻¹) :=
  Classical.choice
    (realBox_has_minkowskiSecondCertificate
      (bohrLatticeBasis Gamma hN) (fun _ => R) (fun _ => hR))

noncomputable def bohrCertificateCoeff {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) : Fin (Gamma.card + 1) → ℤ :=
  Classical.choose
    ((Submodule.mem_span_range_iff_exists_fun ℤ).mp
      ((bohrSuccessiveCertificate Gamma hN R hR).point_mem i))

lemma bohrCertificateCoeff_spec {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    ∑ j, bohrCertificateCoeff Gamma hN R hR i j •
        bohrLatticeBasis Gamma hN j =
      (bohrSuccessiveCertificate Gamma hN R hR).point i :=
  Classical.choose_spec
    ((Submodule.mem_span_range_iff_exists_fun ℤ).mp
      ((bohrSuccessiveCertificate Gamma hN R hR).point_mem i))

noncomputable def bohrCertificatePoint {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) : Fin (Gamma.card + 1) → ℤ :=
  bohrLatticePoint Gamma (bohrCertificateCoeff Gamma hN R hR i)

lemma intCastVec_bohrCertificatePoint {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    intCastVec (bohrCertificatePoint Gamma hN R hR i) =
      (bohrSuccessiveCertificate Gamma hN R hR).point i := by
  rw [bohrCertificatePoint, intCastVec_bohrLatticePoint]
  rw [← bohrCertificateCoeff_spec Gamma hN R hR i]
  funext k
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [bohrLatticeBasis_apply]
  simp [intCastVec, mul_comm]

lemma bohrCertificatePoint_independent {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R) :
    LinearIndependent ℝ (fun i =>
      intCastVec (bohrCertificatePoint Gamma hN R hR i)) := by
  simpa only [intCastVec_bohrCertificatePoint] using
    (bohrSuccessiveCertificate Gamma hN R hR).independent

lemma bohrCertificate_scale_pos {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    0 < (bohrSuccessiveCertificate Gamma hN R hR).scale i := by
  let C := bohrSuccessiveCertificate Gamma hN R hR
  have hs := C.scale_nonneg i
  refine hs.lt_of_ne ?_
  intro hz
  have hpzero : C.point i = 0 := by
    have hm := C.mem_scaledBox i
    rw [← hz, zero_smul] at hm
    ext j
    have hlo := hm.1 j
    have hhi := hm.2 j
    simp only [Pi.zero_apply, neg_zero] at hlo hhi
    exact le_antisymm hhi hlo
  exact C.independent.ne_zero i hpzero

noncomputable def bohrProgressionRadius {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) : ℕ :=
  ⌊((4 * (Gamma.card + 1) : ℝ) *
      (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹⌋₊

noncomputable def bohrCyclicProgression {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R) :
    CyclicCenteredGAP N where
  rank := Gamma.card + 1
  step i := (bohrCertificatePoint Gamma hN R hR i 0 : ZMod N)
  radius := bohrProgressionRadius Gamma hN R hR

lemma bohrProgressionRadius_mul_scale_le {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    (bohrProgressionRadius Gamma hN R hR i : ℝ) *
        (bohrSuccessiveCertificate Gamma hN R hR).scale i ≤
      1 / (4 * (Gamma.card + 1) : ℝ) := by
  let s := (bohrSuccessiveCertificate Gamma hN R hR).scale i
  have hs : 0 < s := bohrCertificate_scale_pos Gamma hN R hR i
  have hm : (0 : ℝ) < 4 * (Gamma.card + 1) := by positivity
  have hfloor :
      (bohrProgressionRadius Gamma hN R hR i : ℝ) ≤
        ((4 * (Gamma.card + 1) : ℝ) * s)⁻¹ := by
    apply Nat.floor_le
    positivity
  calc
    (bohrProgressionRadius Gamma hN R hR i : ℝ) * s ≤
        ((4 * (Gamma.card + 1) : ℝ) * s)⁻¹ * s :=
      mul_le_mul_of_nonneg_right hfloor hs.le
    _ = 1 / (4 * (Gamma.card + 1) : ℝ) := by
      field_simp

lemma abs_intCast_bohrCertificatePoint_le {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i j : Fin (Gamma.card + 1)) :
    |(bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
      (bohrSuccessiveCertificate Gamma hN R hR).scale i * R := by
  let C := bohrSuccessiveCertificate Gamma hN R hR
  have hm := C.mem_scaledBox i
  have hlo := hm.1 j
  have hhi := hm.2 j
  rw [← intCastVec_bohrCertificatePoint Gamma hN R hR i] at hlo hhi
  change -(C.scale i * R) ≤
      (bohrCertificatePoint Gamma hN R hR i j : ℝ) at hlo
  change (bohrCertificatePoint Gamma hN R hR i j : ℝ) ≤
      C.scale i * R at hhi
  exact (abs_le.mpr ⟨hlo, hhi⟩)

def bohrCertificateCombination {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (u : Fin (Gamma.card + 1) → ℤ) : Fin (Gamma.card + 1) → ℤ :=
  fun j => ∑ i, u i * bohrCertificatePoint Gamma hN R hR i j

lemma bohrCertificateCombination_cast_coordinate {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (u : Fin (Gamma.card + 1) → ℤ) (j : Fin (Gamma.card + 1)) :
    (bohrCertificateCombination Gamma hN R hR u j : ZMod N) =
      (bohrCertificateCombination Gamma hN R hR u 0 : ZMod N) *
        indexedCyclicCharacter Gamma j := by
  simp only [bohrCertificateCombination, Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hp := bohrLatticePoint_cast_coordinate Gamma
    (bohrCertificateCoeff Gamma hN R hR i) hN j
  change (bohrCertificatePoint Gamma hN R hR i j : ZMod N) =
    (bohrCertificatePoint Gamma hN R hR i 0 : ZMod N) *
      indexedCyclicCharacter Gamma j at hp
  rw [hp]
  ring

lemma abs_intCast_bohrCertificateCombination_le {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (a : ℕ) (u : Fin (Gamma.card + 1) → ℤ)
    (hu : ∀ i, |u i| ≤ (a * bohrProgressionRadius Gamma hN R hR i : ℕ))
    (j : Fin (Gamma.card + 1)) :
    |(bohrCertificateCombination Gamma hN R hR u j : ℝ)| ≤
      (a : ℝ) * R / 4 := by
  let m := Gamma.card + 1
  have hm : (0 : ℝ) < m := by positivity
  have hR0 : 0 ≤ R := hR.le
  have hterm (i : Fin m) :
      |(u i : ℝ) *
          (bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
        (a : ℝ) * R / (4 * m : ℝ) := by
    rw [abs_mul]
    have huR : |(u i : ℝ)| ≤
        (a : ℝ) * bohrProgressionRadius Gamma hN R hR i := by
      rw [← Int.cast_abs]
      exact_mod_cast hu i
    calc
      |(u i : ℝ)| *
          |(bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
        ((a : ℝ) * bohrProgressionRadius Gamma hN R hR i) *
          ((bohrSuccessiveCertificate Gamma hN R hR).scale i * R) := by
            gcongr
            exact abs_intCast_bohrCertificatePoint_le Gamma hN R hR i j
      _ = (a : ℝ) *
          ((bohrProgressionRadius Gamma hN R hR i : ℝ) *
            (bohrSuccessiveCertificate Gamma hN R hR).scale i) * R := by ring
      _ ≤ (a : ℝ) * (1 / (4 * m : ℝ)) * R := by
        gcongr
        simpa [m, Nat.cast_add, Nat.cast_one] using
          bohrProgressionRadius_mul_scale_le Gamma hN R hR i
      _ = (a : ℝ) * R / (4 * m : ℝ) := by ring
  have hcast : (bohrCertificateCombination Gamma hN R hR u j : ℝ) =
      ∑ i, (u i : ℝ) *
        (bohrCertificatePoint Gamma hN R hR i j : ℝ) := by
    simp [bohrCertificateCombination]
  rw [hcast]
  calc
    |∑ i, (u i : ℝ) *
        (bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
      ∑ i, |(u i : ℝ) *
        (bohrCertificatePoint Gamma hN R hR i j : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, ((a : ℝ) * R / (4 * m : ℝ)) := by
      exact Finset.sum_le_sum fun i hi => hterm i
    _ = (a : ℝ) * R / 4 := by
      simp [m]
      field_simp

lemma eval_bohrCyclicProgression {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (x : (bohrCyclicProgression Gamma hN R hR).Param) :
    (bohrCyclicProgression Gamma hN R hR).eval x =
      (bohrCertificateCombination Gamma hN R hR
        ((bohrCyclicProgression Gamma hN R hR).coeff x) 0 : ZMod N) := by
  simp only [CyclicCenteredGAP.eval, bohrCyclicProgression,
    bohrCertificateCombination, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

theorem bohrCyclicProgression_proper {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (hsmall : R < 2 * N) :
    (bohrCyclicProgression Gamma hN R hR).Proper := by
  let Q := bohrCyclicProgression Gamma hN R hR
  intro x y hxy
  let u : Fin (Gamma.card + 1) → ℤ := fun i => Q.coeff x i - Q.coeff y i
  let v := bohrCertificateCombination Gamma hN R hR u
  have hu (i : Fin (Gamma.card + 1)) :
      |u i| ≤ (2 * bohrProgressionRadius Gamma hN R hR i : ℕ) := by
    exact CyclicCenteredGAP.coeff_sub_abs_le_two_mul Q x y i
  have hv0cast : (v 0 : ZMod N) = 0 := by
    have hx := eval_bohrCyclicProgression Gamma hN R hR x
    have hy := eval_bohrCyclicProgression Gamma hN R hR y
    have hvsub : (v 0 : ZMod N) =
        (bohrCyclicProgression Gamma hN R hR).eval x -
          (bohrCyclicProgression Gamma hN R hR).eval y := by
      rw [hx, hy]
      simp only [v, u, bohrCertificateCombination, Int.cast_sum, Int.cast_mul,
        Int.cast_sub]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hvsub, hxy, sub_self]
  have hvcast (j : Fin (Gamma.card + 1)) : (v j : ZMod N) = 0 := by
    rw [bohrCertificateCombination_cast_coordinate Gamma hN R hR u j,
      hv0cast, zero_mul]
  have hvabs (j : Fin (Gamma.card + 1)) : |(v j : ℝ)| ≤ R / 2 := by
    convert abs_intCast_bohrCertificateCombination_le Gamma hN R hR 2 u hu j
      using 1; norm_num; ring
  have hvzero : v = 0 := by
    funext j
    apply int_eq_zero_of_cast_zmod_eq_zero_of_abs_lt (hvcast j)
    exact (hvabs j).trans_lt (by linarith)
  have hsum : ∑ i, (u i : ℝ) •
      intCastVec (bohrCertificatePoint Gamma hN R hR i) = 0 := by
    funext j
    have hj := congrFun hvzero j
    have hjR : (v j : ℝ) = 0 := by exact_mod_cast hj
    simpa [v, bohrCertificateCombination, intCastVec] using hjR
  have huR : ∀ i, (u i : ℝ) = 0 :=
    (Fintype.linearIndependent_iff.mp
      (bohrCertificatePoint_independent Gamma hN R hR)) _ hsum
  have hu0 : u = 0 := by
    funext i
    change u i = 0
    exact_mod_cast huR i
  funext i
  apply Fin.ext
  have hi0 : u i = 0 := by
    change u i = (0 : Fin (Gamma.card + 1) → ℤ) i
    exact congrFun hu0 i
  have hi : (x i : ℤ) = (y i : ℤ) := by
    dsimp only [u, Q] at hi0
    simp only [CyclicCenteredGAP.coeff] at hi0
    omega
  exact_mod_cast hi

lemma inv_scale_le_two_mul_bohrProgressionRadius_add_one
    {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    (((4 * (Gamma.card + 1) : ℝ) *
        (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹) ≤
      2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1 := by
  have hlt := Nat.lt_floor_add_one
    (((4 * (Gamma.card + 1) : ℝ) *
      (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹)
  change (((4 * (Gamma.card + 1) : ℝ) *
      (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹) <
    (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1 at hlt
  have hradius : 0 ≤ (bohrProgressionRadius Gamma hN R hR i : ℝ) := by
    positivity
  linarith

theorem bohrCyclicProgression_card_lower_bound {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (hsmall : R < 2 * N) :
    ((((4 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1)) *
        (minkowskiSecondConstant (Gamma.card + 1) *
          (N : ℝ) ^ Gamma.card *
            (R ^ (Gamma.card + 1))⁻¹))⁻¹) ≤
      ((bohrCyclicProgression Gamma hN R hR).carrier.card : ℝ) := by
  let c : ℝ := 4 * (Gamma.card + 1)
  let B : ℝ := minkowskiSecondConstant (Gamma.card + 1) *
    |(Matrix.of (bohrLatticeBasis Gamma hN)).det| *
      (∏ _i : Fin (Gamma.card + 1), R)⁻¹
  have hc : 0 < c := by positivity
  have hscale (i : Fin (Gamma.card + 1)) :
      0 < (bohrSuccessiveCertificate Gamma hN R hR).scale i := by
    exact bohrCertificate_scale_pos Gamma hN R hR i
  have hprodscale : 0 <
      ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i := by
    exact Finset.prod_pos fun i _ => hscale i
  have hB : 0 < B := by
    simp only [B, abs_det_matrixOf_bohrLatticeBasis Gamma hN,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    unfold minkowskiSecondConstant
    positivity
  have hcertificate :
      (∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i) ≤ B := by
    exact (bohrSuccessiveCertificate Gamma hN R hR).product_le
  have hreciprocal : (c ^ (Gamma.card + 1) * B)⁻¹ ≤
      (c ^ (Gamma.card + 1) *
        ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ := by
    apply (inv_le_inv₀ (mul_pos (pow_pos hc _) hB)
      (mul_pos (pow_pos hc _) hprodscale)).2
    exact mul_le_mul_of_nonneg_left hcertificate (pow_nonneg hc.le _)
  have hproduct :
      (c ^ (Gamma.card + 1) *
        ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ ≤
      ∏ i : Fin (Gamma.card + 1),
        (2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1) := by
    calc
      (c ^ (Gamma.card + 1) *
          ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ =
          (∏ i : Fin (Gamma.card + 1),
            c * (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ := by
            congr 1
            rw [Finset.prod_mul_distrib]
            simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∏ i : Fin (Gamma.card + 1),
          (c * (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ := by
            rw [Finset.prod_inv_distrib]
      _ ≤ ∏ i : Fin (Gamma.card + 1),
          (2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1) := by
            apply Finset.prod_le_prod
            · intro i hi
              exact inv_nonneg.mpr (mul_nonneg hc.le
                ((bohrSuccessiveCertificate Gamma hN R hR).scale_nonneg i))
            · intro i hi
              simpa [c] using
                inv_scale_le_two_mul_bohrProgressionRadius_add_one
                  Gamma hN R hR i
  have hcard := CyclicCenteredGAP.card_carrier_of_proper
    (bohrCyclicProgression Gamma hN R hR)
    (bohrCyclicProgression_proper Gamma hN R hR hsmall)
  have hBform : B = minkowskiSecondConstant (Gamma.card + 1) *
      (N : ℝ) ^ Gamma.card * (R ^ (Gamma.card + 1))⁻¹ := by
    simp [B, abs_det_matrixOf_bohrLatticeBasis Gamma hN,
      Finset.prod_const]
  calc
    ((((4 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1)) *
        (minkowskiSecondConstant (Gamma.card + 1) *
          (N : ℝ) ^ Gamma.card *
            (R ^ (Gamma.card + 1))⁻¹))⁻¹) =
        (c ^ (Gamma.card + 1) * B)⁻¹ := by
      rw [hBform]
    _ ≤ (c ^ (Gamma.card + 1) *
        ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ :=
      hreciprocal
    _ ≤ ∏ i : Fin (Gamma.card + 1),
        (2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1) := hproduct
    _ = ((bohrCyclicProgression Gamma hN R hR).carrier.card : ℝ) := by
      rw [hcard]
      norm_cast

end

end Erdos3.BohrProgression

end

section

namespace Erdos3.BohrProgression

open scoped BigOperators
open BohrLattice.MinkowskiSecondBox

theorem bohrCyclicProgression_carrier_subset {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (hsmall : 2 * R ≤ B.radius * N) :
    (bohrCyclicProgression B.frequencies hN R hR).carrier ⊆ B.carrier := by
  intro z hz
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hz
  rw [CyclicBohr.Set.mem_carrier]
  intro k hk
  let Γ := B.frequencies
  let i : Fin Γ.card := Γ.equivFin ⟨k, hk⟩
  let u : Fin (Γ.card + 1) → ℤ :=
    (bohrCyclicProgression Γ hN R hR).coeff x
  let v := bohrCertificateCombination Γ hN R hR u
  have hu (j : Fin (Γ.card + 1)) :
      |u j| ≤ (bohrProgressionRadius Γ hN R hR j : ℕ) :=
    CyclicCenteredGAP.coeff_abs_le (bohrCyclicProgression Γ hN R hR) x j
  have heval : (bohrCyclicProgression Γ hN R hR).eval x = (v 0 : ZMod N) :=
    eval_bohrCyclicProgression Γ hN R hR x
  have hchar : indexedCyclicCharacter Γ i.succ = k := by
    change ((Γ.equivFin.symm i : Γ) : ZMod N) = k
    simp [i]
  have hvchar : k * (bohrCyclicProgression Γ hN R hR).eval x =
      (v i.succ : ZMod N) := by
    rw [bohrCertificateCombination_cast_coordinate Γ hN R hR u i.succ,
      hchar, heval, mul_comm]
  have hvabs : |(v i.succ : ℝ)| ≤ R / 4 := by
    simpa using abs_intCast_bohrCertificateCombination_le Γ hN R hR 1 u
      (by simpa using hu) i.succ
  refine (CyclicBohr.norm_one_sub_character_le_of_mul_eq_intCast
    k _ (v i.succ) hvchar).trans ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  apply (div_le_iff₀ hNpos).2
  nlinarith

theorem exists_proper_progression_subset {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) (hB : 0 < B.radius) (hB1 : B.radius ≤ 1)
    (hN : 1 < N) :
    ∃ Q : CyclicCenteredGAP N,
      Q.rank = B.rank + 1 ∧ Q.Proper ∧ Q.carrier ⊆ B.carrier ∧
      (N : ℝ) * (B.radius / (8 * (B.rank + 1))) ^ (B.rank + 1) /
        minkowskiSecondConstant (B.rank + 1) ≤ (Q.carrier.card : ℝ) := by
  let R := B.radius * N / 2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hR : 0 < R := by dsimp [R]; positivity
  have hsmall : R < 2 * N := by dsimp [R]; nlinarith
  refine ⟨bohrCyclicProgression B.frequencies hN R hR, rfl,
    bohrCyclicProgression_proper B.frequencies hN R hR hsmall,
    bohrCyclicProgression_carrier_subset B hN R hR (by dsimp [R]; linarith), ?_⟩
  have hcard := bohrCyclicProgression_card_lower_bound B.frequencies hN R hR hsmall
  have hn : (0 : ℝ) < B.rank + 1 := by positivity
  have hc : 0 < minkowskiSecondConstant (B.rank + 1) := by
    unfold minkowskiSecondConstant
    positivity
  have heq :
      (N : ℝ) * (B.radius / (8 * (B.rank + 1))) ^ (B.rank + 1) /
          minkowskiSecondConstant (B.rank + 1) =
        (((4 * (B.rank + 1) : ℝ) ^ (B.rank + 1)) *
          (minkowskiSecondConstant (B.rank + 1) * (N : ℝ) ^ B.rank *
            (R ^ (B.rank + 1))⁻¹))⁻¹ := by
    dsimp [R]
    simp only [div_pow, mul_pow, pow_succ, mul_inv_rev, inv_inv]
    field_simp
    rw [show (8 : ℝ) ^ B.rank = (2 : ℝ) ^ B.rank * 4 ^ B.rank by
      rw [← mul_pow]; norm_num]
    ring
  rw [heq]
  exact hcard

end Erdos3.BohrProgression

end

section

namespace Erdos3.BohrProgression

open BohrLattice.MinkowskiSecondBox

theorem exists_large_proper_progression {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) (hB : 0 < B.radius) (hB1 : B.radius ≤ 1)
    (hN : 1 < N) {w : ℝ} (hwidth : Real.exp (-w) ≤ B.radius) :
    ∃ Q : CyclicCenteredGAP N,
      Q.rank = B.rank + 1 ∧ Q.Proper ∧ Q.carrier ⊆ B.carrier ∧
      Real.exp (-(((B.rank : ℝ) + 1) * w + 10 * ((B.rank : ℝ) + 1) ^ 2)) * N ≤
        (Q.carrier.card : ℝ) := by
  obtain ⟨Q, hr, hQ, hsub, hcard⟩ := exists_proper_progression_subset B hB hB1 hN
  refine ⟨Q, hr, hQ, hsub, ?_⟩
  have hfactor := progression_size_factor_lower_bound (B.rank + 1) (by omega) hwidth
  push_cast at hfactor
  calc
    _ ≤ ((B.radius / (8 * ((B.rank : ℝ) + 1))) ^ (B.rank + 1) /
        minkowskiSecondConstant (B.rank + 1)) * N :=
      mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg N)
    _ = _ := by ring
    _ ≤ _ := hcard

end Erdos3.BohrProgression

end

section

namespace Erdos3.BohrProgression

namespace CyclicCenteredGAP

@[simp] lemma zero_carrier (N : ℕ) : (zero N).carrier = {0} := by
  have heval : (zero N).eval = fun _ => 0 := by
    funext x
    unfold eval
    exact Finset.sum_eq_zero fun i _ => Fin.elim0 i
  rw [carrier, heval]
  exact Finset.image_const ⟨(fun i => Fin.elim0 i), Finset.mem_univ _⟩ 0

end CyclicCenteredGAP

theorem exists_large_proper_progression_all {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) (hB : 0 < B.radius) (hB1 : B.radius ≤ 1)
    {w : ℝ} (hw : 0 ≤ w) (hwidth : Real.exp (-w) ≤ B.radius) :
    ∃ Q : CyclicCenteredGAP N,
      Q.rank ≤ B.rank + 1 ∧ Q.Proper ∧ Q.carrier ⊆ B.carrier ∧
      Real.exp (-(((B.rank : ℝ) + 1) * w + 10 * ((B.rank : ℝ) + 1) ^ 2)) * N ≤
        (Q.carrier.card : ℝ) := by
  by_cases hN : 1 < N
  · obtain ⟨Q, hr, hQ, hsub, hcard⟩ := exists_large_proper_progression B hB hB1 hN hwidth
    exact ⟨Q, hr.le, hQ, hsub, hcard⟩
  · have hNeq : N = 1 := by have := NeZero.pos N; omega
    subst N
    refine ⟨CyclicCenteredGAP.zero 1, by simp [CyclicCenteredGAP.zero],
      CyclicCenteredGAP.zero_proper 1, ?_, ?_⟩
    · intro x hx
      rw [CyclicCenteredGAP.zero_carrier, Finset.mem_singleton] at hx
      subst x
      exact B.zero_mem
    · simp only [CyclicCenteredGAP.zero_carrier, Finset.card_singleton, Nat.cast_one,
        mul_one]
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ ((B.rank : ℝ) + 1) * w + 10 * ((B.rank : ℝ) + 1) ^ 2 := by positivity
      linarith

end Erdos3.BohrProgression

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CyclicProgressionCoordinates
namespace OAI

section

open scoped BigOperators

namespace Erdos3.BohrProgression

namespace CyclicCenteredGAP

variable {N : ℕ}

def unitParam (Q : CyclicCenteredGAP N) (i : Fin Q.rank)
    (hi : 0 < Q.radius i) : Q.Param := fun j =>
  if hji : j = i then ⟨1, by subst j; omega⟩ else 0

@[simp] lemma unitParam_apply_self (Q : CyclicCenteredGAP N)
    (i : Fin Q.rank) (hi : 0 < Q.radius i) :
    (Q.unitParam i hi i : ℕ) = 1 := by
  simp [unitParam]

@[simp] lemma unitParam_apply_ne (Q : CyclicCenteredGAP N)
    (i j : Fin Q.rank) (hi : 0 < Q.radius i) (hji : j ≠ i) :
    (Q.unitParam i hi j : ℕ) = 0 := by
  simp [unitParam, hji]

@[simp] lemma predParam_apply_self (Q : CyclicCenteredGAP N)
    (x : Q.Param) (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) :
    (Q.predParam x i hi i : ℕ) = (x i : ℕ) - 1 := by
  simp [predParam]

@[simp] lemma predParam_apply_ne (Q : CyclicCenteredGAP N)
    (x : Q.Param) (i j : Fin Q.rank) (hi : 0 < (x i : ℕ))
    (hji : j ≠ i) :
    (Q.predParam x i hi j : ℕ) = x j := by
  simp [predParam, hji]

lemma eval_eq_eval_minParam_add_sum {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (x : Q.Param) :
    Q.eval x = Q.eval Q.minParam +
      ∑ i, (x i : ZMod N) * Q.step i := by
  simp only [eval, coeff, minParam, Fin.val_zero,
    Nat.cast_zero, Int.cast_sub, Int.cast_natCast,
    zero_sub]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Int.cast_neg, Int.cast_natCast]
  ring

lemma eval_unitParam {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (i : Fin Q.rank) (hi : 0 < Q.radius i) :
    Q.eval (Q.unitParam i hi) = Q.eval Q.minParam + Q.step i := by
  rw [Q.eval_eq_eval_minParam_add_sum]
  congr 1
  rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
  simp only [unitParam_apply_self, Nat.cast_one, one_mul]
  have hzero : ∑ j ∈ Finset.univ.erase i,
      ((Q.unitParam i hi j : ℕ) : ZMod N) * Q.step j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j ≠ i := by
      exact Finset.ne_of_mem_erase hj
    simp [Q.unitParam_apply_ne i j hi hji]
  rw [hzero, zero_add]

lemma eval_predParam_add_eval_unitParam {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ))
    (hradius : 0 < Q.radius i) :
    Q.eval (Q.predParam x i hi) + Q.eval (Q.unitParam i hradius) =
      Q.eval x + Q.eval Q.minParam := by
  have hpred := Q.eval_eq_eval_minParam_add_sum (Q.predParam x i hi)
  have hunit := Q.eval_unitParam i hradius
  have hx := Q.eval_eq_eval_minParam_add_sum x
  rw [hpred, hunit, hx]
  have hsum :
      (∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
          Q.step i =
        ∑ j, (x j : ZMod N) * Q.step j := by
    rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
    rw [← Finset.sum_erase_add (Finset.univ)
      (fun j => (x j : ZMod N) * Q.step j) (Finset.mem_univ i)]
    have hrest : ∑ j ∈ Finset.univ.erase i,
        ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j =
      ∑ j ∈ Finset.univ.erase i, (x j : ZMod N) * Q.step j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [Q.predParam_apply_ne x i j hi hji]
    rw [hrest, Q.predParam_apply_self]
    have hxi : (x i : ℕ) - 1 + 1 = x i := Nat.sub_add_cancel hi
    rw [← hxi]
    push_cast
    ring
  calc
    Q.eval Q.minParam +
          (∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
          (Q.eval Q.minParam + Q.step i) =
        Q.eval Q.minParam + Q.eval Q.minParam +
          ((∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
            Q.step i) := by abel
    _ = Q.eval Q.minParam + Q.eval Q.minParam +
          ∑ j, (x j : ZMod N) * Q.step j := by rw [hsum]
    _ = Q.eval Q.minParam + (∑ j, (x j : ZMod N) * Q.step j) +
          Q.eval Q.minParam := by abel

lemma sum_predParam_add_one (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) :
    (∑ j, (Q.predParam x i hi j : ℕ)) + 1 = ∑ j, (x j : ℕ) := by
  rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ)
    (fun j => (x j : ℕ)) (Finset.mem_univ i)]
  have hrest : ∑ j ∈ Finset.univ.erase i,
      (Q.predParam x i hi j : ℕ) =
        ∑ j ∈ Finset.univ.erase i, (x j : ℕ) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Q.predParam_apply_ne x i j hi (Finset.ne_of_mem_erase hj)
  rw [hrest, Q.predParam_apply_self]
  omega

end CyclicCenteredGAP

end Erdos3.BohrProgression

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicProgressionHom
namespace OAI

section

namespace Erdos3.BohrProgression.CyclicCenteredGAP

open scoped BigOperators

variable {N : ℕ} {G : Type*} [AddCommGroup G]

lemma sum_predParam_smul_add (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) (v : Fin Q.rank → G) :
    (∑ j, (Q.predParam x i hi j : ℕ) • v j) + v i = ∑ j, (x j : ℕ) • v j := by
  classical
  rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ)
    (fun j => (x j : ℕ) • v j) (Finset.mem_univ i)]
  have hrest : ∑ j ∈ Finset.univ.erase i, (Q.predParam x i hi j : ℕ) • v j =
      ∑ j ∈ Finset.univ.erase i, (x j : ℕ) • v j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Q.predParam_apply_ne x i j hi (Finset.ne_of_mem_erase hj)]
  have hterm : ((x i : ℕ) - 1) • v i + v i = (x i : ℕ) • v i := by
    simpa only [add_nsmul, one_nsmul] using
      congrArg (fun n : ℕ => n • v i) (Nat.sub_add_cancel hi)
  rw [hrest, Q.predParam_apply_self, add_assoc, hterm]

noncomputable def freimanStep (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (i : Fin Q.rank) : G :=
  if hi : 0 < Q.radius i then L (Q.eval (Q.unitParam i hi)) - L (Q.eval Q.minParam)
  else 0

noncomputable def freimanAffine (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (x : Q.Param) : G :=
  L (Q.eval Q.minParam) + ∑ i, (x i : ℕ) • Q.freimanStep L i

lemma freimanAffine_pred_add_step (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (x : Q.Param) (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) :
    Q.freimanAffine L x = Q.freimanAffine L (Q.predParam x i hi) + Q.freimanStep L i := by
  unfold freimanAffine
  rw [add_assoc, Q.sum_predParam_smul_add]

theorem freimanAffine_eq [NeZero N] (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (hadd : ∀ x y z t : Q.Param,
      Q.eval x + Q.eval y = Q.eval z + Q.eval t →
        L (Q.eval x) + L (Q.eval y) = L (Q.eval z) + L (Q.eval t))
    (x : Q.Param) : Q.freimanAffine L x = L (Q.eval x) := by
  classical
  induction hweight : (∑ i, (x i : ℕ)) using Nat.strong_induction_on generalizing x with
  | h k ih =>
    by_cases hk : k = 0
    · have hsumzero : ∑ i, (x i : ℕ) = 0 := hweight.trans hk
      have hxzero (i : Fin Q.rank) : (x i : ℕ) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp
          hsumzero i (Finset.mem_univ i)
      have hx : x = Q.minParam := by
        funext i
        apply Fin.ext
        exact hxzero i
      subst x
      simp [freimanAffine, minParam]
    · have hsumpos : 0 < ∑ i, (x i : ℕ) := by omega
      rw [Finset.sum_pos_iff_of_nonneg (by simp)] at hsumpos
      obtain ⟨i, _hiuniv, hi⟩ := hsumpos
      have hradius : 0 < Q.radius i := by
        have hix := (x i).isLt
        change (x i : ℕ) < 2 * Q.radius i + 1 at hix
        omega
      let y := Q.predParam x i hi
      have hyweight : (∑ j, (y j : ℕ)) + 1 = ∑ j, (x j : ℕ) :=
        Q.sum_predParam_add_one x i hi
      have hylt : (∑ j, (y j : ℕ)) < k := by omega
      have ihy : Q.freimanAffine L y = L (Q.eval y) := ih _ hylt y rfl
      have hrel := hadd y (Q.unitParam i hradius) x Q.minParam
        (Q.eval_predParam_add_eval_unitParam x i hi hradius)
      rw [Q.freimanAffine_pred_add_step L x i hi, ihy]
      simp only [freimanStep, dif_pos hradius]
      calc
        L (Q.eval y) + (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam)) =
            (L (Q.eval y) + L (Q.eval (Q.unitParam i hradius))) - L (Q.eval Q.minParam) := by abel
        _ = L (Q.eval x) := by rw [hrel, add_sub_cancel_right]

end Erdos3.BohrProgression.CyclicCenteredGAP

end

section

namespace Erdos3.BohrProgression.CyclicCenteredGAP

open scoped BigOperators

variable {N : ℕ} {G : Type*} [AddCommGroup G]

def centerParam (Q : CyclicCenteredGAP N) : Q.Param := fun i => ⟨Q.radius i, by omega⟩

@[simp] lemma eval_centerParam (Q : CyclicCenteredGAP N) : Q.eval Q.centerParam = 0 := by
  simp [eval, coeff, centerParam]

lemma eval_mem_carrier (Q : CyclicCenteredGAP N) (x : Q.Param) : Q.eval x ∈ Q.carrier :=
  Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

noncomputable def coefficientBox (Q : CyclicCenteredGAP N) : Finset (Fin Q.rank → ℤ) :=
  Finset.univ.image Q.coeff

lemma mem_coefficientBox (Q : CyclicCenteredGAP N) {z : Fin Q.rank → ℤ} :
    z ∈ Q.coefficientBox ↔ ∃ x : Q.Param, Q.coeff x = z := by
  simp [coefficientBox]

lemma mem_coefficientBox_iff_abs_le (Q : CyclicCenteredGAP N) {z : Fin Q.rank → ℤ} :
    z ∈ Q.coefficientBox ↔ ∀ i, |z i| ≤ (Q.radius i : ℤ) := by
  rw [Q.mem_coefficientBox]
  constructor
  · rintro ⟨x, rfl⟩
    exact Q.coeff_abs_le x
  · intro hz
    let x : Q.Param := fun i => ⟨(z i + Q.radius i).toNat, by
      have hi := abs_le.mp (hz i)
      omega⟩
    refine ⟨x, ?_⟩
    funext i
    have hi := abs_le.mp (hz i)
    dsimp [coeff, x]
    omega

noncomputable def freimanHom (Q : CyclicCenteredGAP N) (L : ZMod N → G) :
    (Fin Q.rank → ℤ) →+ G where
  toFun z := ∑ i, z i • Q.freimanStep L i
  map_zero' := by simp
  map_add' x y := by simp [add_zsmul, Finset.sum_add_distrib]

theorem freimanHom_coeff [NeZero N] (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (hzero : L 0 = 0)
    (hadd : ∀ x y z t : Q.Param,
      Q.eval x + Q.eval y = Q.eval z + Q.eval t →
        L (Q.eval x) + L (Q.eval y) = L (Q.eval z) + L (Q.eval t))
    (x : Q.Param) : Q.freimanHom L (Q.coeff x) = L (Q.eval x) := by
  have hx := Q.freimanAffine_eq L hadd x
  have hc := Q.freimanAffine_eq L hadd Q.centerParam
  simp only [freimanAffine, centerParam, eval_centerParam, hzero] at hc
  have heq : Q.freimanHom L (Q.coeff x) =
      (∑ i, (x i : ℕ) • Q.freimanStep L i) -
        ∑ i, Q.radius i • Q.freimanStep L i := by
    change (∑ i, Q.coeff x i • Q.freimanStep L i) = _
    simp only [coeff, sub_zsmul, natCast_zsmul]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [heq]
  change L (Q.eval Q.minParam) + (∑ i, (x i : ℕ) • Q.freimanStep L i) = _ at hx
  have hbase : L (Q.eval Q.minParam) = -(∑ i, Q.radius i • Q.freimanStep L i) :=
    eq_neg_of_add_eq_zero_left hc
  rw [hbase] at hx
  simpa only [sub_eq_add_neg, add_comm] using hx

theorem freimanHom_injOn [NeZero N] (Q : CyclicCenteredGAP N) (hQ : Q.Proper)
    (L : ZMod N → G) (hL : Set.InjOn L (Q.carrier : Set _)) (hzero : L 0 = 0)
    (hadd : ∀ x y z t : Q.Param,
      Q.eval x + Q.eval y = Q.eval z + Q.eval t →
        L (Q.eval x) + L (Q.eval y) = L (Q.eval z) + L (Q.eval t)) :
    Set.InjOn (Q.freimanHom L) (Q.coefficientBox : Set _) := by
  intro z hz w hw hzw
  obtain ⟨x, rfl⟩ := Q.mem_coefficientBox.mp hz
  obtain ⟨y, rfl⟩ := Q.mem_coefficientBox.mp hw
  rw [Q.freimanHom_coeff L hzero hadd, Q.freimanHom_coeff L hzero hadd] at hzw
  exact congrArg Q.coeff (hQ (hL (Q.eval_mem_carrier x) (Q.eval_mem_carrier y) hzw))

theorem image_freimanHom [NeZero N] [DecidableEq G] (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (hzero : L 0 = 0)
    (hadd : ∀ x y z t : Q.Param,
      Q.eval x + Q.eval y = Q.eval z + Q.eval t →
        L (Q.eval x) + L (Q.eval y) = L (Q.eval z) + L (Q.eval t)) :
    Q.coefficientBox.image (Q.freimanHom L) = Q.carrier.image L := by
  classical
  simp only [coefficientBox, carrier, Finset.image_image]
  apply Finset.image_congr
  intro x _
  exact Q.freimanHom_coeff L hzero hadd x

end Erdos3.BohrProgression.CyclicCenteredGAP

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreePrimitiveCriterion
namespace OAI

section

namespace Erdos3
variable {X : Type*}

theorem freeTruncation_idempotent (s : ℕ) (p : FreeAlgebra ℚ X) :
    freeTruncation s (freeTruncation s p) = freeTruncation s p := by
  apply freeAlgebra_linear_induction (fun p =>
    freeTruncation s (freeTruncation s p) = freeTruncation s p)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro r p hp
    simp only [map_smul, hp]
  · intro w
    rw [freeTruncation_word]
    split_ifs with hw <;> simp [hw]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LieBCHContinuity
namespace OAI

section

namespace Erdos3

theorem bchWordExpansion_truncation (s : ℕ) :
    wordTruncation s (freeLieWordExpansion (bchLiePolynomial s)) =
      freeLieWordExpansion (bchLiePolynomial s) := by
  apply wordPolynomialEmbedding_injective
  rw [wordPolynomialEmbedding_truncation, wordPolynomialEmbedding_freeLieExpansion,
    bchLiePolynomial_expansion, freeTruncation_idempotent]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

variable {ι : Type*} {N : ι → ℕ} {q : ℕ}

def point (A : ResidueBoxSlice N q) (j : ∀ i, Fin (A.length i)) : ∀ i, Fin (N i) :=
  fun i => ⟨A.start i + q * (j i).val, A.inside i _ (j i).isLt⟩

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialIntegerInputs
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

theorem abs_aeval_sub_aeval_box_bound {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℚ)
    (v w : σ → ℝ) {A B δ : ℝ} {s : ℕ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hcoeff : ∀ m, |((P.coeff m : ℚ) : ℝ)| ≤ A)
    (hv : ∀ i, |v i| ≤ B) (hw : ∀ i, |w i| ≤ B) (hvw : ∀ i, |v i - w i| ≤ δ)
    (hdegree : P.totalDegree ≤ s) :
    |aeval v P - aeval w P| ≤
      P.support.card * A * Fintype.card σ * s * B ^ (s * (Fintype.card σ + 1)) * δ := by
  classical
  have hmonomial (m : σ →₀ ℕ) (hm : m ∈ P.support) :
      |(∏ i, v i ^ m i) - ∏ i, w i ^ m i| ≤
        Fintype.card σ * (δ * s * B ^ s) * (B ^ s) ^ Fintype.card σ := by
    have hmdeg (i : σ) : m i ≤ s :=
      (monomial_le_degreeOf i hm).trans ((degreeOf_le_totalDegree P i).trans hdegree)
    have hpow (u : σ → ℝ) (hu : ∀ i, |u i| ≤ B) (i : σ) : |u i ^ m i| ≤ B ^ s := by
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hu i) _).trans (pow_le_pow_right₀ hB (hmdeg i))
    simpa only [Finset.card_univ] using
      abs_finset_prod_sub_prod_le Finset.univ (fun i => v i ^ m i) (fun i => w i ^ m i)
        (one_le_pow₀ hB) (by positivity)
        (fun i _ => hpow v hv i) (fun i _ => hpow w hw i)
        (fun i _ => abs_pow_sub_pow_box_bound hB hδ (hv i) (hw i) (hvw i) (hmdeg i))
  change |P.eval₂ (algebraMap ℚ ℝ) v - P.eval₂ (algebraMap ℚ ℝ) w| ≤ _
  rw [eval₂_eq', eval₂_eq', ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ m ∈ P.support, |algebraMap ℚ ℝ (P.coeff m) * ∏ i, v i ^ m i -
          algebraMap ℚ ℝ (P.coeff m) * ∏ i, w i ^ m i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ P.support, A * (Fintype.card σ * (δ * s * B ^ s) * (B ^ s) ^ Fintype.card σ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [← mul_sub, abs_mul]
      exact mul_le_mul (hcoeff m) (hmonomial m hm) (abs_nonneg _) hA
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_add, Nat.mul_one, pow_add, pow_mul]
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LieCoordinatePolynomials
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {ι X L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem coordinateBracketList_totalDegree (c : ι → ι → ι → ℚ) (xs : List X)
    (p : ι → MvPolynomial (X × ι) ℚ) {n : ℕ}
    (hp : ∀ i, (p i).totalDegree ≤ n) (k : ι) :
    (coordinateBracketList c xs p k).totalDegree ≤ n + xs.length := by
  induction xs generalizing p n with
  | nil => exact hp k
  | cons x xs ih =>
    simpa only [coordinateBracketList, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 xs.length] using
      ih (coordinateRightBracket c x p) (coordinateRightBracket_totalDegree c x p hp)

theorem dynkinCoordinatePolynomial_totalDegree (c : ι → ι → ι → ℚ)
    (w : FreeSemigroup X) (k : ι) :
    (dynkinCoordinatePolynomial c w k).totalDegree ≤ w.length := by
  have h := coordinateBracketList_totalDegree c w.tail
    (fun i => MvPolynomial.X (w.head, i)) (n := 1)
    (fun _ => (totalDegree_X _).le) k
  simpa only [dynkinCoordinatePolynomial, FreeSemigroup.length, Nat.add_comm] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieCoordinateHeight
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {ι X : Type*} [Fintype ι]

theorem coordinateBracketList_height (c : ι → ι → ι → ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (xs : List X)
    (p : ι → MvPolynomial (X × ι) ℚ) {n : ℕ}
    (hp : ∀ i, RationalPolynomialHeightLE (p i) (lieCoordinateHeight (Fintype.card ι) H n))
    (k : ι) :
    RationalPolynomialHeightLE (coordinateBracketList c xs p k)
      (lieCoordinateHeight (Fintype.card ι) H (n + xs.length)) := by
  induction xs generalizing p n with
  | nil => exact hp k
  | cons x xs ih =>
    have hstep : ∀ i, RationalPolynomialHeightLE (coordinateRightBracket c x p i)
        (lieCoordinateHeight (Fintype.card ι) H (n + 1)) := fun i =>
      (coordinateRightBracket_height c hc x p hp i).mono (lieCoordinateHeight_step _ _ _)
    simpa only [coordinateBracketList, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 xs.length] using ih (coordinateRightBracket c x p) hstep

theorem dynkinCoordinatePolynomial_height (c : ι → ι → ι → ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (w : FreeSemigroup X) (k : ι) :
    RationalPolynomialHeightLE (dynkinCoordinatePolynomial c w k)
      (lieCoordinateHeight (Fintype.card ι) H w.length) := by
  have h := coordinateBracketList_height c hc w.tail
    (fun i => MvPolynomial.X (w.head, i)) (n := 0)
    (fun i => (RationalPolynomialHeightLE.X (w.head, i)).mono
      (lieCoordinateHeight_pos (Fintype.card ι) H 0)) k
  apply h.mono
  apply lieCoordinateHeight_mono_length
  change 0 + w.tail.length ≤ w.tail.length + 1
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
attribute [local instance] LieRing.ofAssociativeRing

theorem lieBCH_eq_add_of_isLieAbelian [IsLieAbelian L] {s : ℕ} (hs : 1 ≤ s) (a b : L) :
    lieBCH s a b = a + b := by
  let x : Fin 2 → FreeLieAlgebra ℚ (Fin 2) := FreeLieAlgebra.of ℚ
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 2)) 1
  have hx (i : Fin 2) : scaledFreeGenerator 1 i ∈ F.layer 1 := scaledFreeGenerator_mem_layer 1 i
  have hmul (i j : Fin 2) : scaledFreeGenerator 1 i * scaledFreeGenerator 1 j = 0 := by
    have h := F.mul_mem (hx i) (hx j)
    simpa only [F.terminal, Submodule.mem_bot] using h
  have hc : Commute (scaledFreeGenerator 1 (0 : Fin 2)) (scaledFreeGenerator 1 (1 : Fin 2)) := by
    change _ * _ = _ * _
    rw [hmul 0 1, hmul 1 0]
  have h : scaledFreeLieEval 1 (lieBCH s (x 0) (x 1)) = scaledFreeLieEval 1 (x 0 + x 1) := by
    simp only [map_lieBCH, map_add, x, scaledFreeLieEval_of]
    rw [(F.extend hs).lieBCH_eq (hx 0) (hx 1)]
    exact nilpotentBCH_eq_add_of_commute (F.isNilpotent_of_mem le_rfl (hx 0))
      (F.isNilpotent_of_mem le_rfl (hx 1)) hc
  have hn : LieModule.lowerCentralSeries ℚ L L 1 = ⊥ := by
    simp [LieModule.lowerCentralSeries_succ]
  have he := lie_lift_eq_of_scaledFreeLieEval_eq ![a, b] hn h
  simpa only [map_lieBCH, map_add, x, FreeLieAlgebra.lift_of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using he

theorem lieBCH_eq_add_of_lie_eq_zero_pos {s : ℕ} (hs : 1 ≤ s) {a b : L}
    (hab : ⁅a, b⁆ = 0) : lieBCH s a b = a + b := by
  let K := LieSubalgebra.lieSpan ℚ L ({a, b} : Set L)
  have ha : a ∈ K := LieSubalgebra.subset_lieSpan (by simp)
  have hb : b ∈ K := LieSubalgebra.subset_lieSpan (by simp)
  have : IsLieAbelian K := by
    apply LieSubalgebra.isLieAbelian_lieSpan_iff.mpr
    intro u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact lie_self _
    · exact hab
    · rw [← lie_skew, hab, neg_zero]
    · exact lie_self _
  have h := congrArg K.incl (lieBCH_eq_add_of_isLieAbelian hs (⟨a, ha⟩ : K) (⟨b, hb⟩ : K))
  simp only [map_lieBCH, map_add] at h
  change lieBCH s a b = a + b at h
  exact h

theorem lieBCH_eq_add_of_lie_eq_zero {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {a b : L}
    (hab : ⁅a, b⁆ = 0) : lieBCH s a b = a + b := by
  by_cases hs : 1 ≤ s
  · exact lieBCH_eq_add_of_lie_eq_zero_pos hs hab
  · have hs0 : s = 0 := by omega
    subst s
    have he (z : L) : z = 0 := by
      have hz : z ∈ LieModule.lowerCentralSeries ℚ L L 0 := by simp
      simpa only [hnil, LieSubmodule.mem_bot] using hz
    rw [he a, he b, zero_add, lieBCH_zero_left hnil]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
namespace OAI

section

namespace Erdos3
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
namespace NilpotentLieBCHGroup
variable {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem commute_of_lie_eq_zero (a b : NilpotentLieBCHGroup L s hnil)
    (hab : ⁅a.coord, b.coord⁆ = 0) : Commute a b := by
  apply ext
  change lieBCH s a.coord b.coord = lieBCH s b.coord a.coord
  have hba : ⁅b.coord, a.coord⁆ = 0 := by rw [← lie_skew, hab, neg_zero]
  rw [lieBCH_eq_add_of_lie_eq_zero hnil hab, lieBCH_eq_add_of_lie_eq_zero hnil hba, add_comm]

theorem commutator_mem_ideal (I : LieIdeal ℚ L) (a b : NilpotentLieBCHGroup L s hnil)
    (hab : ⁅a.coord, b.coord⁆ ∈ I) : (a * b * a⁻¹ * b⁻¹).coord ∈ I := by
  have hlie : ⁅(quotientHom I a).coord, (quotientHom I b).coord⁆ = 0 := by
    rw [quotientHom_coord, quotientHom_coord, ← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hab
  have hc := commute_of_lie_eq_zero (quotientHom I a) (quotientHom I b) hlie
  have h : quotientHom I (a * b * a⁻¹ * b⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hc.eq]
    simp [mul_assoc]
  apply (lieQuotientMap_eq_zero I _).mp
  exact congrArg coord h

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem coord_pow (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) :
    (g ^ n).coord = n • g.coord := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, coord_mul, ih,
      lieBCH_eq_add_of_lie_eq_zero hnil (by simp [nsmul_lie]), succ_nsmul]

theorem coord_pow_rat (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) :
    (g ^ n).coord = (n : ℚ) • g.coord := by
  rw [coord_pow, Nat.cast_smul_eq_nsmul ℚ]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
variable {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem descendingCentralSeries : Subgroup.IsDescendingCentralSeries
    (fun n => subgroup (hnil := hnil)
      ((LieModule.lowerCentralSeries ℚ L L n : LieIdeal ℚ L) : LieSubalgebra ℚ L)) := by
  constructor
  · apply top_unique
    intro a _
    change a.coord ∈ LieModule.lowerCentralSeries ℚ L L 0
    simp
  · intro a n ha b
    change (a * b * a⁻¹ * b⁻¹).coord ∈ LieModule.lowerCentralSeries ℚ L L (n + 1)
    apply commutator_mem_ideal
    rw [← lie_skew a.coord b.coord]
    apply (LieModule.lowerCentralSeries ℚ L L (n + 1)).neg_mem
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top b.coord) ha

theorem lowerCentralSeries_eq_bot :
    (⊤ : Subgroup (NilpotentLieBCHGroup L s hnil)).lowerCentralSeries s = ⊥ := by
  apply bot_unique
  apply (Subgroup.descending_central_series_ge_lower _ (descendingCentralSeries (hnil := hnil)) s).trans
  intro a ha
  rw [Subgroup.mem_bot]
  apply ext
  change a.coord = 0
  change a.coord ∈ LieModule.lowerCentralSeries ℚ L L s at ha
  simpa only [hnil, LieSubmodule.mem_bot] using ha

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

variable {X : Type*} (N H : X → ℕ) (lo a : X → ℤ) (M : ℕ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hne : ∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i))

noncomputable def ofPhysicalResidue : ResidueBoxSlice N M where
  start i := (a i + M * residueIndexLower (lo i) M (a i)).toNat
  length i := residueIndexLength (lo i) (lo i + H i) M (a i)
  inside i j hj := by
    have hx := (physicalResidueCoordinateEquiv (lo i) (lo i + H i) (a i) M hM
      ⟨j, hj⟩).property
    have hhigh := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).2
    rw [physicalResidueCoordinateEquiv_val] at hhigh
    have hboxhigh := (hbox i).2
    have hstart := physicalResidue_start_nonneg N H lo a M hM hbox hne i
    have hlt : ((a i + M * residueIndexLower (lo i) M (a i)).toNat : ℤ) +
        (M : ℤ) * j < N i := by
      rw [Int.toNat_of_nonneg hstart]
      nlinarith
    exact_mod_cast hlt

@[simp] theorem ofPhysicalResidue_length (i : X) :
    (ofPhysicalResidue N H lo a M hM hbox hne).length i =
      residueIndexLength (lo i) (lo i + H i) M (a i) := rfl

@[simp] theorem ofPhysicalResidue_start (i : X) :
    (ofPhysicalResidue N H lo a M hM hbox hne).start i =
      (a i + M * residueIndexLower (lo i) M (a i)).toNat := rfl

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieTreeMultidegree
namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem lieTree_length_le_weight (w : I → ℕ) (hw : ∀ i, 0 < w i) (a : FreeMagma I) :
    a.length ≤ lieTreeWeight w a := by
  induction a using FreeMagma.rec with
  | of i => exact hw i
  | mul a b ha hb => exact Nat.add_le_add ha hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basisBelowProjection_eq_sum_grades (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x : V) :
    basisBelowProjection b w j x = ∑ k ∈ Finset.range j, basisGradeProjection b w k x := by
  apply b.repr.injective
  ext i
  simp [basisBelowProjection_repr, basisGradeProjection_repr]

def BasisGradedSubmodule (b : Basis ι K V) (w : ι → ℕ) (U : Submodule K V) : Prop :=
  ∀ j x, x ∈ U → basisGradeProjection b w j x ∈ U

theorem BasisGradedSubmodule.below_mem (b : Basis ι K V) (w : ι → ℕ) (U : Submodule K V)
    (hU : BasisGradedSubmodule b w U) (j : ℕ) (x : V) (hx : x ∈ U) :
    basisBelowProjection b w j x ∈ U := by
  rw [basisBelowProjection_eq_sum_grades]
  exact Submodule.sum_mem U (fun k _ => hU k x hx)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TopSupportSubstitution
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem mem_weightedSupportLE_one_iff {σ R : Type*} [CommRing R]
    (P : MvPolynomial σ R) (d : ℕ) :
    P ∈ weightedSupportLE (1 : σ → ℕ) d ↔ P.totalDegree ≤ d := by
  simpa only [weightedTotalDegree_one] using mem_weightedSupportLE_iff (1 : σ → ℕ) d P

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

namespace PolynomialTranslationGroup

noncomputable instance instGroup : Group (PolynomialTranslationGroup σ) :=
  Group.ofLeftAxioms
    (by
      intro a b c
      apply PolynomialTranslationGroup.ext
      · exact add_assoc _ _ _
      · simp only [polynomial_mul, base_mul, map_add, polynomialTranslate_comp,
          neg_add_rev, add_assoc])
    (by intro a; apply PolynomialTranslationGroup.ext <;> simp)
    (by
      intro a
      apply PolynomialTranslationGroup.ext
      · simp
      · simp [polynomialTranslate_comp])

noncomputable def exponentialElement (x : σ → ℚ) (P : MvPolynomial σ ℚ) :
    PolynomialTranslationGroup σ := ⟨x, polynomialExponentialCoordinate x P⟩

end PolynomialTranslationGroup
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationGroup

open _root_.MvPolynomial
variable {σ : Type*}

theorem actionHom_rename (g : PolynomialTranslationGroup σ) (P : MvPolynomial σ ℚ) :
    actionHom g (rename Sum.inl P) = rename Sum.inl (polynomialTranslate g.base P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP => simp only [map_mul,rename_X,actionHom_X_inl,hP,polynomialTranslate_X,
      map_add,rename_C]

@[simp] theorem actionHom_one (P : MvPolynomial (σ ⊕ Unit) ℚ) : actionHom 1 P = P := by
  have hh : actionHom (1 : PolynomialTranslationGroup σ) = AlgHom.id ℚ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp
  exact DFunLike.congr_fun hh P

theorem actionHom_mul (g h : PolynomialTranslationGroup σ)
    (P : MvPolynomial (σ ⊕ Unit) ℚ) :
    actionHom (g*h) P = actionHom g (actionHom h P) := by
  have hh : actionHom (g*h) = (actionHom g).comp (actionHom h) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl i => simp [Pi.add_apply, add_assoc]
    | inr u =>
      simp only [actionHom_X_inr,base_mul,polynomial_mul,map_add,polynomialTranslate_comp,
        AlgHom.comp_apply,actionHom_rename]
      rw [show g.base + h.base + -h.base = g.base by abel]
      abel
  exact DFunLike.congr_fun hh P

noncomputable def action (g : PolynomialTranslationGroup σ) :
    MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ] MvPolynomial (σ ⊕ Unit) ℚ :=
  { actionHom g with
    invFun := actionHom g⁻¹
    left_inv := fun P => by
      change actionHom g⁻¹ (actionHom g P) = P
      rw [← actionHom_mul, inv_mul_cancel, actionHom_one]
    right_inv := fun P => by
      change actionHom g (actionHom g⁻¹ P) = P
      rw [← actionHom_mul, mul_inv_cancel, actionHom_one] }

noncomputable def actionMonoidHom : PolynomialTranslationGroup σ →*
    (MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ] MvPolynomial (σ ⊕ Unit) ℚ) where
  toFun := action
  map_one' := by apply AlgEquiv.ext; intro P; exact actionHom_one P
  map_mul' g h := by apply AlgEquiv.ext; intro P; exact actionHom_mul g h P

theorem actionMonoidHom_injective : Function.Injective (actionMonoidHom (σ := σ)) := by
  intro g h heq
  have hb : g.base = h.base := by
    funext i
    have hh := congrArg (fun f : MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ]
      MvPolynomial (σ ⊕ Unit) ℚ => f (X (Sum.inl i))) heq
    change actionHom g (X (Sum.inl i)) = actionHom h (X (Sum.inl i)) at hh
    rw [actionHom_X_inl,actionHom_X_inl] at hh
    exact MvPolynomial.C_injective (σ ⊕ Unit) ℚ (add_left_cancel hh)
  apply PolynomialTranslationGroup.ext hb
  have hh := congrArg (fun f : MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ]
    MvPolynomial (σ ⊕ Unit) ℚ => f (X (Sum.inr ()))) heq
  change actionHom g (X (Sum.inr ())) = actionHom h (X (Sum.inr ())) at hh
  rw [actionHom_X_inr,actionHom_X_inr] at hh
  have hp := MvPolynomial.rename_injective Sum.inl Sum.inl_injective (add_left_cancel hh)
  have hp' := congrArg (polynomialTranslate (-g.base)) hp
  simpa only [hb, polynomialTranslate_comp, neg_add_cancel, polynomialTranslate_zero] using hp'

end Erdos3.PolynomialTranslationGroup

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem scalarDirectionalDerivative_pow_eq_zero_of_weightedSupport
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    ((scalarDirectionalDerivative x).toLinearMap ^ (n + 1)) P = 0 := by
  apply weightedDerivation_pow_eq_zero w _ _ hP
  intro i
  rw [scalarDirectionalDerivative_X, weightedSupportDrop_one]
  intro a ha
  have h : Finsupp.weight w a ≤ 0 := weightedSupportLE_C w 0 (x i) ha
  change Finsupp.weight w a < w i
  exact lt_of_le_of_lt h (hw i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearFactorialIntegrality
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {w : σ → ℕ}

theorem polynomialShear_scaled_pow (D : PolynomialShearLieAlgebra w ℚ)
    (c : ℚ) (k : ℕ) (P : MvPolynomial σ ℚ) :
    ((c • D).val.toLinearMap ^ k) P = c ^ k • (D.val.toLinearMap ^ k) P := by
  change ((c • D.val.toLinearMap) ^ k) P = _
  rw [smul_pow, LinearMap.smul_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearRealGroup
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S] {w : σ → ℕ}

theorem polynomialShearMap_pow_apply (f : R →+* S) (D : PolynomialShearLieAlgebra w R)
    (k : ℕ) (P : MvPolynomial σ R) :
    ((polynomialShearMap f D).val.toLinearMap ^ k) (map f P) =
      map f ((D.val.toLinearMap ^ k) P) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    exact polynomialShearMap_apply_map f D _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationShearExponential
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]

theorem shearDerivationHom_injective : Function.Injective (shearDerivationHom (σ := σ)) := by
  intro x y h
  apply PolynomialTranslationLie.ext
  · funext i
    have hh := congrArg (fun D : Derivation ℚ (MvPolynomial (σ ⊕ Unit) ℚ)
      (MvPolynomial (σ ⊕ Unit) ℚ) => D (X (Sum.inl i))) h
    simpa [shearDerivationHom] using hh
  · apply MvPolynomial.rename_injective Sum.inl Sum.inl_injective
    have hh := congrArg (fun D : Derivation ℚ (MvPolynomial (σ ⊕ Unit) ℚ)
      (MvPolynomial (σ ⊕ Unit) ℚ) => D (X (Sum.inr ()))) h
    simpa [shearDerivationHom] using hh

theorem weightedShearEmbedding_injective (w : σ → ℕ) (d : ℕ) :
    Function.Injective (weightedShearEmbedding w d) := by
  intro x y h
  apply Subtype.ext
  exact shearDerivationHom_injective (congrArg Subtype.val h)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedLinearPolynomialRestriction
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem scalarDirectionalDerivative_linearRestriction
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative z (polynomialLinearRestriction A P) =
      polynomialLinearRestriction A (scalarDirectionalDerivative (A z) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

def intModuleBCHSubgroup (M : Submodule ℤ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hstable : ∀ a ∈ M, ∀ b ∈ M, lieBCH s a b ∈ M) :
    Subgroup (NilpotentLieBCHGroup L s hnil) where
  carrier := {g | g.coord ∈ M}
  one_mem' := M.zero_mem
  mul_mem' := by intro a b ha hb; exact hstable a.coord ha b.coord hb
  inv_mem' := by intro a ha; exact M.neg_mem ha

end Erdos3

end

section

namespace Erdos3

open Module

theorem denominator_grid_subset_mul {ι : Type*} (l m : ℕ) :
    (denominatorGrid l : Set (ι → ℚ)) ⊆ denominatorGrid (m * l) := by
  intro x hx
  have h := hx.nat_smul m
  simpa only [denominatorGrid, Set.mem_ofPred_eq, smul_smul, Nat.cast_mul] using h

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

def coordinateGridBCHSubgroup (e : Basis ι ℚ L) (B : ℕ) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hstable : ∀ a ∈ coordinateGridModule e B, ∀ b ∈ coordinateGridModule e B,
      lieBCH s a b ∈ coordinateGridModule e B) :
    Subgroup (NilpotentLieBCHGroup L s hnil) :=
  intModuleBCHSubgroup (coordinateGridModule e B) hnil hstable

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {K V W ι κ δ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem basisBlockMap_commutes (e : Basis ι K V) (f : Basis κ K W)
    (c : ι → δ) (d : κ → δ) (T : V →ₗ[K] W)
    (hT : ∀ i j, d j ≠ c i → f.repr (T (e i)) j = 0) (a : δ) (x : V) :
    T (basisCoordinateProjection e {i | c i = a} x) =
      basisCoordinateProjection f {j | d j = a} (T x) := by
  classical
  have he : T.comp (basisCoordinateProjection e {i | c i = a}) =
      (basisCoordinateProjection f {j | d j = a}).comp T := by
    apply e.ext
    intro i
    apply f.repr.injective
    ext j
    by_cases hi : c i = a <;> by_cases hj : d j = a
    · simp [LinearMap.comp_apply, basisCoordinateProjection_basis, basisCoordinateProjection_repr, hi, hj]
    · have hij : d j ≠ c i := fun h => hj (h.trans hi)
      simp [LinearMap.comp_apply, basisCoordinateProjection_basis, basisCoordinateProjection_repr, hi, hj, hT i j hij]
    · have hij : d j ≠ c i := fun h => hi (h.symm.trans hj)
      simp [LinearMap.comp_apply, basisCoordinateProjection_basis, basisCoordinateProjection_repr, hi, hj, hT i j hij]
    · simp [LinearMap.comp_apply, basisCoordinateProjection_basis, basisCoordinateProjection_repr, hi, hj]
  exact DFunLike.congr_fun he x

theorem BasisBlockInvariant.map (e : Basis ι K V) (f : Basis κ K W)
    (c : ι → δ) (d : κ → δ) (T : V →ₗ[K] W)
    (hT : ∀ i j, d j ≠ c i → f.repr (T (e i)) j = 0)
    (U : Submodule K V) (hU : BasisBlockInvariant e c U) :
    BasisBlockInvariant f d (U.map T) := by
  rintro a y ⟨x, hx, rfl⟩
  exact ⟨basisCoordinateProjection e {i | c i = a} x, hU a x hx,
    basisBlockMap_commutes e f c d T hT a x⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LinearBCHAbelian
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem linearMap_lieBCH_eq_add {L V : Type*} [LieRing L] [LieAlgebra ℚ L]
    [AddCommGroup V] [Module ℚ V] (f : L →ₗ[ℚ] V)
    (hf : ∀ x y : L, f ⁅x, y⁆ = 0) {s : ℕ} (hs : 1 ≤ s) (a b : L) :
    f (lieBCH s a b) = f a + f b := by
  let : LieRing V := {
    toAddCommGroup := inferInstance
    bracket := fun _ _ => 0
    add_lie := fun _ _ _ => (add_zero 0).symm
    lie_add := fun _ _ _ => (add_zero 0).symm
    lie_self := fun _ => rfl
    leibniz_lie := fun _ _ _ => (add_zero 0).symm }
  let : LieAlgebra ℚ V := {
    toModule := inferInstance
    lie_smul := fun t _ _ => (smul_zero t).symm }
  let : IsLieAbelian V := ⟨fun _ _ => rfl⟩
  let φ : L →ₗ⁅ℚ⁆ V := { f with map_lie' := fun {x y} => hf x y }
  exact (map_lieBCH φ s a b).trans (lieBCH_eq_add_of_isLieAbelian hs (f a) (f b))

theorem linearMap_baseChange_lieBCH_eq_add {L V : Type*} [LieRing L] [LieAlgebra ℚ L]
    [AddCommGroup V] [Module ℚ V] (f : L →ₗ[ℚ] V)
    (hf : ∀ x y : L, f ⁅x, y⁆ = 0) {s : ℕ} (hs : 1 ≤ s) (a b : ℝ ⊗[ℚ] L) :
    f.baseChange ℝ (lieBCH s a b) = f.baseChange ℝ a + f.baseChange ℝ b :=
  linearMap_lieBCH_eq_add ((f.baseChange ℝ).restrictScalars ℚ)
    (linearMap_baseChange_lie_eq_zero f hf) hs a b

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def prod (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) :
    FiniteProbabilityWeights (X × Y) where
  weight z := p.weight z.1 * q.weight z.2
  nonneg z := mul_nonneg (p.nonneg z.1) (q.nonneg z.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, q.total, mul_one, p.total]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

noncomputable def toPMF (p : FiniteProbabilityWeights X) : PMF X :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p.weight x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => p.nonneg x), p.total, ENNReal.ofReal_one])

@[simp] theorem toPMF_apply (p : FiniteProbabilityWeights X) (x : X) :
    p.toPMF x = ENNReal.ofReal (p.weight x) := rfl

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

noncomputable def ofPMF {X : Type*} [Fintype X] (p : PMF X) :
    FiniteProbabilityWeights X where
  weight x := (p x).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    have ht : ∑ x, p x = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    rw [← ENNReal.toReal_sum (fun x _ => p.apply_ne_top x), ht, ENNReal.toReal_one]

@[simp] theorem ofPMF_weight {X : Type*} [Fintype X] (p : PMF X) (x : X) :
    (ofPMF p).weight x = (p x).toReal := rfl

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

noncomputable def ofSupportedPMF {X : Type*} (p : PMF X) (T : Finset X)
    (hT : ∀ x ∉ T, (p x).toReal = 0) : FiniteProbabilityWeights T where
  weight x := (p x.val).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    calc
      _ = ∑ x ∈ T, (p x).toReal := Finset.sum_coe_sort T _
      _ = ∑' x, (p x).toReal := (hasSum_sum_of_ne_finset_zero hT).tsum_eq.symm
      _ = (∑' x, p x).toReal := (ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x)).symm
      _ = 1 := by rw [p.tsum_coe, ENNReal.toReal_one]

@[simp] theorem ofSupportedPMF_weight {X : Type*} (p : PMF X) (T : Finset X)
    (hT : ∀ x ∉ T, (p x).toReal = 0) (x : T) :
    (ofSupportedPMF p T hT).weight x = (p x.val).toReal := rfl

end FiniteProbabilityWeights

noncomputable def shiftedSmoothProductFiniteWeights {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) :
    FiniteProbabilityWeights (rectangularWeightIndices a S 1) :=
  FiniteProbabilityWeights.ofSupportedPMF (shiftedSmoothProductPMF a S hS hZ)
    (rectangularWeightIndices a S 1) (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)

@[simp] theorem shiftedSmoothProductFiniteWeights_weight {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (x : rectangularWeightIndices a S 1) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).weight x =
      (shiftedSmoothProductPMF a S hS hZ x.val).toReal := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace RepresentativeWindow

noncomputable def kernel (w : RepresentativeWindow) : PatchKernel 1 where
  value r := w.value (w.center - r 0)
  nonneg r := w.nonneg _
  le_one r := w.le_one _
  support r hr i := by
    have h := w.small _ hr
    have he : w.center - r 0 - w.center = -r 0 := by ring
    rw [he, abs_neg] at h
    fin_cases i
    exact h.le
  lip := w.lip
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro r t
    apply (w.lipschitz.dist_le_mul _ _).trans
    rw [dist_sub_left]
    exact mul_le_mul_of_nonneg_left (dist_le_pi_dist r t 0) w.lip.coe_nonneg

end RepresentativeWindow
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorTranslationPolynomialSymbolDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem polynomialSlotCoefficient_coeff (β : τ →₀ ℕ) (α : σ →₀ ℕ)
    (P : MvPolynomial (σ ⊕ τ) R) :
    (polynomialSlotCoefficient β P).coeff α = P.coeff (α.sumElim β) := by
  change ((MvPolynomial.basisMonomials σ R).repr
    ((MvPolynomial.basisMonomials σ R).repr.symm _)) α = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastCoefficientBlocks
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι δ ε : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem BasisBlockInvariant.graded [Fintype ι]
    (b : Basis ι K V) (c : ι → δ) (U : Submodule K V)
    (hU : BasisBlockInvariant b c U) (f : δ → ℕ) :
    BasisGradedSubmodule b (fun i => f (c i)) U :=
  hU.coarser b c U f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.GradeProjectionRemainder
namespace OAI

section

namespace Erdos3

open Module

section Coordinates

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem sub_basisGradeProjection_mem_higher (b : Basis ι K V)
    (w : ι → ℕ) (k : ℕ) (x : V)
    (hx : x ∈ Submodule.span K (b '' {i | k ≤ w i})) :
    x - basisGradeProjection b w k x ∈ Submodule.span K (b '' {i | k + 1 ≤ w i}) := by
  apply (basis_mem_span_image_iff b _ _).mpr
  intro i hi
  change ¬ k + 1 ≤ w i at hi
  rw [map_sub, Finsupp.sub_apply, basisGradeProjection_repr]
  by_cases hki : w i = k
  · simp only [hki, ↓reduceIte, sub_self]
  · rw [if_neg hki, sub_zero]
    exact (basis_mem_span_image_iff b _ x).mp hx i (by
      change ¬ k ≤ w i
      omega)

theorem BasisGradedSubmodule.mem_sup_higher_of_grade (b : Basis ι K V)
    (w : ι → ℕ) (U : Submodule K V) (hU : BasisGradedSubmodule b w U)
    (k : ℕ) (x : V) (hx : x ∈ U ⊔ Submodule.span K (b '' {i | k ≤ w i}))
    (hgrade : basisGradeProjection b w k x ∈ U) :
    x ∈ U ⊔ Submodule.span K (b '' {i | k + 1 ≤ w i}) := by
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  have hgz : basisGradeProjection b w k z ∈ U := by
    have h := U.sub_mem hgrade (hU k u hu)
    simpa only [map_add, add_sub_cancel_left] using h
  refine Submodule.mem_sup.mpr ⟨u + basisGradeProjection b w k z, U.add_mem hu hgz,
    z - basisGradeProjection b w k z, sub_basisGradeProjection_mem_higher b w k z hz, ?_⟩
  abel

end Coordinates

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisProjectionRealification
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]

theorem BasisGradedSubmodule.baseChange (b : Basis ι ℚ V) (w : ι → ℕ) (U : Submodule ℚ V)
    (hU : BasisGradedSubmodule b w U) : BasisGradedSubmodule (b.baseChange ℝ) w (U.baseChange ℝ) := by
  intro j x hx
  have hstable : U.baseChange ℝ ≤ (U.baseChange ℝ).comap (basisGradeProjection (b.baseChange ℝ) w j) := by
    conv_lhs => rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    change basisCoordinateProjection (b.baseChange ℝ) {i | w i = j} ((1 : ℝ) ⊗ₜ[ℚ] u) ∈ U.baseChange ℝ
    rw [← basisCoordinateProjection_baseChange, LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem 1 (hU j u hu)
  exact hstable hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedLieUpperSpan
namespace OAI

section

namespace Erdos3

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem weightedLieUpperSpan_antitone (v : I → L) (w : I → ℕ) :
    Antitone (weightedLieUpperSpan v w) := by
  intro d e hde
  apply Submodule.span_mono
  rintro x ⟨a, ha, rfl⟩
  exact ⟨a, hde.trans ha, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationShearExponentialOver
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {R σ : Type*} [CommRing R] [Algebra ℚ R]
  {w : σ ⊕ Unit → ℕ}

omit [Algebra ℚ R] in
theorem translationShear_derivation_rename
    (D : PolynomialShearLieAlgebra w R) (b : σ → R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i)) (P : MvPolynomial σ R) :
    ∃ Q : MvPolynomial σ R, D.val (rename Sum.inl P) = rename Sum.inl Q := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨0, by simp⟩
  | add P Q hP hQ =>
      obtain ⟨P', hP'⟩ := hP
      obtain ⟨Q', hQ'⟩ := hQ
      exact ⟨P' + Q', by simp only [map_add, hP', hQ']⟩
  | mul_X P i hP =>
      obtain ⟨P', hP'⟩ := hP
      refine ⟨P * C (b i) + X i * P', ?_⟩
      simp only [map_mul, rename_X, D.val.leibniz, hb, hP', smul_eq_mul,
        map_add, rename_C]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationExponentialSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem polynomialTranslate_exponentialCoordinate_series_of_nilpotent (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ}
    (hP : ((scalarDirectionalDerivative x).toLinearMap ^ (n + 1)) P = 0) :
    polynomialTranslate x (polynomialExponentialCoordinate x P) =
      ∑ i ∈ Finset.range (n + 1),
        (((i + 1).factorial : ℚ)⁻¹) • ((scalarDirectionalDerivative x).toLinearMap ^ i) P := by
  rw [polynomialTranslate_exponentialCoordinate]
  exact polynomialExponentialCoordinate_neg_series_of_nilpotent x hP

theorem polynomialTranslate_exponentialCoordinate_series
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialTranslate x (polynomialExponentialCoordinate x P) =
      ∑ i ∈ Finset.range (n + 1),
        (((i + 1).factorial : ℚ)⁻¹) • ((scalarDirectionalDerivative x).toLinearMap ^ i) P :=
  polynomialTranslate_exponentialCoordinate_series_of_nilpotent x
    (scalarDirectionalDerivative_pow_eq_zero_of_weightedSupport w hw x hP)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def affineParameterSubstitution {I K : Type*} [Fintype K]
    (b : Option K → I → ℝ) (j : I) : MvPolynomial K ℝ :=
  MvPolynomial.C (b none j) + rowPolynomial (fun k => b (some k) j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativeFiberSlicePatch
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open _root_.MvPolynomial

variable {X : Type*} {keep : X → Prop} {N : {x // keep x} → ℕ} {q s d : ℕ}

noncomputable def fiberInverseParameters (S : ResidueBoxSlice N q) (k : {x // keep x}) :
    MvPolynomial X ℝ :=
  (q : ℝ)⁻¹ • (MvPolynomial.X k.val - C (S.start k : ℝ))

theorem fiberInverseParameters_degree (S : ResidueBoxSlice N q) (k : {x // keep x}) :
    S.fiberInverseParameters k ∈ weightedSupportLE (fun _ : X => 1) 1 :=
  (weightedSupportLE _ _).smul_mem _
    ((weightedSupportLE _ _).sub_mem (weightedSupportLE_X _ _) (weightedSupportLE_C _ _ _))

noncomputable def fiberReinsertPatch (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) : PolynomialPatch X s d :=
  Q.reparam S.fiberInverseParameters S.fiberInverseParameters_degree

@[simp] theorem fiberReinsertPatch_kernel (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) : (S.fiberReinsertPatch Q).kernel = Q.kernel := rfl

@[simp] theorem fiberReinsertPatch_weight (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) : (S.fiberReinsertPatch Q).weight = Q.weight := rfl

@[simp] theorem fiberReinsertPatch_lip (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) : (S.fiberReinsertPatch Q).kernel.lip = Q.kernel.lip := rfl

theorem fiberReinsertPatch_value (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) (x : X → ℝ) :
    (S.fiberReinsertPatch Q).value x =
      Q.value (fun k => (x k.val - (S.start k : ℝ)) / (q : ℝ)) := by
  rw [fiberReinsertPatch, PolynomialPatch.reparam_value]
  congr 1
  funext k
  simp only [fiberInverseParameters, map_smul, map_sub, aeval_X, aeval_C,
    smul_eq_mul, div_eq_mul_inv, mul_comm, Algebra.algebraMap_self, RingHom.id_apply]

def fiberIntegerPoint [DecidablePred keep] (S : ResidueBoxSlice N q)
    (fixed : {x // ¬keep x} → ℤ) (u : ∀ k, Fin (S.length k)) : X → ℤ :=
  finiteSplitPoint keep (fun k => ((S.point u k).val : ℤ)) fixed

theorem fiberReinsertPatch_point_value [DecidablePred keep] (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) (hq : 0 < q)
    (fixed : {x // ¬keep x} → ℤ) (u : ∀ k, Fin (S.length k)) :
    (S.fiberReinsertPatch Q).value
      (fun k => ((finiteSplitPoint keep (fun i => ((S.point u i).val : ℤ)) fixed k : ℤ) : ℝ)) =
        Q.value (fun k => ((u k).val : ℝ)) := by
  rw [fiberReinsertPatch_value]
  congr 1
  funext k
  rw [finiteSplitPoint_fixed]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [point, Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  field_simp
  ring

@[simp] theorem fiberReinsertPatch_integerPoint_value [DecidablePred keep]
    (S : ResidueBoxSlice N q) (Q : PolynomialPatch {x // keep x} s d) (hq : 0 < q)
    (fixed : {x // ¬keep x} → ℤ) (u : ∀ k, Fin (S.length k)) :
    (S.fiberReinsertPatch Q).value (fun k => (S.fiberIntegerPoint fixed u k : ℝ)) =
      Q.value (fun k => ((u k).val : ℝ)) :=
  S.fiberReinsertPatch_point_value Q hq fixed u

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q : ℕ}

def comp (S : ResidueBoxSlice N q) {r : ℕ} (T : ResidueBoxSlice S.length r) :
    ResidueBoxSlice N (q * r) where
  start i := S.start i + q * T.start i
  length := T.length
  inside i j hj := by
    have h := S.inside i (T.start i + r * j) (T.inside i j hj)
    simpa only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] using h

@[simp] theorem comp_point (S : ResidueBoxSlice N q) {r : ℕ}
    (T : ResidueBoxSlice S.length r) (x : ∀ i, Fin (T.length i)) :
    (S.comp T).point x = S.point (T.point x) := by
  ext i
  simp [comp, point, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

noncomputable def polynomial (S : ResidueBoxSlice N q) (i : I) : MvPolynomial I ℝ :=
  MvPolynomial.C (S.start i : ℝ) + MvPolynomial.C (q : ℝ) * MvPolynomial.X i

@[simp] theorem polynomial_eval (S : ResidueBoxSlice N q)
    (x : ∀ i, Fin (S.length i)) (i : I) :
    MvPolynomial.aeval (R := ℝ) (fun i => ((x i).val : ℝ)) (S.polynomial i) =
      ((S.point x i).val : ℝ) := by
  simp [polynomial, point, Nat.cast_add, Nat.cast_mul]

end ResidueBoxSlice

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q r : ℕ}

theorem comp_length_exp_lower
    (A : ResidueBoxSlice N q) (B : ResidueBoxSlice A.length r) {u v : ℝ}
    (hA : ∀ i, Real.exp (-u) * (N i : ℝ) ≤ A.length i)
    (hB : ∀ i, Real.exp (-v) * (A.length i : ℝ) ≤ B.length i) :
    ∀ i, Real.exp (-(u + v)) * (N i : ℝ) ≤ (A.comp B).length i := by
  intro i
  change Real.exp (-(u + v)) * (N i : ℝ) ≤ (B.length i : ℝ)
  calc
    Real.exp (-(u + v)) * (N i : ℝ) =
        Real.exp (-v) * (Real.exp (-u) * (N i : ℝ)) := by
      rw [neg_add, Real.exp_add]
      ring
    _ ≤ Real.exp (-v) * (A.length i : ℝ) :=
      mul_le_mul_of_nonneg_left (hA i) (Real.exp_pos _).le
    _ ≤ (B.length i : ℝ) := hB i

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} {N : X → ℕ} {q : ℕ}

def integerAffine (S : ResidueBoxSlice N q) (x : X → ℤ) : X → ℤ :=
  fun i => (S.start i : ℤ) + (q : ℤ) * x i

def integerPullback (S : ResidueBoxSlice N q) (f : (X → ℤ) → ℝ) :
    (X → ℤ) → ℝ := fun x => f (S.integerAffine x)

@[simp] theorem integerAffine_finPoint (S : ResidueBoxSlice N q)
    (x : ∀ i, Fin (S.length i)) :
    S.integerAffine (fun i => ((x i).val : ℤ)) =
      fun i => ((S.point x i).val : ℤ) := by
  funext i
  simp [integerAffine, point, Nat.cast_add, Nat.cast_mul]

@[simp] theorem integerAffine_comp (S : ResidueBoxSlice N q) {r : ℕ}
    (T : ResidueBoxSlice S.length r) (x : X → ℤ) :
    (S.comp T).integerAffine x = S.integerAffine (T.integerAffine x) := by
  funext i
  simp only [integerAffine, comp, Nat.cast_add, Nat.cast_mul]
  ring

@[simp] theorem integerPullback_comp (S : ResidueBoxSlice N q) {r : ℕ}
    (T : ResidueBoxSlice S.length r) (f : (X → ℤ) → ℝ) :
    (S.comp T).integerPullback f = T.integerPullback (S.integerPullback f) := by
  funext x
  simp only [integerPullback, integerAffine_comp]

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {U : Type*} {N : U → ℕ} {q : ℕ}

def integerPoint (A : ResidueBoxSlice N q) (j : ∀ i, Fin (A.length i)) : U → ℤ :=
  fun i => ((A.point j i).val : ℤ)

theorem integerPoint_eq (A : ResidueBoxSlice N q) (j : ∀ i, Fin (A.length i)) :
    A.integerPoint j = commonStridePoint (fun i => (A.start i : ℤ)) q
      (fun i => ((j i).val : ℤ)) := by
  funext i
  simp only [integerPoint, point, commonStridePoint, Nat.cast_add, Nat.cast_mul]

@[simp] theorem commonStrideIndex_integerPoint (A : ResidueBoxSlice N q) (hq : 0 < q)
    (j : ∀ i, Fin (A.length i)) :
    commonStrideIndex (fun i => (A.start i : ℤ)) q (A.integerPoint j) =
      (fun i => ((j i).val : ℤ)) := by
  rw [integerPoint_eq, commonStrideIndex_point _ hq]

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeGraphSmallDifference
namespace OAI

section

namespace Erdos3.BSG

open _root_.Finset hiding card
open _root_.OAI.Finset
open Fintype
open scoped BigOperators Pointwise Combinatorics.Additive' Indicator BSGConvolution

section
variable {α : Type*} [Fintype α] [DecidableEq α] {H : Finset (α × α)} {A B X : Finset α} {a b x : α}
  {K : ℝ}

omit [Fintype α] in
lemma oneOfPair_aux (hH : H ⊆ X ×ˢ X) : #{yz ∈ H | yz.1 = x} = #{c ∈ X | (x, c) ∈ H} := by
  refine card_nbij' Prod.snd (fun c ↦ (x, c)) ?_ (by simp [Set.MapsTo])
    (by grind [Set.LeftInvOn]) (by simp [Set.LeftInvOn])
  simpa +contextual [Set.MapsTo, eq_comm] using fun a b hab _ ↦ (mem_product.1 (hH hab)).2

lemma oneOfPair_subset : oneOfPair H X ⊆ X := filter_subset ..

lemma oneOfPair_bound_one :
    (∑ x ∈ X \ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α ≤ (3 / 4) * X.dens ^ 2 := calc
  _ ≤ (∑ _x ∈ X \ oneOfPair H X, 3 / 4 * X.dens : ℝ) / card α := by
    gcongr
    grind [oneOfPair]
  _ = (X \ oneOfPair H X).dens * (3 / 4 * X.dens) := by simp [dens]; ring
  _ ≤ X.dens * (3 / 4 * X.dens) := by grw [sdiff_subset]
  _ = _ := by ring

lemma oneOfPair_bound_two (hH : H ⊆ X ×ˢ X) (Hcard : (7 / 8 : ℝ) * X.dens ^ 2 ≤ H.dens) :
    (1 / 8 : ℝ) * X.dens ^ 2 ≤ X.dens * (oneOfPair H X).dens := calc
  _ ≤ H.dens - (3 / 4 : ℝ) * X.dens ^ 2 := by linarith
  _ ≤ H.dens - (∑ x ∈ X \ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α := by
    gcongr; exact oneOfPair_bound_one
  _ = H.dens - (∑ x ∈ X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α
    + (∑ x ∈ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α := by
    rw [sum_sdiff_eq_sub oneOfPair_subset, sub_add, sub_div]
  _ = (∑ x ∈ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α := by
    simp only [dens, Fintype.card_prod, Nat.cast_mul, NNRat.cast_div, NNRat.cast_natCast,
      NNRat.cast_mul, ← sum_div, div_div, add_eq_right, sub_eq_zero, ← oneOfPair_aux hH]
    norm_cast
    rw [← card_eq_sum_card_fiberwise fun x hx ↦ (mem_product.1 (hH hx)).1]
  _ ≤ (∑ _x ∈ oneOfPair H X, (X.dens : ℝ)) / card α := by gcongr with i; exact filter_subset ..
  _ = X.dens * (oneOfPair H X).dens := by simp [dens]; ring

lemma oneOfPair_bound (hH : H ⊆ X ×ˢ X) (hX : X.Nonempty)
    (Hcard : (7 / 8 : ℝ) * X.dens ^ 2 ≤ H.dens) (h : A.dens / (2 * K) ≤ X.dens) :
    A.dens / (2 ^ 4 * K : ℝ) ≤ (oneOfPair H X).dens := calc
    _ = (A.dens / (2 * K) : ℝ) / 8 := by ring
    _ ≤ (X.dens / 8 : ℝ) := by gcongr
    _ ≤ (oneOfPair H X).dens :=
      le_of_mul_le_mul_left ((oneOfPair_bound_two hH Hcard).trans_eq' (by ring)) <| by positivity

end

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {A B : Finset G} {x : G}

variable {K : Type*} [Semifield K] [CharZero K] [StarRing K]

section lemma2
variable {H : Finset (G × G)} {X : Finset G}

lemma BSG_aux {K : ℝ} (hK : 0 < K) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B]) :
    ∃ x : G, ∃ A' ⊆ A ∩ (x +ᵥ B), (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧
      (A' - A').dens ≤ 2 ^ 10 * K ^ 5 * B.dens ^ 4 / A.dens ^ 3 := by
  obtain ⟨x, X, hX₁, hX₂, hX₃⟩ := lemma_one' (c := 1 / 8) (by norm_num) hK hAB hA hB
  set H : Finset (G × G) := (X ×ˢ X).filter
    fun ⟨a, b⟩ ↦ A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)
  have : (0 : ℝ) < X.dens := hX₂.trans_lt' (by positivity)
  refine ⟨x, oneOfPair H X, (filter_subset _ _).trans hX₁, ?_, ?_⟩
  · rw [← mul_inv, inv_mul_eq_div]
    refine oneOfPair_bound (filter_subset _ _) (by simpa using this) ?_ hX₂
    convert hX₃ using 2
    · norm_num
    · unfold H
      ring_nf
  have := big_quadruple_bound (H := H) (fun x hx ↦ (mem_filter.1 hx).2) hX₂
  rw [le_div_iff₀ (by positivity)]
  rw [mul_div_assoc', div_le_iff₀ (by positivity)] at this
  grind

end lemma2

theorem balogSzemerediGowers {K : ℝ} (hK : 0 ≤ K) (hB : B.Nonempty)
    (hAB : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧
      (A' - A').dens ≤ 2 ^ 10 * K ^ 5 * B.dens ^ 4 / A.dens ^ 3 := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  obtain rfl | hK := eq_or_lt_of_le hK
  · simp
  · grind [BSG_aux]

theorem BSG_self {K : ℝ} (hK : 0 ≤ K) (hA : A.Nonempty) (hAK : K⁻¹ * A.dens ^ 3 ≤ E[A]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧ (A' - A').dens ≤ 2 ^ 10 * K ^ 5 * A.dens := by
  convert balogSzemerediGowers hK hA ?_ using 5 <;> grind

theorem BSG_self' {K : ℝ} (hK : 0 ≤ K) (hA : A.Nonempty) (hAK : K⁻¹ * A.dens ^ 3 ≤ E[A]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧ (A' - A').dens ≤ 2 ^ 14 * K ^ 6 * A'.dens := by
  obtain ⟨A', hA', hAA', hAK'⟩ := BSG_self hK hA hAK
  refine ⟨A', hA', hAA', hAK'.trans ?_⟩
  calc
    _ = 2 ^ 14 * K ^ 6 * ((2 ^ 4)⁻¹ * K⁻¹ * A.dens) := ?_
    _ ≤ _ := by gcongr
  grind

end Erdos3.BSG

end

section

namespace Erdos3.BSG

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem exists_large_subset_small_difference (A : Finset G) (hA : A.Nonempty)
    {K : ℝ} (hK : 0 < K) (henergy : K⁻¹ * (A.card : ℝ) ^ 3 ≤ (Finset.addEnergy A A : ℝ)) :
    ∃ S ⊆ A, S.Nonempty ∧ (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * A.card ≤ (S.card : ℝ) ∧
      ((S - S).card : ℝ) ≤ (2 ^ 14 : ℝ) * K ^ 6 * S.card := by
  have he : K⁻¹ * (A.dens : ℝ) ^ 3 ≤ (Finset.addEnergy' A A : ℝ) := by
    rw [Finset.cast_addEnergy']
    simp only [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, div_pow]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right henergy (by positivity)
  obtain ⟨S, hSA, hsize, hsmall⟩ := BSG_self' hK.le hA he
  have hsize' := (density_mul_le_iff_card_mul_le A S ((2 ^ 4 : ℝ)⁻¹ * K⁻¹)).mp
    (by simpa only [mul_assoc] using hsize)
  have hsmall' := (density_le_mul_iff_card_le_mul (S - S) S ((2 ^ 14 : ℝ) * K ^ 6)).mp
    (by simpa only [mul_assoc] using hsmall)
  have hpos : (0 : ℝ) < S.card :=
    (mul_pos (mul_pos (by positivity) (inv_pos.mpr hK))
      (by exact_mod_cast hA.card_pos)).trans_le hsize'
  exact ⟨S, hSA, Finset.card_pos.mp (by exact_mod_cast hpos), hsize', hsmall'⟩

end Erdos3.BSG

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace SimplexHypergraph

@[simp]
theorem deletionCapacity_fin (k n : ℕ) :
    deletionCapacity (fun _ : Fin k => Fin n) =
      k * n ^ (k - 1) := by
  simp [deletionCapacity]

end SimplexHypergraph

end Erdos3.FixedDensity

end

end OAI
end


