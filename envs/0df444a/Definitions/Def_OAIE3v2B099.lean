-- Prove2me | Definitions.Def_OAIE3v2B099
-- name    : OAIE3v2B099
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:29:59.817194+00:00
-- url     : https://prove2.me/theorems/c9fd566b-713a-4ebe-96c5-fcc622619e44
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 101 of 311
-- statement:
--   Definitions bundle 101 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B069`, `OAIE3v2B070`, `OAIE3v2B071`, `OAIE3v2B072`, `OAIE3v2B073`, `OAIE3v2B074`, `OAIE3v2B075`, `OAIE3v2B081`, `OAIE3v2B082`, `OAIE3v2B083`, `OAIE3v2B084`, `OAIE3v2B085` of this split.
--
--   Modules: `Dynamics/AllocatedFixedScaleCollisionBudget.lean`, `Dynamics/EarlyFiberCapBudget.lean`, `Dynamics/PreparedModularCanonicalDetectorPeriodBudget.lean`, `Dynamics/PreparedModularGeneralNativeBudget.lean`, `Dynamics/PreparedSameScaleBadProductBudget.lean`, `Estimates/AllocatedFiberCap.lean`, `Estimates/AnchoredReferenceDomination.lean`, `Estimates/BooleanCubeProduct.lean`, `Estimates/CanonicalScalarSourceEnvelope.lean`, `Estimates/CoefficientProductHaar.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/CubeSignalAlgebra.lean`, `Estimates/DenseProgressionInnerFamily.lean`, `Estimates/NormalizedTwistParameterPartition.lean`, `Estimates/OverlapCubeWeights.lean`, `Estimates/QuadraticCyclicAntisymmetric.lean`, `Estimates/SampledCommonSlice.lean`, `Fourier/AllocatedMaskedCoefficientFourier.lean`, `Fourier/AnchoredCoefficientFourierNormalization.lean`, `Fourier/CommonCoveredSiteCharacter.lean`, `Fourier/CyclicAffineCharacterPhase.lean`, `Fourier/EuclideanJetTorus.lean`, `Fourier/FixedPrincipalCoefficientSpectrum.lean`, `Geometry/BoxDifferenceHom.lean`, `Geometry/BoxOverlapSize.lean`, `Geometry/MixedRealCoordinates.lean`, `Geometry/SampledCommonBox.lean`, `Geometry/SupportedCubeEquivTransport.lean`, `Geometry/SupportedCubeUnitBounds.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/SelectedResidueApproximation.lean`, `Lattices/StandardLatticeCoordinates.lean`, `Linear/KernelCoefficientLogBudget.lean`, `Probability/CanonicalCoverLaw.lean`, `Probability/CoefficientProductLaw.lean`, `Probability/CubeMixtureVertex.lean`, `Sampling/ForecastPreparedScaleBudget.lean`, `Sampling/ShiftedSmoothFiniteGridLaw.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B069
import Definitions.Def_OAIE3v2B070
import Definitions.Def_OAIE3v2B071
import Definitions.Def_OAIE3v2B072
import Definitions.Def_OAIE3v2B073
import Definitions.Def_OAIE3v2B074
import Definitions.Def_OAIE3v2B075
import Definitions.Def_OAIE3v2B081
import Definitions.Def_OAIE3v2B082
import Definitions.Def_OAIE3v2B083
import Definitions.Def_OAIE3v2B084
import Definitions.Def_OAIE3v2B085

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem expect_cross_gowersNorm_pow_le (j : ℕ) (f g : H → ℂ) :
    (𝔼 h, gowersNorm (j + 1) (crossDerivative f g h) ^ (2 ^ (j + 1))) ≤
      (gowersNorm (j + 2) f * gowersNorm (j + 2) g) ^ (2 ^ (j + 1)) := by
  let A := 𝔼 h, gowersNorm (j + 1) (crossDerivative f g h) ^ (2 ^ (j + 1))
  let B := (gowersNorm (j + 2) f * gowersNorm (j + 2) g) ^ (2 ^ (j + 1))
  have hA : 0 ≤ A := Finset.expect_nonneg (fun h _ ↦
    pow_nonneg (gowersNorm_nonneg j _) _)
  have hB : 0 ≤ B := pow_nonneg
    (mul_nonneg (gowersNorm_nonneg (j + 1) f) (gowersNorm_nonneg (j + 1) g)) _
  have hnorm : A ≤ ‖𝔼 h, gowersMoment (j + 1) (crossDerivative f g h)‖ := by
    dsimp [A]
    simp only [gowersNorm_pow, ← expect_re]
    exact Complex.re_le_norm _
  have hpower : (gowersMoment (j + 2) f).re * (gowersMoment (j + 2) g).re = B ^ 2 := by
    dsimp [B]
    rw [← gowersNorm_pow, ← gowersNorm_pow, ← mul_pow, ← pow_mul]
    congr 1
  have hsq : A ^ 2 ≤ B ^ 2 := (pow_le_pow_left₀ hA hnorm 2).trans
    ((norm_expect_gowersMoment_crossDerivative_sq_le (j + 1) f g).trans_eq hpower)
  change A ≤ B
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeProduct
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem norm_mixedGowersMoment_le (j : ℕ) (F : (Fin (j + 1) → Bool) → H → ℂ) :
    ‖mixedGowersMoment (j + 1) F‖ ≤ ∏ ω, gowersNorm (j + 1) (F ω) := by
  induction j with
  | zero =>
    rw [mixedGowersMoment_one, norm_mul, norm_star, prod_bool_tuple_succ]
    rw [Fintype.prod_subsingleton _ (default : Fin 0 → Bool),
      Fintype.prod_subsingleton _ (default : Fin 0 → Bool),
      gowersNorm_one, gowersNorm_one]
  | succ j ih =>
    let D (ω : Fin (j + 1) → Bool) (h : H) :=
      crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h
    have hnorm : ‖mixedGowersMoment (j + 2) F‖ ≤
        𝔼 h, ∏ ω, gowersNorm (j + 1) (D ω h) := by
      change ‖𝔼 h, mixedGowersMoment (j + 1) (fun ω ↦ D ω h)‖ ≤ _
      exact (RCLike.norm_expect_le (K := ℂ)).trans
        (Finset.expect_le_expect (fun h _ ↦ ih (fun ω ↦ D ω h)))
    have hholder := expect_prod_boolean_pow_le (j + 1)
      (fun ω h ↦ gowersNorm (j + 1) (D ω h)) (fun ω h ↦ gowersNorm_nonneg j _)
    have hcross : (∏ ω, 𝔼 h, gowersNorm (j + 1) (D ω h) ^ (2 ^ (j + 1))) ≤
        ∏ ω : Fin (j + 1) → Bool,
          (gowersNorm (j + 2) (F (Fin.cons false ω)) *
            gowersNorm (j + 2) (F (Fin.cons true ω))) ^ (2 ^ (j + 1)) := by
      apply Finset.prod_le_prod
      · intro ω hω
        exact Finset.expect_nonneg (fun h _ ↦ pow_nonneg (gowersNorm_nonneg j _) _)
      · intro ω hω
        exact expect_cross_gowersNorm_pow_le j _ _
    have hfactor : (∏ ω : Fin (j + 1) → Bool,
          (gowersNorm (j + 2) (F (Fin.cons false ω)) *
            gowersNorm (j + 2) (F (Fin.cons true ω))) ^ (2 ^ (j + 1))) =
        (∏ ω, gowersNorm (j + 2) (F ω)) ^ (2 ^ (j + 1)) := by
      rw [Finset.prod_pow, Finset.prod_mul_distrib,
        ← prod_bool_tuple_succ (fun ω ↦ gowersNorm (j + 2) (F ω))]
    apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
      (Finset.prod_nonneg (fun ω _ ↦ gowersNorm_nonneg (j + 1) _))
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm _).trans
      (hholder.trans (hcross.trans_eq hfactor))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H]

variable [Fintype H]

theorem mixedGowersMoment_eq_expect_cube {j : ℕ} (F : (Fin j → Bool) → H → ℂ) :
    mixedGowersMoment j F = 𝔼 hs : Fin j → H, 𝔼 x, mixedCubeProduct F hs x := by
  induction j with
  | zero => simp [mixedGowersMoment]
  | succ j ih =>
    rw [mixedGowersMoment, expect_fin_cons]
    simp_rw [ih, mixedCubeProduct_crossDerivative, mixedCubeProduct_cons]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem restrictedGowersNorm_nonneg (j : ℕ) (Q : Finset H) (f : H → ℂ) :
    0 ≤ restrictedGowersNorm (j + 1) Q f :=
  div_nonneg (gowersNorm_nonneg j _) (gowersNorm_nonneg j _)

theorem restrictedGowersNorm_degree_one {Q : Finset H} (hQ : Q.Nonempty) (f : H → ℂ) :
    restrictedGowersNorm 1 Q f = ‖𝔼 x ∈ Q, f x‖ := by
  rw [restrictedGowersNorm, gowersNorm_one, gowersNorm_one,
    norm_expect_restrict_one, expect_restrictTo, Finset.expect_eq_sum_div_card]
  simp only [norm_div, Complex.norm_natCast]
  have hcard : (Q.card : ℝ) ≠ 0 := by exact_mod_cast hQ.card_pos.ne'
  have hH : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem norm_mixedGowersMoment_restrict_le (j : ℕ) (Q : Finset H)
    (F : (Fin (j + 1) → Bool) → H → ℂ) :
    ‖mixedGowersMoment (j + 1) (fun ω ↦ restrictTo Q (F ω))‖ /
        (gowersMoment (j + 1) (restrictTo Q (fun _ ↦ 1))).re ≤
      ∏ ω, restrictedGowersNorm (j + 1) Q (F ω) := by
  simp only [restrictedGowersNorm, Finset.prod_div_distrib]
  rw [Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [gowersNorm_pow]
  exact div_le_div_of_nonneg_right (norm_mixedGowersMoment_le j _)
    (gowersMoment_re_nonneg j _)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem gowersMoment_indicator_eq_cubeCount (j : ℕ) (Q : Finset H) :
    gowersMoment j (restrictTo Q (fun _ ↦ 1)) =
      (groupCubeCount j Q : ℂ) / (Fintype.card H : ℂ) ^ (j + 1) := by
  rw [← mixedGowersMoment_const, mixedGowersMoment_eq_expect_cube]
  simp_rw [mixedCubeProduct_indicator]
  rw [← Finset.expect_product', Finset.univ_product_univ]
  rw [Fintype.expect_eq_sum_div_card]
  have hsum : (∑ p : (Fin j → H) × H,
      if ∀ ω : Fin j → Bool, p.2 + cubeShift p.1 ω ∈ Q then (1 : ℂ) else 0) =
        (groupCubeCount j Q : ℂ) := by
    simp [groupCubeCount, groupCubeSet]
  rw [hsum]
  simp [Fintype.card_prod, pow_succ]

theorem gowersMoment_indicator_re (j : ℕ) (Q : Finset H) :
    (gowersMoment j (restrictTo Q (fun _ ↦ 1))).re =
      (groupCubeCount j Q : ℝ) / (Fintype.card H : ℝ) ^ (j + 1) := by
  rw [gowersMoment_indicator_eq_cubeCount]
  simpa only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast] using
    (Complex.ofReal_re ((groupCubeCount j Q : ℝ) / (Fintype.card H : ℝ) ^ (j + 1)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A]

section FiniteAmbient

variable [Fintype A] [DecidableEq A]

theorem mixedGowersMoment_restrict_eq_supportedCubeSum (j : ℕ) (Q : Finset A)
    (F : (Fin j → Bool) → A → ℂ) :
    mixedGowersMoment j (fun ω ↦ restrictTo Q (F ω)) =
      supportedCubeSum j (Q : Set A) F / (Fintype.card A : ℂ) ^ (j + 1) := by
  classical
  rw [mixedGowersMoment_eq_expect_cube]
  simp_rw [mixedCubeProduct_restrictTo]
  rw [← Finset.expect_product', Finset.univ_product_univ,
    Fintype.expect_eq_sum_div_card, supportedCubeSum_eq_sum]
  have hc : (Fintype.card ((Fin j → A) × A) : ℂ) = (Fintype.card A : ℂ) ^ (j + 1) := by
    simp [pow_succ]
  rw [hc]
  congr 1
  simp [groupCubeSet, Finset.sum_filter]

end FiniteAmbient

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

variable [Fintype B] [DecidableEq B]

theorem mixedGowersMoment_imageExtension {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (F : (Fin j → Bool) → A → ℂ) :
    mixedGowersMoment j (fun ω ↦ imageExtension φ Q (F ω)) =
      supportedCubeSum j (Q : Set A) F / (Fintype.card B : ℂ) ^ (j + 1) := by
  classical
  have hr : (fun ω ↦ imageExtension φ Q (F ω)) =
      (fun ω ↦ restrictTo (Q.image φ) (imageExtension φ Q (F ω))) := by
    funext ω
    exact (restrictTo_imageExtension φ Q (F ω)).symm
  rw [hr, mixedGowersMoment_restrict_eq_supportedCubeSum]
  simp only [Finset.coe_image, supportedCubeSum_imageExtension hφ]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

theorem supportedCubeSum_derivative (j : ℕ) (Q : Finset A)
    (F : (Fin (j + 1) → Bool) → A → ℂ) :
    supportedCubeSum (j + 1) (Q : Set A) F =
      ∑ h ∈ cubeDifferenceSupport Q, supportedCubeSum j (derivativeSupport Q h : Set A)
        (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h) := by
  let he := (supportedCubeDerivativeEquiv j Q).symm
  calc
    _ = ∑ p : Σ h : cubeDifferenceSupport Q,
        SupportedCube j (derivativeSupport Q h.val : Set A),
        mixedCubeProduct F (Fin.cons p.1.val p.2.val.1) p.2.val.2 := by
      symm
      apply Fintype.sum_equiv he
      intro p
      rfl
    _ = _ := by
      simp only [Fintype.sum_sigma, mixedCubeProduct_cons,
        ← mixedCubeProduct_crossDerivative, supportedCubeSum]
      exact Finset.sum_coe_sort (cubeDifferenceSupport Q)
        (fun h ↦ supportedCubeSum j (derivativeSupport Q h : Set A)
          (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

variable [Fintype B] [DecidableEq B]

theorem gowersMoment_imageExtension_re {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    (gowersMoment j (imageExtension φ Q f)).re =
      (supportedCubeSum j (Q : Set A) (fun _ ↦ f)).re /
        (Fintype.card B : ℝ) ^ (j + 1) := by
  have hm := congrArg Complex.re (mixedGowersMoment_imageExtension hφ j (fun _ ↦ f))
  simpa only [mixedGowersMoment_const, ← Nat.cast_pow, Complex.div_natCast_re] using hm

theorem restrictedGowersNorm_imageExtension_pow {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    restrictedGowersNorm (j + 1) (Q.image φ) (imageExtension φ Q f) ^ (2 ^ (j + 1)) =
      (supportedCubeSum (j + 1) (Q : Set A) (fun _ ↦ f)).re /
        Nat.card (SupportedCube (j + 1) (Q : Set A)) := by
  simp only [restrictedGowersNorm, div_pow, gowersNorm_pow,
    restrictTo_imageExtension, gowersMoment_imageExtension_re hφ, gowersMoment_indicator_re]
  rw [← card_supportedCube_image hφ]
  exact div_div_div_cancel_right₀
    (pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card B : ℝ) ≠ 0)) _ _

theorem finiteSupportGowersNorm_eq_restricted {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    finiteSupportGowersNorm (j + 1) Q f =
      restrictedGowersNorm (j + 1) (Q.image φ) (imageExtension φ Q f) := by
  unfold finiteSupportGowersNorm
  rw [← restrictedGowersNorm_imageExtension_pow hφ]
  exact Real.pow_rpow_inv_natCast (restrictedGowersNorm_nonneg j _ _)
    (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))

theorem norm_supportedCubeSum_le_of_embedding {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (F : (Fin (j + 1) → Bool) → A → ℂ) :
    ‖supportedCubeSum (j + 1) (Q : Set A) F‖ /
        Nat.card (SupportedCube (j + 1) (Q : Set A)) ≤
      ∏ ω, finiteSupportGowersNorm (j + 1) Q (F ω) := by
  have h := norm_mixedGowersMoment_restrict_le j (Q.image φ)
    (fun ω ↦ imageExtension φ Q (F ω))
  simp only [restrictTo_imageExtension, mixedGowersMoment_imageExtension hφ,
    norm_div, norm_pow, Complex.norm_natCast, gowersMoment_indicator_re,
    ← card_supportedCube_image hφ, ← finiteSupportGowersNorm_eq_restricted hφ] at h
  rwa [div_div_div_cancel_right₀
    (pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card B : ℝ) ≠ 0))] at h

theorem finiteSupportGowersNorm_degree_one_of_embedding {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (hQ : Q.Nonempty) (f : A → ℂ) :
    finiteSupportGowersNorm 1 Q f = ‖𝔼 x ∈ Q, f x‖ := by
  classical
  rw [finiteSupportGowersNorm_eq_restricted hφ 0,
    restrictedGowersNorm_degree_one (hQ.image φ)]
  simp only [Finset.expect_eq_sum_div_card]
  rw [Finset.card_image_of_injOn hφ.injOn, Finset.sum_image]
  · congr 2
    apply Finset.sum_congr rfl
    intro x hx
    exact imageExtension_apply hφ.injOn f hx
  · exact hφ.injOn

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

variable [DecidableEq A]

variable [Fintype B] [DecidableEq B]

omit [DecidableEq A] in
theorem finiteSupportGowersNorm_pow_mul_count {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (hQ : Q.Nonempty) (j : ℕ) (f : A → ℂ) :
    (Nat.card (SupportedCube (j + 1) (Q : Set A)) : ℝ) *
        finiteSupportGowersNorm (j + 1) Q f ^ (2 ^ (j + 1)) =
      (supportedCubeSum (j + 1) (Q : Set A) (fun _ ↦ f)).re := by
  rw [finiteSupportGowersNorm_eq_restricted hφ, restrictedGowersNorm_imageExtension_pow hφ]
  have hC : (Nat.card (SupportedCube (j + 1) (Q : Set A)) : ℝ) ≠ 0 := by
    exact_mod_cast (card_supportedCube_pos (j + 1) hQ).ne'
  field_simp

theorem finiteSupportGowersNorm_derivative_mul_count {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (hQ : Q.Nonempty) (j : ℕ) (f : A → ℂ) :
    (Nat.card (SupportedCube (j + 2) (Q : Set A)) : ℝ) *
        finiteSupportGowersNorm (j + 2) Q f ^ (2 ^ (j + 2)) =
      ∑ h ∈ cubeDifferenceSupport Q,
        (Nat.card (SupportedCube (j + 1) (derivativeSupport Q h : Set A)) : ℝ) *
          finiteSupportGowersNorm (j + 1) (derivativeSupport Q h)
            (multiplicativeDerivative f h) ^ (2 ^ (j + 1)) := by
  rw [finiteSupportGowersNorm_pow_mul_count hφ hQ]
  have he := congrArg Complex.re (supportedCubeSum_derivative (j + 1) Q (fun _ ↦ f))
  simp only [crossDerivative_self, Complex.re_sum] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro h hh
  have hφh : ReflectsPairSums φ (derivativeSupport Q h : Set A) :=
    hφ.mono (fun _ hx ↦ (Finset.mem_filter.mp hx).1)
  exact (finiteSupportGowersNorm_pow_mul_count hφh
    ((mem_cubeDifferenceSupport Q h).mp hh) j (multiplicativeDerivative f h)).symm

theorem finiteSupportGowersNorm_derivative {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (hQ : Q.Nonempty) (j : ℕ) (f : A → ℂ) :
    finiteSupportGowersNorm (j + 2) Q f ^ (2 ^ (j + 2)) =
      ∑ h ∈ cubeDifferenceSupport Q,
        ((Nat.card (SupportedCube (j + 1) (derivativeSupport Q h : Set A)) : ℝ) /
          Nat.card (SupportedCube (j + 2) (Q : Set A))) *
          finiteSupportGowersNorm (j + 1) (derivativeSupport Q h)
            (multiplicativeDerivative f h) ^ (2 ^ (j + 1)) := by
  have hC : (Nat.card (SupportedCube (j + 2) (Q : Set A)) : ℝ) ≠ 0 := by
    exact_mod_cast (card_supportedCube_pos (j + 2) hQ).ne'
  calc
    _ = ((Nat.card (SupportedCube (j + 2) (Q : Set A)) : ℝ) *
        finiteSupportGowersNorm (j + 2) Q f ^ (2 ^ (j + 2))) /
          Nat.card (SupportedCube (j + 2) (Q : Set A)) := by field_simp
    _ = _ := by
      rw [finiteSupportGowersNorm_derivative_mul_count hφ hQ, Finset.sum_div]
      simp only [div_mul_eq_mul_div]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

theorem translatedIntegerBox_norm_degree_one (a : ι → ℤ) (f : (ι → ℤ) → ℂ) :
    finiteSupportGowersNorm 1 (translatedIntegerBox a T) f =
      ‖𝔼 x ∈ translatedIntegerBox a T, f x‖ :=
  finiteSupportGowersNorm_degree_one_of_embedding (translatedIntegerBox_reflectsPairSums T a)
    (translatedIntegerBox_nonempty T a) f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDifferenceHom
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_weighted_pair_mean_pow_four_le_box {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (F : X → Y → ℂ) (a : X → ℂ) (b : Y → ℂ)
    (ha : ∀ x, ‖a x‖ ≤ 1) (hb : ∀ y, ‖b y‖ ≤ 1) :
    ‖𝔼 x, 𝔼 y, F x y * a x * b y‖ ^ 4 ≤ (finiteBoxCorrelation F).re := by
  let m : ℂ := 𝔼 x, 𝔼 x', a x * star (a x') * (𝔼 y, F x y * star (F x' y))
  have hleft : (𝔼 y, b y * (𝔼 x, F x y * a x)) = 𝔼 x, 𝔼 y, F x y * a x * b y := by
    simp_rw [Finset.mul_expect]
    rw [Finset.expect_comm]
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    ring
  have hright : (𝔼 x, 𝔼 x', 𝔼 y, (F x y * a x) * star (F x' y * a x')) = m := by
    dsimp [m]
    simp_rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro x' _
    apply Finset.expect_congr rfl
    intro y _
    rw [map_mul]
    ring
  have hfirst : ‖𝔼 x, 𝔼 y, F x y * a x * b y‖ ^ 2 ≤ m.re := by
    simpa only [hleft, hright, one_pow, one_mul] using
      finite_family_cauchy_schwarz_re b (fun x y => F x y * a x) hb
  have hsecond : ‖m‖ ^ 2 ≤ 𝔼 x, 𝔼 x', ‖𝔼 y, F x y * star (F x' y)‖ ^ 2 := by
    have hh := norm_weighted_expect_sq_le
      (fun u : X × X => a u.1 * star (a u.2))
      (fun u : X × X => 𝔼 y, F u.1 y * star (F u.2 y)) (fun u => by
        rw [norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _) (ha _)).trans (ha _))
    simpa only [← Finset.univ_product_univ, Finset.expect_product, m] using hh
  have hm : 0 ≤ m.re := (sq_nonneg _).trans hfirst
  calc
    _ = (‖𝔼 x, 𝔼 y, F x y * a x * b y‖ ^ 2) ^ 2 := by ring
    _ ≤ m.re ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ ≤ ‖m‖ ^ 2 := pow_le_pow_left₀ hm (Complex.re_le_norm m) 2
    _ ≤ _ := hsecond.trans_eq (finiteBoxCorrelation_re_eq_mean_square F).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

theorem residueSmoothMass_congr {K X : Type*} [Fintype K] [Fintype X]
    (r s : K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hrs : ∀ z, (modulus z.2 : ℤ) ∣ s z - r z) :
    shiftedSmoothProductMass (residueProfileCenter r modulus) (residueProfileWidth modulus V) =
      shiftedSmoothProductMass (residueProfileCenter s modulus) (residueProfileWidth modulus V) := by
  rw [residueSmoothWeight_mass r modulus hmodulus V hV,
    residueSmoothWeight_mass s modulus hmodulus V hV, residueSmoothWeight_congr r s modulus V hrs]

theorem boundedColumnResidueRepresentative_congr {K X : Type*} (modulus : X → ℕ)
    (r : ColumnResiduePattern K X modulus) (z : K × X) :
    (modulus z.2 : ℤ) ∣ boundedColumnResidueRepresentative modulus r z - columnResidueRepresentative modulus r z := by
  refine ⟨-(columnResidueRepresentative modulus r z / (modulus z.2 : ℤ)), ?_⟩
  have h := Int.emod_add_mul_ediv (columnResidueRepresentative modulus r z) (modulus z.2 : ℤ)
  unfold boundedColumnResidueRepresentative
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
namespace OAI

section

namespace Erdos3

theorem progression_slice_geometry {L m H : ℕ} (c : ℤ)
    (hL : 0 < L) (hm : 0 < m) (hH : 2 ≤ H) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : integerProgressionSupport c (m : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (hdense : δ * L ≤ ((integerProgressionSupport c (m : ℤ) H).card : ℝ)) :
    δ * L ≤ (m * H : ℕ) ∧ ((m * H : ℕ) : ℝ) < 2 * L ∧
      m ≤ ⌈2 / δ⌉₊ ∧ |(c : ℝ)| ≤ δ⁻¹ * (m * H : ℕ) := by
  have hbase := hsubset (integerProgressionSupport_point c m H hm 0 (by omega))
  have hlast := hsubset (integerProgressionSupport_point c m H hm (H - 1) (by omega))
  have hc0 : 0 ≤ c := by simpa only [Nat.cast_zero, mul_zero, add_zero] using (Finset.mem_Ico.mp hbase).1
  have hh : (c : ℝ) + (m : ℝ) * ((H - 1 : ℕ) : ℝ) < L := by
    exact_mod_cast (Finset.mem_Ico.mp hlast).2
  rw [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one] at hh
  rw [card_integerProgressionSupport c m H hm] at hdense
  exact progression_endpoint_bounds hL hm hH hδ (by exact_mod_cast hc0) hh hdense

end Erdos3

end

section

namespace Erdos3

theorem exists_same_stride_progression_reindex {N m H : ℕ} (c : ℤ)
    (hm : 0 < m) (hH : 0 < H)
    (hsub : integerProgressionSupport c m H ⊆ Finset.Ico (0 : ℤ) N) :
    ∃ r a : ℕ, r < m ∧ a + H ≤ N ∧
      integerProgressionSupport c m H =
        (Finset.Ico (a : ℤ) (a + H)).image (fun x => (r : ℤ) + m * x) := by
  have hbase := hsub (integerProgressionSupport_point c m H hm 0 hH)
  simp only [Nat.cast_zero, mul_zero, add_zero, Finset.mem_Ico] at hbase
  have hc : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hbase.1
  let a := c.toNat / m
  let r := c.toNat % m
  have ha : a ≤ c.toNat := Nat.div_le_self _ _
  have hlast := hsub (integerProgressionSupport_point c m H hm (H - 1) (by omega))
  have hlastN : c.toNat + m * (H - 1) < N := by
    have ht := (Finset.mem_Ico.mp hlast).2
    rw [← hc] at ht
    exact_mod_cast ht
  have hmul : H - 1 ≤ m * (H - 1) := by nlinarith
  have hrepr : c = (r : ℤ) + m * a := by
    rw [← hc]
    exact_mod_cast (Nat.mod_add_div c.toNat m).symm
  refine ⟨r, a, Nat.mod_lt _ hm, by omega, ?_⟩
  rw [hrepr]
  exact integerProgressionSupport_reindex r m a H

theorem exists_bounded_common_stride_reindex {I : Type*} (N H : I → ℕ) (c : I → ℤ)
    {m : ℕ} (hm : 0 < m) (hH : ∀ i, 0 < H i) {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hsub : ∀ i, integerProgressionSupport (c i) m (H i) ⊆ Finset.Ico (0 : ℤ) (N i))
    (hdense : ∀ i, δ * N i ≤ (H i : ℝ)) :
    ∃ d : ℕ, ∃ r a : I → ℕ, 0 < d ∧ d ≤ ⌈2 / δ⌉₊ ∧
      ∀ i, r i < ⌈2 / δ⌉₊ ∧ a i + H i ≤ N i ∧
        integerProgressionSupport (c i) m (H i) =
          (Finset.Ico (a i : ℤ) (a i + H i)).image (fun x => (r i : ℤ) + d * x) := by
  classical
  by_cases hlong : ∃ i, 2 ≤ H i
  · obtain ⟨i, hi⟩ := hlong
    have hbase := hsub i (integerProgressionSupport_point (c i) m (H i) hm 0 (hH i))
    have hNi : 0 < N i := by
      simp only [Nat.cast_zero, mul_zero, add_zero, Finset.mem_Ico] at hbase
      omega
    have hgeom := progression_slice_geometry (c i) hNi hm hi hδ (hsub i)
      (by simpa only [card_integerProgressionSupport (c i) m (H i) hm] using hdense i)
    choose r a hr ha he using fun i => exists_same_stride_progression_reindex (c i) hm (hH i) (hsub i)
    exact ⟨m, r, a, hm, hgeom.2.2.1, fun i => ⟨(hr i).trans_le hgeom.2.2.1, ha i, he i⟩⟩
  · have hsingle (i : I) : H i = 1 := by have := hH i; have := not_exists.mp hlong i; omega
    have he (i : I) : integerProgressionSupport (c i) m (H i) =
        integerProgressionSupport (c i) 1 (H i) := by simp only [hsingle i, integerProgressionSupport_singleton]
    have hsub1 (i : I) : integerProgressionSupport (c i) 1 (H i) ⊆ Finset.Ico (0 : ℤ) (N i) :=
      he i ▸ hsub i
    choose r a hr ha he' using fun i => exists_same_stride_progression_reindex (m := 1)
      (c i) zero_lt_one (hH i) (hsub1 i)
    have hM : 1 ≤ ⌈2 / δ⌉₊ := by
      have h1 : (1 : ℝ) ≤ 2 / δ := (le_div_iff₀ hδ).mpr (by linarith)
      exact_mod_cast h1.trans (Nat.le_ceil _)
    exact ⟨1, r, a, zero_lt_one, hM, fun i => ⟨(hr i).trans_le hM, ha i, (he i).trans (he' i)⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CyclicAffineCharacterPhase
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_affine_cyclic_character_phase {I : Type*} [Fintype I]
    {N : ℕ} [NeZero N] (ξ : (I → ℤ) →+ ZMod N) (ξ₀ : ZMod N) :
    ∃ (a : ℝ) (b : I → ℝ), ∀ (x : I → ℤ) (n : ZMod N),
      CircleFourier.character
        (((n.val : ℝ) * (a + ∑ i, (x i : ℝ) * b i) : ℝ) : CircleFourier.Circle) =
          AddChar.zmodAddEquiv (ξ₀ + ξ x) n := by
  classical
  obtain ⟨a, ha⟩ := CyclicBohr.exists_real_frequency_phase ξ₀
  choose b hb using fun i => CyclicBohr.exists_real_frequency_phase (ξ (Pi.single i 1))
  simp only [CyclicBohr.character] at ha hb
  refine ⟨a, b, ?_⟩
  intro x n
  have hx : ξ x = ∑ i, (x i) • ξ (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    rw [map_sum]
    simp only [map_zsmul]
  rw [CircleFourier.character_affine_integer_combination, ha n, hx]
  simp only [map_add, map_sum, map_zsmul, AddChar.add_apply, AddChar.sum_apply,
    AddChar.zsmul_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [hb i n]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Module

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

variable [Fintype I] [Fintype J]

theorem latticeIntegerLift_projection (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) (z : J → ℤ) :
    Wᗮ.orthogonalProjectionOnto (latticeIntegerLift Λ W bP z).val = (bP.equivFun.symm z).val :=
  congrArg Subtype.val (latticeLiftSection_rightInverse Λ W bP (bP.equivFun.symm z))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter
namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] (U : Submodule ℝ (D → ℝ))

noncomputable def euclideanSubspaceTorusHomeomorph :
    (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) ≃ₜ
        SubspaceArrayTorus Unit U where
  toEquiv := (euclideanSubspaceTorusEquiv U).toEquiv
  continuous_toFun := euclideanSubspaceTorusEquiv_continuous U
  continuous_invFun := euclideanSubspaceTorusEquiv_symm_continuous U

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Matrix

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J]

theorem standardLatticeIntegerLift_projection (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) (z : J → ℤ) :
    Wᗮ.orthogonalProjectionOnto (standardLatticeIntegerLift W bP hP z).val =
      bP.equivFun.symm (fun j => (z j : ℝ)) := by
  have h := latticeIntegerLift_projection (standardEuclideanLattice D) W
    (integerBasisOfReal (projectedIntegerLattice W) bP hP) z
  exact h.trans (integerBasisOfReal_synthesis (projectedIntegerLattice W) bP hP z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedRealCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedRealCoordinates_point (x : (I → ℝ) × (Fin n → ℝ)) :
    mixedRealCoordinates W b o (mixedRealPoint W b o x) = x := by
  change ((orthonormalChart o).symm
      ((normalizedOrthogonalChart W b) ((normalizedOrthogonalChart W b).symm
        ((orthonormalChart o) x.1, x.2))).1,
    ((normalizedOrthogonalChart W b) ((normalizedOrthogonalChart W b).symm
        ((orthonormalChart o) x.1, x.2))).2) = x
  simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.EarlyFiberCapBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem earlyFiberCap_exp_bound {m : ℕ} (a n : Fin m → ℕ) (R V : Fin m → ℝ) {P : ℝ}
    (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P) (hR : ∀ j, 0 < R j) (hV : ∀ j, 0 ≤ V j)
    (ha : ∀ j, (a j : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hVP : ∀ j, V j ≤ Real.exp P) :
    (∏ j, earlyConstantDensityCap (a j) (n j) (R j) (V j)) ≤ Real.exp (earlyFiberCapLog P) := by
  calc
    _ ≤ ∏ _j : Fin m, Real.exp (3*P^2+17*P) :=
      Finset.prod_le_prod (fun j _ => earlyConstantDensityCap_nonneg _ _ (hR j) (hV j))
        (fun j _ => earlyConstantDensityCap_exp_bound _ _ hP (hR j)
          (ha j) (hn j) hA (hRP j) (hVP j))
    _ = (Real.exp (3*P^2+17*P))^m := by simp
    _ ≤ Real.exp (P*(3*P^2+17*P)) :=
      pow_le_exp_mul_of_le_exp (Real.exp_nonneg _) le_rfl (by positivity) m hm
    _ = _ := by congr 1; unfold earlyFiberCapLog; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistParameterPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_normalizedTwist_parameter_partition {I : Type*} [Fintype I]
    [DecidableEq I] (N : I → ℕ) (q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hqexp : (q : ℝ) ≤ Real.exp p)
    (hN : ∀ i, Real.exp (3 * p + 16) ≤ (N i : ℝ)) :
    ∃ P : ∀ i, FiniteProgressionPartition (N i),
      (∀ i a, (P i).step a = q) ∧
      (∀ i a, 0 < (P i).length a) ∧
      (∀ i a, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ (P i).length a) ∧
      (∀ i a (j : Fin ((P i).length a)),
        |((P i).point a j).val / (N i : ℝ) - (P i).start a / (N i : ℝ)| ≤
          Real.exp (-(2 * p)) / 4) ∧
      (∀ i a (j k : Fin ((P i).length a)),
        |((P i).point a j).val / (N i : ℝ) - ((P i).point a k).val / (N i : ℝ)| ≤
          Real.exp (-(2 * p)) / 4) ∧
      (∀ i, (Fintype.card (P i).Label : ℝ) ≤ Real.exp (3 * p + 16)) ∧
      (Fintype.card (∀ i, (P i).Label) : ℝ) ≤
        Real.exp ((Fintype.card I : ℝ) * (3 * p + 16)) := by
  classical
  let H := fun i => exponentialProgressionScale (N i) q p
  have hscale (i : I) := exponentialProgressionScale_bounds (N i) q p hp hq hqexp (hN i)
  let P : ∀ i, FiniteProgressionPartition (N i) := fun i =>
    FiniteProgressionPartition.comparableResidueProgressions (N i) q (H i) hq
      (hscale i).1 (hscale i).2.1
  have hstep (i : I) (a : (P i).Label) : (P i).step a = q :=
    FiniteProgressionPartition.comparableResidueProgressions_step _ _ _ _ _ _ _
  have hlength (i : I) (a : (P i).Label) :
      H i ≤ (P i).length a ∧ (P i).length a < 2 * H i :=
    FiniteProgressionPartition.comparableResidueProgressions_length_bounds _ _ _ _ _ _ _
  have hNpos (i : I) : 0 < N i := by
    exact_mod_cast (Real.exp_pos _).trans_le (hN i)
  have hlower (i : I) (a : (P i).Label) :
      (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ (P i).length a :=
    (hscale i).2.2.1.trans (by exact_mod_cast (hlength i a).1)
  have hcard (i : I) : (Fintype.card (P i).Label : ℝ) ≤ Real.exp (3 * p + 16) :=
    (P i).label_card_le_exp_of_length_lower (hNpos i) (hlower i)
  refine ⟨P, hstep, fun i a => (hscale i).1.trans_le (hlength i a).1, hlower,
    ?_, ?_, hcard, ?_⟩
  · intro i a j
    exact (P i).normalized_point_sub_start_le_of_bound a (hstep i a)
      (hlength i a).2 (hNpos i) (hscale i).2.2.2 j
  · intro i a j k
    exact (P i).normalized_point_sub_point_le_of_bound a (hstep i a)
      (hlength i a).2 (hNpos i) (hscale i).2.2.2 j k
  · calc
      _ = ∏ i, (Fintype.card (P i).Label : ℝ) := by rw [Fintype.card_pi, Nat.cast_prod]
      _ ≤ ∏ _i : I, Real.exp (3 * p + 16) :=
        Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hcard i)
      _ = Real.exp ((Fintype.card I : ℝ) * (3 * p + 16)) := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanJetTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem coefficientCoordinateTori_compact {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)] :
    CompactSpace (CoefficientCoordinateTori (K := K) U) := by
  have h := isCompact_univ.image (coefficientCoordinateTorus_continuous (K := K) U)
  rw [Set.image_univ, Set.range_eq_univ.mpr (coefficientCoordinateTorus_surjective U)] at h
  exact ⟨h⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientProductHaar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

theorem coefficientCoordinateTorus_measurePreserving {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ s : CoefficientSlot K m, MeasurableSpace (SubspaceArrayTorus Unit (U s.1))]
    [∀ s : CoefficientSlot K m, BorelSpace (SubspaceArrayTorus Unit (U s.1))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)] :
    MeasurePreserving (coefficientCoordinateTorus U) μ (Measure.pi ν) := by
  let _ := coefficientCoordinateTori_compact (K := K) U
  let _ : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  let _ : (Measure.pi ν).IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := Measure.pi ν) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving (coefficientCoordinateTorus_continuous U)
    (coefficientCoordinateTorus_surjective U) (by simp)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientProductLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem coefficientProductDensity_probability {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ s : CoefficientSlot K m, MeasurableSpace (SubspaceArrayTorus Unit (U s.1))]
    [∀ s : CoefficientSlot K m, BorelSpace (SubspaceArrayTorus Unit (U s.1))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)]
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hf : ∀ s, Integrable (f s) (ν s)) (hf0 : ∀ s x, 0 ≤ f s x)
    (hmass : ∀ s, (∫ x, f s x ∂ν s) = 1) :
    Integrable (coefficientProductDensity U f) μ ∧
      (∀ x, 0 ≤ coefficientProductDensity U f x) ∧
      (∫ x, coefficientProductDensity U f x ∂μ) = 1 := by
  let g : CoefficientCoordinateTori (K := K) U → ℝ := fun y => ∏ s, f s (y s)
  have hg : Integrable g (Measure.pi ν) := Integrable.fintype_prod_dep hf
  have hp := coefficientCoordinateTorus_measurePreserving U μ ν
  refine ⟨hp.integrable_comp_of_integrable hg, coefficientProductDensity_nonneg U f hf0, ?_⟩
  have hg' : AEStronglyMeasurable g (Measure.map (coefficientCoordinateTorus U) μ) := by
    simpa only [hp.map_eq] using hg.aestronglyMeasurable
  calc
    (∫ x, coefficientProductDensity U f x ∂μ) = ∫ y, g y ∂Measure.pi ν := by
      simpa only [hp.map_eq, g, coefficientProductDensity] using
        (integral_map hp.measurable.aemeasurable hg').symm
    _ = ∏ s, ∫ x, f s x ∂ν s := integral_fintype_prod_eq_prod f
    _ = 1 := by simp only [hmass, Finset.prod_const_one]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))

theorem principalIntervalLength_support {k : ℤ}
    (hk : k ∈ (principalIntegerPMF K T γ hK hT hγ hlarge).support) :
    k ∈ Finset.Ico 0 (principalIntervalLength K T γ : ℤ) := by
  have hb := principalIntegerPMF_support hK hT hγ hlarge hk
  have he : T * (k : ℝ) / K = (k : ℝ) / (K / T) := by field_simp
  rw [he] at hb
  have hlo := (lt_div_iff₀ (div_pos hK hT)).mp hb.1
  have hhi := (div_lt_iff₀ (div_pos hK hT)).mp hb.2
  have hk0 : (0 : ℝ) ≤ k := (mul_pos hγ (div_pos hK hT)).le.trans hlo.le
  have hkL : (k : ℝ) < principalIntervalLength K T γ :=
    hhi.trans_le (Nat.le_ceil _)
  exact Finset.mem_Ico.mpr ⟨by exact_mod_cast hk0, by exact_mod_cast hkL⟩

include hK hT hγ hlarge in
theorem principalIntervalWeight_range (x : Option Empty → ℝ) :
    0 ≤ principalIntervalWeight K T γ x ∧ principalIntervalWeight K T γ x ≤ 16 := by
  have hL := principalIntervalLength_pos hK hT hγ
  have ha0 : 0 ≤ (principalIntervalLength K T γ : ℝ) / (K / T) := by positivity
  have ha : (principalIntervalLength K T γ : ℝ) / (K / T) ≤ 4 * γ :=
    (div_le_iff₀ (div_pos hK hT)).mpr (principalIntervalLength_bounds hK hT hγ hlarge).2
  have hb := normalizedIntegerInterpolation_range (K / T) (3 * γ / 2) (γ / 2)
    (div_pos hK hT) (by positivity) hlarge
      ((principalIntervalLength K T γ : ℝ) / (K / T) * x none)
  constructor
  · exact mul_nonneg ha0 hb.1
  · calc
      principalIntervalWeight K T γ x ≤
          ((principalIntervalLength K T γ : ℝ) / (K / T)) * (2 / (γ / 2)) :=
        mul_le_mul_of_nonneg_left hb.2 ha0
      _ ≤ (4 * γ) * (2 / (γ / 2)) :=
        mul_le_mul_of_nonneg_right ha (by positivity)
      _ = 16 := by field_simp; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedMaskedCoefficientFourier
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedMaskedFourierBudget (m : ℕ) (P : ℝ) : ℝ :=
  let Q := allocatedFourierLogBudget m P
  P + (4 * Q + 2) ^ 4 + (4 * Q * (4 * Q + 2) ^ 4 + Q)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AnchoredCoefficientFourierNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedResidueSmoothPMF_weighted_fourier_normalization {K I J : Type*}
    [Fintype K] [Fintype I] [Fintype J]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (w : (K × I → ℤ) → ℂ) (c : J → ℂ) (u : J → (K × I → ℤ) → ℂ)
    (keep : J → Prop) [DecidablePred keep] {C τ : ℝ}
    (hc : (∑ j, ‖c j‖) ≤ C) (hτ : 0 ≤ τ)
    (hkeep : ∀ j, keep j → ∀ x, u j x = 1)
    (hdiscard : ∀ j, ¬keep j →
      ‖∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        (w x * u j x)‖ ≤ τ) :
    ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        (w x * ∑ j, c j * u j x)) -
      (∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * w x) *
        (∑ j, if keep j then c j else 0)‖ ≤ C * τ := by
  have hproject := selectedResidueSmoothPMF_discard_error modulus G V hV hZ
    w c u keep hc hτ hdiscard
  have heq (x : K × I → ℤ) :
      (∑ j, if keep j then c j * u j x else 0) =
        ∑ j, if keep j then c j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : keep j
    · simp only [hj, ite_true, hkeep j hj x, mul_one]
    · simp only [hj, ite_false]
  simp_rw [heq, ← mul_assoc] at hproject
  rw [tsum_mul_right] at hproject
  simpa only [mul_assoc] using hproject

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalCoverLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] (U : Submodule ℝ (D → ℝ))
variable [MeasurableSpace (SubspaceArrayTorus Unit U)] [BorelSpace (SubspaceArrayTorus Unit U)]

noncomputable def euclideanSubspaceTorusMeasurableEquiv :
    (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) ≃ᵐ
        SubspaceArrayTorus Unit U := by
  let : BorelSpace (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) :=
    QuotientAddGroup.borelSpace
  exact (euclideanSubspaceTorusHomeomorph U).toMeasurableEquiv

variable (ν : Measure (euclideanSubspace U ⧸
  (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup))

noncomputable def euclideanSubspaceTorusMeasure : Measure (SubspaceArrayTorus Unit U) :=
  Measure.map (euclideanSubspaceTorusMeasurableEquiv U) ν

theorem euclideanSubspaceTorusMeasure_probability [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (euclideanSubspaceTorusMeasure U ν) := by
  unfold euclideanSubspaceTorusMeasure
  exact Measure.isProbabilityMeasure_map (euclideanSubspaceTorusMeasurableEquiv U).measurable.aemeasurable

theorem euclideanSubspaceTorusMeasure_invariant [ν.IsAddLeftInvariant] :
    (euclideanSubspaceTorusMeasure U ν).IsAddLeftInvariant :=
  isAddLeftInvariant_map (euclideanSubspaceTorusEquiv U).toAddMonoidHom.toAddHom
    (euclideanSubspaceTorusMeasurableEquiv U).measurable (euclideanSubspaceTorusEquiv U).surjective

theorem euclideanSubspaceTorusMeasure_mass
    (f : (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) → ℝ)
    (hf : Integrable f ν) (hm : (∫ x, f x ∂ν) = 1) :
    Integrable (fun y => f ((euclideanSubspaceTorusEquiv U).symm y))
        (euclideanSubspaceTorusMeasure U ν) ∧
      (∫ y, f ((euclideanSubspaceTorusEquiv U).symm y)
        ∂euclideanSubspaceTorusMeasure U ν) = 1 := by
  let e := euclideanSubspaceTorusMeasurableEquiv U
  change Integrable (fun y => f (e.symm y)) (Measure.map e ν) ∧
    (∫ y, f (e.symm y) ∂Measure.map e ν) = 1
  constructor
  · apply (integrable_map_equiv e _).mpr
    simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using hf
  · rw [integral_map_equiv]
    simpa only [MeasurableEquiv.symm_apply_apply] using hm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiberCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem coefficientFiberMap_nonconstant {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (y : CoefficientTorus (K := Empty) U) (x : CoefficientTorus (K := K) U)
    (s : CoefficientSlot K m) (hs : s.2.val ≠ 0) :
    coefficientCoordinateTorus U (coefficientFiberMap U t y x) s =
      coefficientCoordinateTorus U x s := by
  simp only [coefficientFiberMap, map_add, map_sub, Pi.add_apply, Pi.sub_apply,
    constantCoefficientTorusMap_nonconstant U _ s hs, sub_zero, zero_add]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

theorem coefficientFiberAverage_nonneg {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) (t : K → ℤ)
    (F : CoefficientTorus (K := K) U → ℝ) (hF : ∀ x, 0 ≤ F x)
    (y : CoefficientTorus (K := Empty) U) : 0 ≤ coefficientFiberAverage U μ t F y :=
  integral_nonneg (fun x => hF (coefficientFiberMap U t y x))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem coefficientProductDensity_fiber_bound {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hf0 : ∀ s x, 0 ≤ f s x) (C : Fin m → ℝ)
    (hC : ∀ (s : CoefficientSlot K m), s.2.val = 0 → ∀ x, f s x ≤ C s.1)
    (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) (x : CoefficientTorus (K := K) U) :
    coefficientProductDensity U f (coefficientFiberMap U t y x) ≤
      (∏ j, C j) * coefficientProductDensity U (nonconstantCoefficientFactor U f) x := by
  calc
    _ ≤ ∏ s : CoefficientSlot K m,
        (if s.2.val = 0 then C s.1 else 1) *
          nonconstantCoefficientFactor U f s (coefficientCoordinateTorus U x s) := by
      apply Finset.prod_le_prod (fun s _ => hf0 s _)
      intro s _
      by_cases hs : s.2.val = 0
      · simpa only [nonconstantCoefficientFactor, if_pos hs, mul_one] using hC s hs
          (coefficientCoordinateTorus U (coefficientFiberMap U t y x) s)
      · simp only [nonconstantCoefficientFactor, if_neg hs, one_mul,
          coefficientFiberMap_nonconstant U t y x s hs, le_refl]
    _ = _ := by rw [Finset.prod_mul_distrib, constantCoefficientCap_product]; rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem nonconstantCoefficientDensity_probability {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
    [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)]
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hfi : ∀ s, Integrable (f s) (ν s)) (hf0 : ∀ s x, 0 ≤ f s x)
    (hmass : ∀ s, (∫ x, f s x ∂ν s) = 1) :
    Integrable (coefficientProductDensity U (nonconstantCoefficientFactor U f)) μ ∧
      (∀ x, 0 ≤ coefficientProductDensity U (nonconstantCoefficientFactor U f) x) ∧
      (∫ x, coefficientProductDensity U (nonconstantCoefficientFactor U f) x ∂μ) = 1 := by
  apply coefficientProductDensity_probability U μ ν
  · intro s
    change Integrable (fun x => if s.2.val = 0 then 1 else f s x) (ν s)
    by_cases hs : s.2.val = 0
    · simpa only [if_pos hs] using
        (integrable_const (1 : ℝ) (μ := ν s))
    · simpa only [if_neg hs] using hfi s
  · intro s x
    by_cases hs : s.2.val = 0
    · simp only [nonconstantCoefficientFactor, if_pos hs, zero_le_one]
    · simpa only [nonconstantCoefficientFactor, if_neg hs] using hf0 s x
  · intro s
    by_cases hs : s.2.val = 0
    · simp only [nonconstantCoefficientFactor, if_pos hs, integral_const,
        probReal_univ, one_smul]
    · simpa only [nonconstantCoefficientFactor, if_neg hs] using hmass s

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

noncomputable def canonicalCoefficientFactor (s : CoefficientSlot K m)
    (y : SubspaceArrayTorus Unit (U s.1)) : ℝ :=
  canonicalMixedDensity (euclideanSubspace (U s.1)) (b s.1) (hb s.1) (o s.1)
    (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => p s.1 i s.2)
    ((euclideanSubspaceTorusEquiv (U s.1)).symm y)

theorem canonicalCoefficientDensity_product :
    canonicalCoefficientDensity U b hb o c w p =
      coefficientProductDensity U (canonicalCoefficientFactor U b hb o c w p) := by
  funext x
  unfold canonicalCoefficientDensity canonicalArrayDensity coefficientProductDensity
  rw [Fintype.prod_sigma]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem unconditionedSpatialWidthCutoff_bounds {K X : Type*} [Fintype X]
    {B τ L σ : ℝ} (hB : 0 ≤ B) (hτ : 0 < τ) (hτhalf : τ ≤ 1/2)
    (hbudget : 2 * (Fintype.card X : ℝ) * τ ≤ σ / 8)
    (N : X → ℕ) (hN : ∀ i, unconditionedSpatialWidthCutoff B τ L ≤ (N i : ℝ)) :
    (∀ i, 0 < N i) ∧
    (∀ i, 4 ≤ τ * (N i : ℝ)) ∧
    (∀ z : Option K × X, 0 < trimmedSpatialWidths B τ N z) ∧
    (∀ z : Option K × X, 8 * (probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth (fun _ : X => 1) (trimmedSpatialWidths B τ N) z) ∧
    (∀ z : Option K × X, L ≤ trimmedSpatialWidths B τ N z) ∧
    (∀ i, 2 * spatialTrimMargin τ N i < N i) ∧
    2 * (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ σ / 8 := by
  have hsize (i : X) : 4 ≤ τ * (N i : ℝ) := by
    have hh := (le_max_left _ _).trans (hN i)
    have hh' := (div_le_iff₀ hτ).mp hh
    linarith
  have hpos (i : X) : 0 < N i := by
    have hh : 0 < (N i : ℝ) := by nlinarith [hsize i]
    exact_mod_cast hh
  let M : ℝ := max (8 * (probabilityProfileLipschitz : ℝ)) L
  have hM : 0 ≤ M := (by positivity : (0 : ℝ) ≤ 8 * (probabilityProfileLipschitz : ℝ)).trans
    (le_max_left _ _)
  have hwide (i : X) : 8 * (1 + B) * M ≤ τ * (N i : ℝ) := by
    have hh := (le_max_right _ _).trans (hN i)
    have hh' := (div_le_iff₀ hτ).mp hh
    linarith
  have hwidth (z : Option K × X) : M ≤ trimmedSpatialWidths B τ N z := by
    rcases z with ⟨k, i⟩
    cases k with
    | none =>
      change M ≤ τ * ((N i : ℝ) / 8)
      have hh : 8 * M ≤ 8 * (1 + B) * M := by nlinarith
      nlinarith [hwide i]
    | some k =>
      change M ≤ τ * (1 * (N i : ℝ) / (8 * (1 + B)))
      rw [one_mul, ← mul_div_assoc]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (1 + B))).mpr
      nlinarith [hwide i]
  refine ⟨hpos, hsize, trimmedSpatialWidths_pos hB hτ N hpos, ?_, ?_,
    spatialTrimMargin_proper hτhalf N hpos hsize,
    (spatialTrimMargin_error_bound N hpos hsize).trans hbudget⟩
  · intro z
    change 8 * (probabilityProfileLipschitz : ℝ) ≤ trimmedSpatialWidths B τ N z / (1 : ℕ)
    simpa only [Nat.cast_one, div_one] using (le_max_left _ _).trans (hwidth z)
  · intro z
    exact (le_max_right _ _).trans (hwidth z)

theorem unconditionedSpatialWidthBudget {K X : Type*} [Fintype X]
    {B L σ : ℝ} (hB : 0 ≤ B) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (N : X → ℕ)
    (hN : ∀ i, unconditionedSpatialWidthCutoff B
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) L ≤ (N i : ℝ)) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    (∀ i, 0 < N i) ∧
    (∀ i, 4 ≤ τ * (N i : ℝ)) ∧
    (∀ z : Option K × X, 0 < trimmedSpatialWidths B τ N z) ∧
    (∀ z : Option K × X, 8 * (probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth (fun _ : X => 1) (trimmedSpatialWidths B τ N) z) ∧
    (∀ z : Option K × X, L ≤ trimmedSpatialWidths B τ N z) ∧
    (∀ i, 2 * spatialTrimMargin τ N i < N i) ∧
    2 * (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ σ / 8 := by
  obtain ⟨hτ, hτhalf, hbudget⟩ := unconditionedSpatialTrimFraction_bounds (Fintype.card X) hσ hσ1
  exact unconditionedSpatialWidthCutoff_bounds hB hτ hτhalf hbudget N hN

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnchoredReferenceDomination
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem trimmedIntegerBox_card_ratio_le_two {I : Type*} [Fintype I] [DecidableEq I]
    (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (hloss : (∑ i, 2 * (R i : ℝ) / N i) ≤ 1/2) :
    ((integerBox N).card : ℝ) / (trimmedIntegerBox N R).card ≤ 2 := by
  have hA : (0 : ℝ) < (trimmedIntegerBox N R).card := by
    exact_mod_cast (trimmedIntegerBox_nonempty N R hR).card_pos
  have hN (i : I) : 0 < N i := lt_of_le_of_lt (Nat.zero_le _) (hR i)
  have hBnat : 0 < (integerBox N).card := by
    rw [card_integerBox]
    exact Finset.prod_pos (fun i _ => hN i)
  have hB : (0 : ℝ) < (integerBox N).card := by exact_mod_cast hBnat
  have h := (trimmedIntegerBox_card_deficit N R hN (fun i => (hR i).le)).trans hloss
  have hh : (1/2 : ℝ) ≤ ((trimmedIntegerBox N R).card : ℝ) / (integerBox N).card := by linarith
  have hm := (le_div_iff₀ hB).mp hh
  apply (div_le_iff₀ hA).mpr
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledCommonSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem normalizedSupportedCubeSum_self_re {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Fintype B] [DecidableEq B] {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    (normalizedSupportedCubeSum (j + 1) Q (fun _ => f)).re =
      finiteSupportGowersNorm (j + 1) Q f ^ (2 ^ (j + 1)) := by
  rw [finiteSupportGowersNorm_eq_restricted hφ, restrictedGowersNorm_imageExtension_pow hφ]
  exact Complex.div_natCast_re _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SampledCommonBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_dense_box_inner_family {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ) :
    ∃ D : Finset (Finset (I → ℤ)),
      (D.card : ℝ) ≤ Real.exp ((5 * p + 20) * Fintype.card I + p + 2) ∧
      (∀ A ∈ D, ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ),
        0 < m ∧ m ≤ ⌈2 / Real.exp (-p)⌉₊ ∧ A = commonStrideBox c m H) ∧
      ∀ (c : I → ℤ) (m : ℕ) (H : I → ℕ), 0 < m → (∀ i, 0 < H i) →
        (∀ i, integerProgressionSupport (c i) m (H i) ⊆ Finset.Ico (0 : ℤ) (N i)) →
        (∀ i, Real.exp (-p) * N i ≤ (H i : ℝ)) →
        ∃ A ∈ D, A.Nonempty ∧ A ⊆ commonStrideBox c m H ∧
          2 * (1 - (A.card : ℝ) / (commonStrideBox c m H).card) ≤
            Fintype.card I * Real.exp (-p) := by
  classical
  choose C hcount hshape hcover using fun i => exists_finite_inner_interval_family hp (N i)
  let M := ⌈2 / Real.exp (-p)⌉₊
  let D := finiteCommonStrideFamily M C
  have hprod : (∏ i, ((C i).card : ℝ)) ≤ Real.exp ((4 * p + 18) * Fintype.card I) := by
    calc
      _ ≤ ∏ _i : I, Real.exp (4 * p + 18) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hcount i)
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
        congr 1
        ring
  refine ⟨D, ?_, fun A hA => finiteCommonStrideFamily_shape M C hshape hA, ?_⟩
  · calc
      (D.card : ℝ) ≤ (M : ℝ) ^ (Fintype.card I + 1) * ∏ i, ((C i).card : ℝ) := by
        exact_mod_cast finiteCommonStrideFamily_card M C
      _ ≤ Real.exp (p + 2) ^ (Fintype.card I + 1) *
          Real.exp ((4 * p + 18) * Fintype.card I) :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (commonStrideCount_exp_bound hp) _)
          hprod (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) (by positivity)
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
  · intro c m H hm hH hsub hdense
    obtain ⟨d, r, a, hd, hdM, hcoord⟩ := exists_bounded_common_stride_reindex N H c hm hH
      (Real.exp_pos _) (Real.exp_le_one_iff.mpr (by linarith)) hsub hdense
    choose S hSC hSn hSsub hShalf hSerr using fun i =>
      hcover i (a i) (H i) (hcoord i).2.1 (hH i) (hdense i)
    let Aaxis (i : I) := (S i).image (fun x => (r i : ℤ) + d * x)
    let A := Fintype.piFinset Aaxis
    have hg (i : I) : Function.Injective (fun x : ℤ => (r i : ℤ) + d * x) := by
      intro x y he
      exact mul_left_cancel₀ (by exact_mod_cast hd.ne' : (d : ℤ) ≠ 0) (add_left_cancel he)
    have hAsub (i : I) : Aaxis i ⊆ integerProgressionSupport (c i) m (H i) := by
      rw [(hcoord i).2.2]
      exact Finset.image_subset_image (hSsub i)
    have hB (i : I) : (integerProgressionSupport (c i) m (H i)).Nonempty := by
      apply Finset.card_pos.mp
      simpa only [card_integerProgressionSupport _ _ _ hm] using hH i
    refine ⟨A, mem_finiteCommonStrideFamily M C hd hdM r (fun i => (hcoord i).1) S hSC,
      Fintype.piFinset_nonempty.mpr (fun i => (hSn i).image _),
      Fintype.piFinset_subset _ _ hAsub, ?_⟩
    have hloss := piFinset_inner_normalized_loss Aaxis
      (fun i => integerProgressionSupport (c i) m (H i)) hB hAsub
      (fun _ => Real.exp (-p)) (fun i => by
        simpa only [Aaxis, Finset.card_image_of_injective _ (hg i),
          card_integerProgressionSupport _ _ _ hm] using hSerr i)
    simpa only [A, commonStrideBox, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hloss

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OverlapCubeWeights
namespace OAI

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem box_overlap_cube_weight (a : ι → ℤ) (T : ι → ℕ) [∀ i, NeZero (T i)]
    (j : ℕ) {h : ι → ℤ} (hh : h ∈ cubeDifferenceSupport (translatedIntegerBox a T))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsize : δ * (translatedIntegerBox a T).card ≤
      ((derivativeSupport (translatedIntegerBox a T) h).card : ℝ)) :
    let Q := translatedIntegerBox a T
    let R := derivativeSupport Q h
    ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) ^ Fintype.card ι * δ ^ (j + 1) *
        ((R.card : ℝ) / (Q.card : ℝ) ^ 2) ≤
      (Nat.card (SupportedCube (j + 1) (R : Set (ι → ℤ))) : ℝ) /
        Nat.card (SupportedCube (j + 2) (Q : Set (ι → ℤ))) := by
  let Q := translatedIntegerBox a T
  let lengths := fun i => ((T i : ℤ) - |h i|).toNat
  let origin := fun i => a i + max 0 (-h i)
  let : ∀ i, NeZero (lengths i) := fun i => ⟨(box_overlap_length_pos a T hh i).ne'⟩
  have hR : derivativeSupport Q h = translatedIntegerBox origin lengths :=
    derivativeSupport_translatedIntegerBox a T h
  have hC := (translatedIntegerBox_cubeCount_bounds lengths origin (j + 1)).1
  rw [← hR] at hC
  have hC' : ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) ^ Fintype.card ι *
      ((derivativeSupport Q h).card : ℝ) ^ (j + 2) ≤
      Nat.card (SupportedCube (j + 1) (derivativeSupport Q h : Set (ι → ℤ))) := by
    convert hC using 1
    push_cast
    ring
  apply overlap_weight_comparison j
    (by exact_mod_cast (translatedIntegerBox_nonempty T a).card_pos)
    (Nat.cast_nonneg _) (by positivity) hδ
    (by exact_mod_cast card_supportedCube_pos (j + 2) (translatedIntegerBox_nonempty T a))
    _ hC' hsize
  exact_mod_cast card_supportedCube_le (j + 2) Q

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxOverlapSize
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem box_gowers_lower_bound_of_overlaps {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (T : ι → ℕ) [∀ i, NeZero (T i)] (j : ℕ)
    (f : (ι → ℤ) → ℂ) (P : (ι → ℤ) → Prop) [DecidablePred P]
    {δ η μ : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hμ : μ ≤ ∑ h ∈ cubeDifferenceSupport (translatedIntegerBox a T),
      (((derivativeSupport (translatedIntegerBox a T) h).card : ℝ) /
        ((translatedIntegerBox a T).card : ℝ) ^ 2) * (if P h then (1 : ℝ) else 0))
    (hretained : ∀ h ∈ cubeDifferenceSupport (translatedIntegerBox a T), P h →
      δ * (translatedIntegerBox a T).card ≤
        ((derivativeSupport (translatedIntegerBox a T) h).card : ℝ) ∧
      η ≤ finiteSupportGowersNorm (j + 1) (derivativeSupport (translatedIntegerBox a T) h)
        (multiplicativeDerivative f h)) :
    ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) ^ Fintype.card ι * δ ^ (j + 1) *
        η ^ (2 ^ (j + 1)) * μ ≤
      finiteSupportGowersNorm (j + 2) (translatedIntegerBox a T) f ^ (2 ^ (j + 2)) := by
  let Q := translatedIntegerBox a T
  let c := ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) ^ Fintype.card ι
  let K := c * δ ^ (j + 1) * η ^ (2 ^ (j + 1))
  let W := fun h => ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2
  let V := fun h => (Nat.card (SupportedCube (j + 1) (derivativeSupport Q h : Set (ι → ℤ))) : ℝ) /
    Nat.card (SupportedCube (j + 2) (Q : Set (ι → ℤ)))
  let N := fun h => finiteSupportGowersNorm (j + 1) (derivativeSupport Q h) (multiplicativeDerivative f h)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hN (h : ι → ℤ) : 0 ≤ N h := by
    have hφ := (translatedIntegerBox_reflectsPairSums T a).mono
      (fun _ hx => (Finset.mem_filter.mp hx).1 :
        (derivativeSupport Q h : Set (ι → ℤ)) ⊆ (Q : Set (ι → ℤ)))
    dsimp [N]
    rw [finiteSupportGowersNorm_eq_restricted hφ]
    exact restrictedGowersNorm_nonneg j _ _
  have hpoint (h : ι → ℤ) (hh : h ∈ cubeDifferenceSupport Q) :
      K * (W h * (if P h then (1 : ℝ) else 0)) ≤ V h * N h ^ (2 ^ (j + 1)) := by
    by_cases hp : P h
    · simp only [if_pos hp, mul_one]
      have hw : c * δ ^ (j + 1) * W h ≤ V h :=
        box_overlap_cube_weight a T j hh hδ (hretained h hh hp).1
      have hn : η ^ (2 ^ (j + 1)) ≤ N h ^ (2 ^ (j + 1)) :=
        pow_le_pow_left₀ hη (hretained h hh hp).2 _
      calc
        _ = (c * δ ^ (j + 1) * W h) * η ^ (2 ^ (j + 1)) := by dsimp [K]; ring
        _ ≤ _ := mul_le_mul hw hn (pow_nonneg hη _) (by dsimp [V]; positivity)
    · simp only [if_neg hp, mul_zero]
      exact mul_nonneg (by dsimp [V]; positivity) (pow_nonneg (hN h) _)
  calc
    _ ≤ K * (∑ h ∈ cubeDifferenceSupport Q, W h * (if P h then (1 : ℝ) else 0)) :=
      mul_le_mul_of_nonneg_left hμ hK
    _ = ∑ h ∈ cubeDifferenceSupport Q, K * (W h * (if P h then (1 : ℝ) else 0)) :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ h ∈ cubeDifferenceSupport Q, V h * N h ^ (2 ^ (j + 1)) := Finset.sum_le_sum hpoint
    _ = _ := (finiteSupportGowersNorm_derivative (translatedIntegerBox_reflectsPairSums T a)
      (translatedIntegerBox_nonempty T a) j f).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubeSignalAlgebra
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixedCubeObservable_norm_le_one {J : Type*} {d : ℕ}
    (f : J → (Fin 2 → ℤ) → ℂ) (hf : ∀ j x, ‖f j x‖ ≤ 1)
    (a : (Fin d → Bool) → J) (x : Fin (d + 2) → ℤ) : ‖mixedCubeObservable f a x‖ ≤ 1 := by
  unfold mixedCubeObservable
  rw [norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro ω _
  rw [conjugationPower_norm]
  exact hf _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticCyclicAntisymmetric
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem exists_reflected_corner_correlation (F : G → G → ℂ) (b₁ b₂ b₃ : G → ℂ)
    (hb₁ : ∀ x, ‖b₁ x‖ ≤ 1) (hb₂ : ∀ y, ‖b₂ y‖ ≤ 1) (hb₃ : ∀ z, ‖b₃ z‖ ≤ 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcorr : ρ ≤ (𝔼 x, 𝔼 y, F y x * b₁ x * b₂ y * b₃ (x + y)).re) :
    ∃ (z : G) (b : G → ℂ), (∀ y, ‖b y‖ ≤ 1) ∧
      ρ ^ 2 ≤ (𝔼 y, 𝔼 y',
        F y (z - y - y') * star (F y' (z - y - y')) * b y * star (b y')).re := by
  let B (z y : G) := b₂ y * star (b₃ (z - y))
  have hnorm : ρ ≤ ‖𝔼 x, b₁ x * (𝔼 y, F y x * b₂ y * b₃ (x + y))‖ := by
    have heq : (𝔼 x, b₁ x * (𝔼 y, F y x * b₂ y * b₃ (x + y))) =
        𝔼 x, 𝔼 y, F y x * b₁ x * b₂ y * b₃ (x + y) := by
      simp_rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      apply Finset.expect_congr rfl
      intro y _
      ring
    rw [heq]
    exact hcorr.trans (Complex.re_le_norm _)
  have hcs := finite_family_cauchy_schwarz_re b₁
    (fun y x => F y x * b₂ y * b₃ (x + y)) hb₁
  simp only [one_pow, one_mul] at hcs
  have hchange : (𝔼 y, 𝔼 y', 𝔼 x,
      (F y x * b₂ y * b₃ (x + y)) * star (F y' x * b₂ y' * b₃ (x + y'))) =
      𝔼 z, 𝔼 y, 𝔼 y',
        F y (z - y - y') * star (F y' (z - y - y')) * B z y * star (B z y') := by
    calc
      _ = 𝔼 y, 𝔼 y', 𝔼 z,
          F y (z - y - y') * star (F y' (z - y - y')) * B z y * star (B z y') := by
        apply Finset.expect_congr rfl
        intro y _
        apply Finset.expect_congr rfl
        intro y' _
        apply Fintype.expect_equiv (Equiv.addRight (y + y'))
        intro x
        have h₁ : x + (y + y') - y = x + y' := by abel
        have h₂ : x + (y + y') - y' = x + y := by abel
        simp only [Equiv.coe_addRight, B, h₁, h₂, add_sub_cancel_right, star_mul, star_star]
        ring
      _ = 𝔼 y, 𝔼 z, 𝔼 y',
          F y (z - y - y') * star (F y' (z - y - y')) * B z y * star (B z y') := by
        apply Finset.expect_congr rfl
        intro y _
        exact Finset.expect_comm _ _ _
      _ = _ := Finset.expect_comm _ _ _
  have hmean := (pow_le_pow_left₀ hρ hnorm 2).trans hcs
  rw [hchange, expect_re, Fintype.expect_eq_sum_div_card] at hmean
  have hsum : (∑ _z : G, ρ ^ 2) ≤ ∑ z : G, (𝔼 y, 𝔼 y',
      F y (z - y - y') * star (F y' (z - y - y')) * B z y * star (B z y')).re := by
    have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using
      (le_div_iff₀ hcard).mp hmean
  obtain ⟨z, _, hz⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨z, B z, ?_, hz⟩
  intro y
  simp only [B, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hb₂ _)).trans (hb₃ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

section

namespace Erdos3

noncomputable def goodKernelUniformCandidate {α J : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] {L B : ℕ} {κ : ℝ}
    (selection : α ↪ J) (x : J → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection κ B x) (_height : ℕ) : Fin B :=
  ⟨Classical.choose hx.2 - 1, by
    have h := Classical.choose_spec hx.2
    omega⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FixedPrincipalCoefficientSpectrum
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

def positiveModerateSpectrumBlockCount (n j t : ℕ) : ℕ :=
  max (positiveModerateSpectrumExponent n j) (positiveModerateLengthExponent n * t) + 1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def positiveModerateAccuracyScale (n j t : ℕ) (U V W : ℝ) : ℝ :=
  1 + (2 * positiveModerateSpectrumConstant n j U V * 2 ^ positiveModerateSpectrumExponent n j +
    W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t)

noncomputable def positiveModerateRetainedBias (n j t : ℕ) (U V W ε : ℝ) : ℝ :=
  ε / positiveModerateAccuracyScale n j t U V W

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeUnitBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem finiteSupportGowersNorm_le_one_of_embedding
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]
    {φ : A →+ B} {Q : Finset A} (hφ : ReflectsPairSums φ (Q : Set A))
    (j : ℕ) (f : A → ℂ) (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) :
    finiteSupportGowersNorm (j + 1) Q f ≤ 1 := by
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) zero_le_one
  rw [one_pow, ← normalizedSupportedCubeSum_self_re hφ]
  exact (Complex.re_le_norm _).trans
    (normalizedSupportedCubeSum_norm_le_one (j + 1) Q (fun _ => f) (fun _ => hf))

theorem normalizedSupportedCubeSum_le_vertex
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]
    {φ : A →+ B} {Q : Finset A} (hφ : ReflectsPairSums φ (Q : Set A))
    (j : ℕ) (F : (Fin (j + 1) → Bool) → A → ℂ)
    (hF : ∀ ω x, x ∈ Q → ‖F ω x‖ ≤ 1) (ω₀ : Fin (j + 1) → Bool) :
    ‖normalizedSupportedCubeSum (j + 1) Q F‖ ≤ finiteSupportGowersNorm (j + 1) Q (F ω₀) := by
  have hnonneg (ω) : 0 ≤ finiteSupportGowersNorm (j + 1) Q (F ω) := by
    rw [finiteSupportGowersNorm_eq_restricted hφ]
    exact restrictedGowersNorm_nonneg _ _ _
  have hprod : (∏ ω, finiteSupportGowersNorm (j + 1) Q (F ω)) ≤
      ∏ ω, if ω = ω₀ then finiteSupportGowersNorm (j + 1) Q (F ω₀) else 1 := by
    apply Finset.prod_le_prod (fun ω _ => hnonneg ω)
    intro ω _
    split_ifs with h
    · subst ω; exact le_rfl
    · exact finiteSupportGowersNorm_le_one_of_embedding hφ j (F ω) (hF ω)
  have hcs : ‖normalizedSupportedCubeSum (j + 1) Q F‖ ≤
      ∏ ω, finiteSupportGowersNorm (j + 1) Q (F ω) := by
    simpa only [normalizedSupportedCubeSum, norm_div, Complex.norm_natCast] using
      norm_supportedCubeSum_le_of_embedding hφ j F
  exact hcs.trans (by simpa using hprod)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedScaleCollisionBudget
namespace OAI

section

namespace Erdos3

noncomputable def allocatedFixedScaleCollisionLog (m : ℕ) (P : ℝ) : ℝ :=
  VectorPolynomial.allocatedFourierLogBudget m P + 2*P*(P+5) +
    spatialSamplingBudget P + 2*P + 4

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedModularCanonicalDetectorPeriodBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_preparedModularCanonicalDetector_period_budget (m dim Cgrid : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {nX : ℕ} {A : Type*} [Fintype A]
      (n : Fin m → ℕ) (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
      {P Pk Qstride p : ℝ}, 0 ≤ P → (nX : ℝ) ≤ P → Pk ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P →
      (Fintype.card A : ℝ) ≤ P → (∀ j, (n j : ℝ) ≤ P) →
      (∀ j, (Fintype.card (Q j) : ℝ) ≤ P) →
      let O := fun j : Fin m => (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)
      let budget := (P + C) ^ C
      let L := ((m + 1 : ℕ) : ℝ) * Pk
      let qlog := L + nX * Qstride
      let maskLog := (Fintype.card A : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
        ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)
      let labelLog := (∑ j, (n j : ℝ) * L) + ∑ j, (Fintype.card (Q j) : ℝ) * L
      P ≤ budget ∧ L ∈ Set.Icc 0 budget ∧ qlog ∈ Set.Icc 0 budget ∧
      (p + 1) ∈ Set.Icc 0 budget ∧ maskLog ∈ Set.Icc 0 budget ∧
      labelLog ∈ Set.Icc 0 budget ∧
      ((dim : ℝ) + qlog + (p + 1) + 1) ∈ Set.Icc 0 budget ∧
      ((Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (p + 1) + 4) ∈ Set.Icc 0 budget ∧
      ∀ {M period : ℕ} [NeZero period],
        (M : ℝ) ≤ Real.exp Pk → period ≤ M ^ (m + 1) →
        (period : ℝ) ≤ Real.exp budget ∧
        (layerKernelIndexBound m M : ℝ) ^ Fintype.card A * coefficientDeckPeriodCap O Q period ≤
          Real.exp budget ∧
        (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤
          Real.exp budget := by
  let rows : ℕ := ∑ j : Fin m, Fintype.card
    (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)
  let X : Polynomial ℕ := Polynomial.X
  let Lp := Polynomial.C (m + 1) * X
  let Qp := Lp + X * X
  let Mp := X * (Polynomial.C (m * 2 ^ (m + 1)) * X) + X * (Polynomial.C rows * Lp)
  let labelp := Polynomial.C (2 * m) * X * Lp
  let tp := Polynomial.C dim + Qp + (X + 1) + 1
  let gp := Polynomial.C Cgrid + Polynomial.C (dim + 1) * Qp + (X + 1) + 4
  let poly := X + Lp + Mp + labelp + tp + gp
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro nX A _ n Q _ P Pk Qstride p hP hnX hPk hQstride hp hA hn hQ O budget L qlog maskLog labelLog
  have hPk0 : 0 ≤ Pk := hPk.1
  have hp0 : 0 ≤ p := hp.1
  let Lb := ((m + 1 : ℕ) : ℝ) * P
  let Qb := Lb + P * P
  let Mb := P * ((m * 2 ^ (m + 1) : ℕ) * P) + P * (rows * Lb)
  let labelb := (2 * m : ℕ) * P * Lb
  let tb := (dim : ℝ) + Qb + (P + 1) + 1
  let gb := (Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * Qb + (P + 1) + 4
  have hLb : 0 ≤ Lb := by dsimp only [Lb]; positivity
  have hQb : 0 ≤ Qb := by dsimp only [Qb]; positivity
  have hMb : 0 ≤ Mb := by dsimp only [Mb]; positivity
  have hlb : 0 ≤ labelb := by dsimp only [labelb]; positivity
  have htb : 0 ≤ tb := by dsimp only [tb]; positivity
  have hgb : 0 ≤ gb := by dsimp only [gb]; positivity
  have htotal : P + Lb + Mb + labelb + tb + gb ≤ budget := by
    simpa [poly, X, Lp, Qp, Mp, labelp, tp, gp, Lb, Qb, Mb, labelb, tb, gb,
      Polynomial.eval₂_pow] using hbound P hP
  have hL : L ≤ Lb := mul_le_mul_of_nonneg_left hPk.2 (Nat.cast_nonneg _)
  have hL0 : 0 ≤ L := mul_nonneg (Nat.cast_nonneg _) hPk.1
  have hqlog : qlog ≤ Qb := add_le_add hL
    (mul_le_mul hnX hQstride.2 hQstride.1 hP)
  have hqlog0 : 0 ≤ qlog := add_nonneg hL0 (mul_nonneg (Nat.cast_nonneg _) hQstride.1)
  have hsum : (∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)) ≤ P * (rows * Lb) := by
    calc
      _ ≤ ∑ j : Fin m, P * (Fintype.card (O j) * Lb) := by
        apply Finset.sum_le_sum
        intro j _
        gcongr
        exact hQ j
      _ = _ := by
        simp only [O, rows, Nat.cast_sum]
        rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hmask : maskLog ≤ Mb := by
    apply add_le_add _ hsum
    gcongr
    exact hPk.2
  have hlabel : labelLog ≤ labelb := by
    calc
      _ ≤ (∑ _j : Fin m, P * Lb) + ∑ _j : Fin m, P * Lb := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro j _
          gcongr
          exact hn j
        · apply Finset.sum_le_sum
          intro j _
          gcongr
          exact hQ j
      _ = _ := by simp only [labelb, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]; ring
  have ht : (dim : ℝ) + qlog + (p + 1) + 1 ≤ tb := by
    dsimp only [tb]
    gcongr
    exact hp.2
  have hg : (Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (p + 1) + 4 ≤ gb := by
    dsimp only [gb]
    gcongr
    exact hp.2
  have hLbudget : L ≤ budget := by linarith
  have hmaskbudget : maskLog ≤ budget := by linarith
  have hlabelbudget : labelLog ≤ budget := by linarith
  refine ⟨by linarith, ⟨hL0, hLbudget⟩,
    ⟨hqlog0, ?_⟩, ⟨by positivity, ?_⟩,
    ⟨by dsimp only [maskLog]; positivity, hmaskbudget⟩,
    ⟨by dsimp only [labelLog]; positivity, hlabelbudget⟩,
    ⟨by positivity, by linarith⟩, ⟨by positivity, by linarith⟩, ?_⟩
  · dsimp only [tb] at htotal htb
    linarith [Nat.cast_nonneg (α := ℝ) dim]
  · dsimp only [tb] at htotal htb
    linarith [Nat.cast_nonneg (α := ℝ) dim, hp.2]
  · intro M period _ hM hperiod
    obtain ⟨hperiodBound, hmaskBound, hlabelBound⟩ :=
      canonicalPeriod_primitive_bounds A n O Q hM hperiod
    exact ⟨hperiodBound.trans (Real.exp_le_exp.mpr hLbudget),
      hmaskBound.trans (Real.exp_le_exp.mpr hmaskbudget),
      hlabelBound.trans (Real.exp_le_exp.mpr hlabelbudget)⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedModularGeneralNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_canonicalSlicedNative_input_budget (m dim Amass Aanalytic : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {P D p v F Prho Pk target Banalytic pGeometry Ecoarse gain : ℝ} {nX : ℕ},
      0 ≤ P → D ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P → v ∈ Set.Icc 0 P →
      F ∈ Set.Icc 0 P → Prho ∈ Set.Icc 0 P → Pk ∈ Set.Icc 0 P →
      target ∈ Set.Icc 0 P → Banalytic ∈ Set.Icc 0 P →
      pGeometry ∈ Set.Icc 0 P → Ecoarse ∈ Set.Icc 0 P →
      gain ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Emodel := (D + p + v + F + Prho + Pk + target + Amass) ^ Amass
      let analytic := (D + p + v + F + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic
      let Espatial := coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim (pGeometry + Ecoarse))
      let volumeLog := allocatedAmbientNormalizationLog dim (nX : ℝ) pGeometry pGeometry pGeometry
      let Pvolume := (nX : ℝ) + volumeLog
      let budget := (P + C) ^ C
      P ≤ budget ∧ Emodel ∈ Set.Icc 0 budget ∧ analytic ∈ Set.Icc 0 budget ∧
        Espatial ∈ Set.Icc 0 budget ∧ Pvolume ∈ Set.Icc 0 budget ∧
        volumeLog ≤ Pvolume ∧ (nX : ℝ) ≤ gain + 8 + Emodel + Espatial + Pvolume := by
  obtain ⟨Aspatial, _, hspatial⟩ := exists_allocatedEarlyCoarseLog_bound m dim
  let X : Polynomial ℕ := Polynomial.X
  let massPoly := (7 * X + Polynomial.C Amass) ^ Amass
  let analyticPoly := (8 * X + Polynomial.C Aanalytic) ^ Aanalytic
  let spatialPoly := (2 * X + Polynomial.C Aspatial) ^ Aspatial
  let volumePoly := X + allocatedAmbientNormalizationLog dim X X X X
  obtain ⟨C, hC, hbound⟩ :=
    exists_natPolynomial_eval_budget (X + massPoly + analyticPoly + spatialPoly + volumePoly)
  refine ⟨C, hC, ?_⟩
  intro P D p v F Prho Pk target Banalytic pGeometry Ecoarse gain nX hP hD hp hv hF hPrho hPk
    htarget hBanalytic hGeometry hEcoarse hgain hnX Emodel analytic Espatial volumeLog Pvolume budget
  let massBound := (7 * P + Amass) ^ Amass
  let analyticBound := (8 * P + Aanalytic) ^ Aanalytic
  let spatialBound := (2 * P + Aspatial) ^ Aspatial
  let volumeBound := P + allocatedAmbientNormalizationLog dim P P P P
  have hsum : P + massBound + analyticBound + spatialBound + volumeBound ≤ budget := by
    simpa [X, massPoly, analyticPoly, spatialPoly, volumePoly, massBound, analyticBound,
      spatialBound, volumeBound, allocatedAmbientNormalizationLog, Polynomial.eval₂_pow] using hbound P hP
  have hD0 : 0 ≤ D := hD.1
  have hp0 : 0 ≤ p := hp.1
  have hv0 : 0 ≤ v := hv.1
  have hF0 : 0 ≤ F := hF.1
  have hPrho0 : 0 ≤ Prho := hPrho.1
  have hPk0 : 0 ≤ Pk := hPk.1
  have htarget0 : 0 ≤ target := htarget.1
  have hBanalytic0 : 0 ≤ Banalytic := hBanalytic.1
  have hGeometry0 : 0 ≤ pGeometry := hGeometry.1
  have hEcoarse0 : 0 ≤ Ecoarse := hEcoarse.1
  have hmass0 : 0 ≤ Emodel := by dsimp [Emodel]; positivity
  have hanalytic0 : 0 ≤ analytic := by dsimp [analytic]; positivity
  have hspatial0 : 0 ≤ Espatial :=
    (coarseSpatialLogs_nonneg (allocatedEarlyCoarseInput_bounds m dim
      (add_nonneg hGeometry.1 hEcoarse.1)).1).2
  have hvolume0 : 0 ≤ volumeLog := by
    dsimp [volumeLog, allocatedAmbientNormalizationLog]
    positivity
  have hPvolume0 : 0 ≤ Pvolume := add_nonneg (Nat.cast_nonneg _) hvolume0
  have hm : Emodel ≤ massBound := by
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hD.2, hp.2, hv.2, hF.2, hPrho.2, hPk.2, htarget.2]
  have ha : analytic ≤ analyticBound := by
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hD.2, hp.2, hv.2, hF.2, hPrho.2, hPk.2, htarget.2, hBanalytic.2]
  have hs : Espatial ≤ spatialBound := by
    apply (hspatial (add_nonneg hGeometry.1 hEcoarse.1)).2.trans
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hGeometry.2, hEcoarse.2]
  have hvb : Pvolume ≤ volumeBound := by
    dsimp only [Pvolume, volumeLog, volumeBound, allocatedAmbientNormalizationLog]
    gcongr <;> first | assumption | exact hGeometry.2
  have hm0 : 0 ≤ massBound := by dsimp [massBound]; positivity
  have ha0 : 0 ≤ analyticBound := by dsimp [analyticBound]; positivity
  have hs0 : 0 ≤ spatialBound := by dsimp [spatialBound]; positivity
  have hv0 : 0 ≤ volumeBound := by
    dsimp [volumeBound, allocatedAmbientNormalizationLog]
    positivity
  refine ⟨?_, ⟨hmass0, ?_⟩, ⟨hanalytic0, ?_⟩, ⟨hspatial0, ?_⟩,
    ⟨hPvolume0, ?_⟩, ?_, ?_⟩
  · linarith only [hsum, hm0, ha0, hs0, hv0]
  · linarith only [hsum, hm, hP, ha0, hs0, hv0]
  · linarith only [hsum, ha, hP, hm0, hs0, hv0]
  · linarith only [hsum, hs, hP, hm0, ha0, hv0]
  · linarith only [hsum, hvb, hP, hm0, ha0, hs0]
  · exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  · dsimp only [Pvolume]
    linarith only [hgain.1, hmass0, hspatial0, hvolume0]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CubeMixtureVertex
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_large_vertex_of_cube_mixture
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]
    {φ : A →+ B} {Q : Finset A} (hφ : ReflectsPairSums φ (Q : Set A))
    (s : ℕ) {I : Type*} [Fintype I] (p : ℝ)
    (c : I → ℂ) (F : I → (Fin (s + 1) → Bool) → A → ℂ)
    (hF : ∀ i ω x, x ∈ Q → ‖F i ω x‖ ≤ 1)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp p)
    (z : ℂ) (hz : Real.exp (-p) ≤ z.re)
    (herr : ‖z - ∑ i, c i * normalizedSupportedCubeSum (s + 1) Q (F i)‖ ≤ Real.exp (-p) / 2)
    (ω : Fin (s + 1) → Bool) :
    ∃ i, Real.exp (-(2 * p + 2)) ≤ finiteSupportGowersNorm (s + 1) Q (F i ω) := by
  have hlarge : Real.exp (-p) / 2 ≤
      ‖∑ i, c i * normalizedSupportedCubeSum (s + 1) Q (F i)‖ := by
    have h := norm_sub_norm_le z (∑ i, c i * normalizedSupportedCubeSum (s + 1) Q (F i))
    have hreal := Complex.re_le_norm z
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term c
    (fun i => normalizedSupportedCubeSum (s + 1) Q (F i))
    (half_pos (Real.exp_pos _)) (Real.exp_pos p) hc hlarge
  have he : Real.exp (-(2 * p)) / 2 = (Real.exp (-p) / 2) / Real.exp p := by
    rw [div_right_comm, ← Real.exp_sub]
    congr 2
    ring
  have hsmall : Real.exp (-(2 * p + 2)) ≤ Real.exp (-(2 * p)) / 2 :=
    (Real.exp_le_exp.mpr (by linarith : -(2 * p + 2) ≤ -(2 * p) - 1)).trans
      (exp_sub_one_le_half_exp (-(2 * p)))
  rw [he] at hsmall
  exact ⟨i, (hsmall.trans hi).trans (normalizedSupportedCubeSum_le_vertex hφ s (F i) (hF i) ω)⟩

theorem exists_site_twist_of_degree_zero_cube_mixture
    {X : Type*} [Fintype X] [DecidableEq X] (N : X → ℕ) [∀ x, NeZero (N x)]
    {I : Type*} [Fintype I] (p : ℝ) (f : (X → ℤ) → ℂ) (c : I → ℂ)
    (twist : I → Finset (Fin 1) → (X → ℤ) → ℂ)
    (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1)
    (ht : ∀ i ω x, x ∈ integerBox N → ‖twist i ω x‖ ≤ 1)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp p) (z : ℂ) (hz : Real.exp (-p) ≤ z.re)
    (herr : ‖z - ∑ i, c i *
      (𝔼 cube : SupportedCube 1 (integerBox N : Set (X → ℤ)),
        let u := (BooleanCubeKernel.physicalCubeParametersEquiv X 1).symm cube.val
        ∏ ω, conjugationPower ω.card (f (BooleanCubeKernel.physicalCubeVertexValue u ω)) *
          twist i ω (BooleanCubeKernel.physicalCubeVertexValue u ω))‖ ≤ Real.exp (-p) / 2) :
    ∃ i, Real.exp (-(2 * p + 2)) ≤ ‖𝔼 x ∈ integerBox N, f x * twist i ∅ x‖ := by
  let F : I → (Fin 1 → Bool) → (X → ℤ) → ℂ := fun i ω x =>
    f x * conjugationPower (booleanWeight ω)
      (twist i (BooleanCubeKernel.vertexFinsetEquiv 1 ω) x)
  have hF : ∀ i ω x, x ∈ integerBox N → ‖F i ω x‖ ≤ 1 := by
    intro i ω x hx
    dsimp only [F]
    rw [norm_mul, conjugationPower_norm]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x hx)).trans (ht i _ x hx)
  simp_rw [BooleanCubeKernel.physical_twisted_cube_mean] at herr
  obtain ⟨i, hi⟩ := exists_large_vertex_of_cube_mixture (boxReduction_reflectsPairSums N)
    0 p c F hF hc z hz herr (fun _ => false)
  rw [finiteSupportGowersNorm_degree_one_of_embedding
    (boxReduction_reflectsPairSums N) (integerBox_nonempty N)] at hi
  refine ⟨i, ?_⟩
  simpa only [F, booleanWeight, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero,
    conjugationPower, RingHom.id_apply, BooleanCubeKernel.vertexFinsetEquiv,
    Equiv.coe_fn_mk, Finset.filter_false] using hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def preparedSamplerBlockCount (m dim : ℕ) (j : Fin m) : ℕ :=
  let rows := boundedBooleanJetRows (Fin dim) (j.val + 1)
  1 + Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1)) +
    max (positiveModerateSpectrumBlockCount j.val rows.card ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount j.val rows.card ((j.val + 1) * rows.card))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def preparedCommonBlockCount (m : ℕ) (j : Fin m) : ℕ :=
  ∑ s : Fin (m + 1), preparedSamplerBlockCount m (s.val + 1) j

variable {X J : Type}
  {m : ℕ}

noncomputable def preparedCommonSamplerDimension (m M : ℕ) : ℕ :=
  (m + 1) * (m + 3) + M * m * (∑ j, preparedCommonBlockCount m j) + M + m + 2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def enlargedPreparedCommonSamplerDimension (m M Jalloc : ℕ) : ℕ :=
  (m + 1) * (m + 3) + (m + 1) * Jalloc +
    M * m * (∑ j : Fin m, (preparedCommonBlockCount m j + Jalloc)) + M + m + Jalloc + 2

theorem enlargedPreparedCommonSamplerDimension_polynomial (m M Jalloc : ℕ) :
    enlargedPreparedCommonSamplerDimension m M Jalloc =
      preparedCommonSamplerDimension m M + (m + 2 + M * m * m) * Jalloc := by
  simp only [enlargedPreparedCommonSamplerDimension, preparedCommonSamplerDimension,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id]
  ring

theorem enlargedPreparedCommonSamplerDimension_ge (m M Jalloc : ℕ) :
    M ≤ enlargedPreparedCommonSamplerDimension m M Jalloc := by
  unfold enlargedPreparedCommonSamplerDimension
  omega

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ShiftedSmoothFiniteGridLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem rectangularWeightIndices_normalized_bound {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i)
    (k : rectangularWeightIndices a S 1) (i : I) :
    |rectangularLatticePoint a S k.val i| ≤ 1 := by
  have hi := Fintype.mem_piFinset.mp k.property i
  have h := sampledWeightIndices_mem_bound hi
  change |((k.val i : ℝ) - a i) / S i| ≤ 1
  rw [abs_div, abs_of_pos (hS i), div_le_one (hS i)]
  simpa only [mul_one] using h

theorem shiftedSmoothProductFiniteWeights_mean_eq_tsum {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (I → ℤ) → ℝ) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).mean (fun k => f k.val) =
      ∑' k, (shiftedSmoothProductPMF a S hS hZ k).toReal * f k := by
  change (∑ k : rectangularWeightIndices a S 1,
    (shiftedSmoothProductPMF a S hS hZ k.val).toReal * f k.val) = _
  rw [Finset.sum_coe_sort (rectangularWeightIndices a S 1)
    (fun k => (shiftedSmoothProductPMF a S hS hZ k).toReal * f k)]
  exact (hasSum_sum_of_ne_finset_zero (fun k hk => by
    rw [shiftedSmoothProductPMF_toReal_zero_off a S hS hZ k hk, zero_mul])).tsum_eq.symm

theorem shiftedSmoothProductFiniteWeights_event_eq_map {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (event : (I → ℤ) → Prop) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).eventProbability (fun k => event k.val) =
      ((shiftedSmoothProductPMF a S hS hZ).map (fun k => decide (event k)) true).toReal := by
  rw [FiniteProbabilityWeights.eventProbability,
    shiftedSmoothProductFiniteWeights_mean_eq_tsum a S hS hZ
      (fun k => if event k then 1 else 0), pmf_map_toReal_indicator]
  apply tsum_congr
  intro k
  simp only [decide_eq_true_eq]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedSameScaleBadProductBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedModularCanonicalDetectorAllocationBudget (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {P : ℝ} {M nX : ℕ},
      0 ≤ P → (M : ℝ) ≤ P → (nX : ℝ) ≤ P →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let budget := (P + A) ^ A
      P ≤ budget ∧ (Jalloc : ℝ) ∈ Set.Icc 0 budget ∧ pnum ∈ Set.Icc 0 budget ∧
        pnum + Jalloc + nX + M + 1 ≤ budget := by
  let c := 2 ^ m * (2 ^ (2 * m) * m.factorial + 1) + 1
  let blocks := ∑ j : Fin m, preparedCommonBlockCount m j
  let X : Polynomial ℕ := Polynomial.X
  let allocation : Polynomial ℕ := Polynomial.C c * (Polynomial.C (m + 1) * X + 11)
  let base : Polynomial ℕ := Polynomial.C ((m + 1) * (m + 3)) +
    X * Polynomial.C m * Polynomial.C blocks + X + Polynomial.C m + 2
  let dimension := base + (Polynomial.C (m + 2) + X * Polynomial.C m * Polynomial.C m) * allocation
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget (dimension + allocation + 3 * X + 1)
  refine ⟨A, hA, ?_⟩
  intro P M nX hP hM hnX Jalloc pnum budget
  let allocBound : ℝ := c * (((m : ℝ) + 1) * P + 11)
  let baseBound : ℝ := ((m : ℝ) + 1) * (m + 3) + P * m * blocks + P + m + 2
  let dimBound : ℝ := baseBound + ((m : ℝ) + 2 + P * m * m) * allocBound
  have halloc0 : 0 ≤ allocBound := by dsimp only [allocBound]; positivity
  have hbase0 : 0 ≤ baseBound := by dsimp only [baseBound]; positivity
  have hdim0 : 0 ≤ dimBound := by dsimp only [dimBound]; positivity
  have halloc : (Jalloc : ℝ) ≤ allocBound := by
    have hlinear := Nat.cast_le (α := ℝ).mpr (modularInitialBlockCount_linear_bound m (nX + m * M))
    change (Jalloc : ℝ) ≤ (c * (nX + m * M + 11) : ℕ) at hlinear
    push_cast at hlinear
    apply hlinear.trans
    dsimp only [allocBound]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg c)
    have hmM := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg m)
    nlinarith
  have hbase : (preparedCommonSamplerDimension m M : ℝ) ≤ baseBound := by
    simp only [preparedCommonSamplerDimension, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
    dsimp only [baseBound, blocks]
    gcongr
  have hdim : pnum ≤ dimBound := by
    dsimp only [pnum]
    rw [enlargedPreparedCommonSamplerDimension_polynomial]
    push_cast
    dsimp only [dimBound]
    apply add_le_add hbase
    exact mul_le_mul (by gcongr) halloc (Nat.cast_nonneg _) (by positivity)
  have hsum : dimBound + allocBound + 3 * P + 1 ≤ budget := by
    simpa [dimension, allocation, base, X, dimBound, allocBound, baseBound,
      Nat.cast_add, Nat.cast_mul] using hbound P hP
  have hallocNonneg : (0 : ℝ) ≤ Jalloc := Nat.cast_nonneg _
  have hnumNonneg : 0 ≤ pnum := Nat.cast_nonneg _
  refine ⟨?_, ⟨hallocNonneg, ?_⟩, ⟨hnumNonneg, ?_⟩, ?_⟩
  all_goals linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedBadProductSourceBudget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {B P0 E V : ℝ} {M nX : ℕ},
      0 ≤ B → (M : ℝ) ≤ B → (nX : ℝ) ≤ B →
      P0 ∈ Set.Icc 0 B → E ∈ Set.Icc 0 B → V ∈ Set.Icc 0 B →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum := enlargedPreparedCommonSamplerDimension m M Jalloc
      let ncoeff := (m + 1) * (pnum + 1) ^ m
      let P := (B + C) ^ C
      B ≤ P ∧ P0 ≤ P ∧ (ncoeff : ℝ) + pnum ≤ P ∧
        allocatedWitnessScaleLog P0 (2 * P0 + 2 * V + 5 * E + 24) ≤ P ∧
        V + 3 * E + 16 ≤ P ∧ ((pnum + 1) * nX : ℕ) ≤ P := by
  obtain ⟨A, _, halloc⟩ := exists_preparedModularCanonicalDetectorAllocationBudget m
  let X : Polynomial ℕ := Polynomial.X
  let dim : Polynomial ℕ := (X + Polynomial.C A) ^ A
  let coeff : Polynomial ℕ := Polynomial.C (m + 1) * (dim + 1) ^ m
  let scale : Polynomial ℕ := (1 + X ^ 2) * (5 * X + 49) + X ^ 2 * (9 * X + 24)
  let total := X + coeff + dim + scale + (4 * X + 16) + (dim + 1) * X
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget total
  refine ⟨C, hC, ?_⟩
  intro B P0 E V M nX hB hM hnX hP0 hE hV Jalloc pnum ncoeff P
  have hP0lo := hP0.1
  have hP0hi := hP0.2
  have hElo := hE.1
  have hEhi := hE.2
  have hVlo := hV.1
  have hVhi := hV.2
  let dimBound : ℝ := (B + A) ^ A
  let coeffBound : ℝ := (m + 1 : ℕ) * (dimBound + 1) ^ m
  let scaleBound : ℝ := (1 + B ^ 2) * (5 * B + 49) + B ^ 2 * (9 * B + 24)
  have hdim0 : 0 ≤ dimBound := by dsimp only [dimBound]; positivity
  have hcoeff0 : 0 ≤ coeffBound := by dsimp only [coeffBound]; positivity
  have hscale0 : 0 ≤ scaleBound := by dsimp only [scaleBound]; positivity
  have hframe0 : 0 ≤ (dimBound + 1) * B := by positivity
  obtain ⟨_, _, hnum, _⟩ := halloc hB hM hnX
  have hnumBound : (pnum : ℝ) ≤ dimBound := hnum.2
  have hcoeff : (ncoeff : ℝ) ≤ coeffBound := by
    dsimp only [ncoeff, coeffBound]
    push_cast
    gcongr
  have hframe : (((pnum + 1) * nX : ℕ) : ℝ) ≤ (dimBound + 1) * B := by
    push_cast
    gcongr
  have hscale : allocatedWitnessScaleLog P0 (2 * P0 + 2 * V + 5 * E + 24) ≤ scaleBound := by
    unfold allocatedWitnessScaleLog allocatedScaleLog
    dsimp only [scaleBound]
    gcongr; linarith
  have htotal : B + coeffBound + dimBound + scaleBound + (4 * B + 16) +
      (dimBound + 1) * B ≤ P := by
    simpa [total, X, coeff, dim, scale, coeffBound, dimBound, scaleBound, P,
      Nat.cast_add, Polynomial.eval₂_pow] using hbound B hB
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

end Erdos3.VectorPolynomial

end

end OAI
end


