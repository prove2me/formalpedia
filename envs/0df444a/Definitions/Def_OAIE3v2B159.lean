-- Prove2me | Definitions.Def_OAIE3v2B159
-- name    : OAIE3v2B159
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:33:17.905228+00:00
-- url     : https://prove2.me/theorems/f2012b40-79f5-41c6-8845-610a84d38d4a
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 161 of 311
-- statement:
--   Definitions bundle 161 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B140`, `OAIE3v2B141`, `OAIE3v2B142`, `OAIE3v2B143`, `OAIE3v2B144`, `OAIE3v2B145`, `OAIE3v2B147`, `OAIE3v2B148`, `OAIE3v2B149`, `OAIE3v2B150` of this split.
--
--   Modules: `Dynamics/PreparedFiniteStageNativeBudget.lean`, `Estimates/AllocatedCandidateCommonFastGeometry.lean`, `Estimates/AllocatedExternalCandidateOptionJointConclusion.lean`, `Estimates/CenteredFiniteSliceResidualEnvelope.lean`, `Estimates/FullTaggedRationalRetraction.lean`, `Estimates/MarginalTailModeling.lean`, `Estimates/NativeMarkedFreezingPhysicalData.lean`, `Estimates/NativeModelOrbit.lean`, `Estimates/OptionComplementCover.lean`, `Estimates/OptionMarkedSurjective.lean`, `Estimates/PreparedFiniteForwardFixedCenterThreshold.lean`, `Estimates/PreparedFiniteForwardTreeStorage.lean`, `Estimates/PreparedUniformEarlyRadiusWithCutoff.lean`, `Estimates/RealifiedTopQuotient.lean`, `Estimates/SiteTwistCommonModulus.lean`, `Estimates/UnconditionedTrimmedSliceFamily.lean`, `Fourier/BohrNiltestBudget.lean`, `Fourier/JoinedFrequencyQuotientInjectivity.lean`, `Geometry/CommonRationalModelCoordinates.lean`, `Geometry/NativeProductOrbitMetric.lean`, `Geometry/ProductComponentCoordinates.lean`, `Lattices/AffineCoefficientCoverTilt.lean`, `Lattices/AffineCoefficientResidueWidths.lean`, `Lattices/ConcreteAffineMeshBoundary.lean`, `Lattices/RelativeSliceAffineThreeFactorLaw.lean`, `Lattices/ResidueBoxSliceCoordinateDisintegration.lean`, `Lattices/ResidueBoxSliceSubtypeSites.lean`, `Lattices/RetainedAffineCommonCover.lean`, `Lattices/UniformExternalMarkedAffineSliceFreezingDictionary.lean`, `Linear/KernelPrincipalFiberSliceLaw.lean`, `Linear/KernelProjectionPresentPivotIdeal.lean`, `Linear/RationalTagProjectionComplement.lean`, `Linear/TripleProductBasisBounds.lean`, `Nilpotent/CyclicNiltestApproximation.lean`, `Nilpotent/NiltestVerticalBounds.lean`, `Nilpotent/PolynomialShearNilmanifold.lean`, `Polynomial/ForecastSlicedEarlyUnrestrictedPolynomialBudget.lean`, `Polynomial/MajorTranslationDegreeSymbol.lean`, `Polynomial/OrdinaryPolynomialPhaseCanonicalTopology.lean`, `Polynomial/PreparedFiniteForwardPolynomialCap.lean`, `Polynomial/QuantitativeOuterPolynomialProducts.lean`, `Polynomial/VectorPolynomialSliceInterpolation.lean`, `Sampling/AllocatedProbabilityGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B140
import Definitions.Def_OAIE3v2B141
import Definitions.Def_OAIE3v2B142
import Definitions.Def_OAIE3v2B143
import Definitions.Def_OAIE3v2B144
import Definitions.Def_OAIE3v2B145
import Definitions.Def_OAIE3v2B147
import Definitions.Def_OAIE3v2B148
import Definitions.Def_OAIE3v2B149
import Definitions.Def_OAIE3v2B150

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialShearNilmanifold
namespace OAI

section

namespace Erdos3

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]

theorem polynomialShearNilmanifold_complexity (s : ℕ) (hpos : ∀ i, 0 < w i)
    (hw : ∀ i, w i ≤ s) {p : ℝ} (hp : 0 ≤ p)
    (hd : (Fintype.card (PolynomialShearIndex w) : ℝ) ≤ p)
    (hf : (s.factorial : ℝ) ≤ Real.exp p)
    (hH : ((2 * s + 1 : ℕ) : ℝ) ≤ Real.exp p) :
    (polynomialShearNilmanifold w s hw).GeometryComplexityLE p := by
  refine ⟨hd, hf, ?_, ?_⟩
  · intro i j k
    exact rationalLogHeight_le_of_height (polynomialShearOrderedBasis_structure_height w s hpos hw i j k) hH
  · intro i j k
    exact rationalLogHeight_le_of_height (polynomialShearLayerFinBasis_height w (i.val + 1) j k)
      (by simpa using Real.one_le_exp_iff.mpr hp)

theorem polynomialShearNilmanifold_complexity_budget (s : ℕ) (hpos : ∀ i, 0 < w i)
    (hw : ∀ i, w i ≤ s) :
    (polynomialShearNilmanifold w s hw).GeometryComplexityLE
      ((Fintype.card (PolynomialShearIndex w) + s.factorial + 2 * s + 1 : ℕ) : ℝ) := by
  let n := Fintype.card (PolynomialShearIndex w) + s.factorial + 2 * s + 1
  have hn : (Fintype.card (PolynomialShearIndex w) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show Fintype.card (PolynomialShearIndex w) ≤ n by dsimp [n]; omega)
  have hf : (s.factorial : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show s.factorial ≤ n by dsimp [n]; omega)
  have hH : ((2 * s + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 2 * s + 1 ≤ n by dsimp [n]; omega)
  have he : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  exact polynomialShearNilmanifold_complexity w s hpos hw (Nat.cast_nonneg n) hn
    (hf.trans he) (hH.trans he)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientResidueWidths
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem affine_coefficient_mode_residue_removal_lipschitz_amplitude {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) {C : ℝ}
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R : ℝ} (hζ : 0 < ζ) (hN : ∀ i : Fin m, ∀ k, multiaffineBiasBudget i.val ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hrowBudget : ∀ i : Fin m, ((i.val + 1).factorial : ℝ) * C ≤ R)
    (hdenom : ∀ i : Fin m, (∏ j : Fin (i.val + 1) → I,
      (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤ R)
    (hcoeff : ∀ i : Fin m, (Fintype.card I : ℝ) ^ (i.val + 1) *
      (A ^ (i.val + 1) * multiaffineBiasBudget i.val ζ) ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth stride V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / residueProfileWidth stride V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option K × I) *
      ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {r β : ℝ} (hr : 0 ≤ r)
    (hmove : ∀ i : Fin m, ∀ z,
      ((i.val + 1 : ℕ) : ℝ) * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1)))
    (F : (Option K × I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (hLip : LipschitzWith Lip F) :
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      (F (fun t => (residueLatticeArray residue stride z t : ℝ) / V t) *
        layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ)))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + (Lip : ℝ) * r + β := by
  obtain ⟨i, rows, hrows, hlocal⟩ := exists_affine_coefficient_local_removal
    U frequency hbound hbad p hp hm N stride hs hζ hN
    H hH hA hscale hrank hrowBudget hdenom hcoeff hβ hpower
  have hNp k : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos i.val hζ).trans_le (hN i k)
  exact residue_smooth_row_shift_transfer_lipschitz_amplitude N stride hNp hs rows residue V hV hZ hV1
    hδ hδ1 hmesh hsmall zero_le_one hrows hr (by simpa only [mul_one] using hmove i)
    _ (fun b => (layeredCoefficientCharacter_norm _ p b).le) hlocal F hF hLip

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem affine_coefficient_residue_removal_of_widths_lipschitz_amplitude {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R T S : ℝ} (hζ : 0 < ζ) (hT : 0 < T) (hS : 0 ≤ S)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (hH : ∀ k, 0 < H k)
    (hsize : ∀ k, (stride k : ℝ) * T * (finiteLayerBiasBudget m ζ + 1) ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : layerRemovalRankBudget m (Fintype.card I) C 1
      (finiteLayerBiasBudget m ζ) (2 * T) S ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth stride V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / residueProfileWidth stride V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option K × I) *
      ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {ρ r β : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (hmove : (m : ℝ) * 1 ≤ r * ρ * T)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1)))
    (F : (Option K × I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (hLip : LipschitzWith Lip F) :
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      (F (fun t => (residueLatticeArray residue stride z t : ℝ) / V t) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ)))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + (Lip : ℝ) * r + β := by
  classical
  let B := finiteLayerBiasBudget m ζ
  let D : ℝ := 1
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m hζ
  have hD : 0 ≤ D := zero_le_one
  have hA : 0 ≤ 2 * T := by positivity
  have hb (i : Fin m) : multiaffineBiasBudget i.val ζ ≤ B :=
    multiaffineBiasBudget_le_finite i hζ
  obtain ⟨N, hN, hscale, hshift⟩ := exists_mode_shift_lengths m hT hB hρ hr hmove H stride hs hsize V hwidth
  have hbud (i : Fin m) := layerRemovalRankBudget_bounds i (Fintype.card I) hC hD
    (zero_le_one.trans hB) hA hS
  apply affine_coefficient_mode_residue_removal_lipschitz_amplitude U frequency hbound hbad
    p hp hm N stride hs hζ (fun i k => (hb i).trans (hN k)) H hH hA hscale hrank
    (fun i => by simpa only [D, one_pow, mul_one] using (hbud i).1.trans hR) _ _ residue V hV hZ hV1 hδ hδ1 hmesh hsmall hr _ hβ hpower F hF hLip
  · intro i
    have hi := tensorDenominatorBound_le (H := Fin (i.val + 1))
      (multiaffineBiasBudget_pos i.val hζ).le (fun k => (stride k : ℝ))
      (fun k => Nat.cast_nonneg _) hstride
    have hi' : (∏ j : Fin (i.val + 1) → I,
        (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤
        (multiaffineBiasBudget i.val ζ * S ^ (i.val + 1)) ^ (Fintype.card I ^ (i.val + 1)) := by
      simpa only [Fintype.card_fin] using hi
    apply hi'.trans
    apply le_trans _ ((hbud i).2.1.trans hR)
    exact pow_le_pow_left₀
      (mul_nonneg (multiaffineBiasBudget_pos i.val hζ).le (pow_nonneg hS _))
      (mul_le_mul_of_nonneg_right (hb i) (pow_nonneg hS _)) _
  · intro i
    apply le_trans _ ((hbud i).2.2.trans hR)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hb i) (pow_nonneg hA _))
      (pow_nonneg (Nat.cast_nonneg _) _)
  · intro i z
    have hi : ((i.val + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    have hs' : (m : ℝ) * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z := by
      simpa only [mul_one] using hshift z
    exact (mul_le_mul_of_nonneg_right hi
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans hs'

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedAffineCommonCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem affine_coefficient_amplitude_residue_removal_at_error {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (F : (Option K × I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (hLip : LipschitzWith Lip F)
    (H : I → ℝ)
    (hsize : ∀ k, modeResidueSideThreshold m (Fintype.card (Option K × I))
      1 S ρ (modeAmplitudeAccuracy Lip ε) ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : modeRemovalRankThreshold m (Fintype.card I) (Fintype.card (Option K × I))
      C 1 S ρ (modeAmplitudeAccuracy Lip ε) ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      (F (fun t => (residueLatticeArray residue stride z t : ℝ) / V t) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ)))‖ ≤ ε := by
  classical
  let ε₀ := modeAmplitudeAccuracy (Lip : ℝ) ε
  have hε₀ : 0 < ε₀ := modeAmplitudeAccuracy_pos Lip.coe_nonneg hε
  let d := Fintype.card (Option K × I)
  let D : ℝ := 1
  let T := modeRemovalShrink m d D ρ ε₀
  let B := finiteLayerBiasBudget m (modeRemovalBias m ε₀)
  have hD : 0 ≤ D := zero_le_one
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (modeRemovalShrink_one_le m d hD hρ hε₀)
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε₀)
  have hside := modeRemovalSideThreshold_bounds m d hD hS hρ hε₀
  have hsizeBase k : modeRemovalSideThreshold m d D S ρ ε₀ ≤ H k :=
    (modeResidueSideThreshold_bounds m d hD hS hρ hε₀).1.trans (hsize k)
  have hH k : 0 < H k := hside.1.trans_le (hsizeBase k)
  have hsize' k : (stride k : ℝ) * T * (B + 1) ≤ H k := by
    calc
      _ ≤ S * T * (B + 1) := by gcongr; exact hstride k
      _ ≤ H k := hside.2.1.trans (hsizeBase k)
  have hv z : 1 ≤ residueProfileWidth stride V z ∧
      1 / residueProfileWidth stride V z ≤ modeRemovalMesh d :=
    modeResidueWidth_mesh m d hD hS hρ hε₀ (hs z.2) (hstride z.2) (hsize z.2) (hV z) (hwidth z)
  have hmass := shiftedSmoothProductMass_lower (residueProfileCenter residue stride)
    (residueProfileWidth stride V) (residueProfileWidth_pos stride V hs hV)
    (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d) (fun z => (hv z).2) (modeRemovalMesh_small d)
  have hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V) :=
    (div_pos (Finset.prod_pos (fun z _ => residueProfileWidth_pos stride V hs hV z)) (by norm_num)).trans_le hmass
  refine ⟨hZ, ?_⟩
  have hout := affine_coefficient_residue_removal_of_widths_lipschitz_amplitude U hC frequency hbound hbad
    p hp hm stride hs (modeRemovalBias_pos m hε₀) hT hS hstride H hH hsize' hrank hR
    residue V hV hZ (fun z => (hv z).1) (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d)
    (fun z => (hv z).2) (modeRemovalMesh_small d) hρ (modeRemovalRadius_pos d hε₀).le hwidth
    (modeRemovalShrink_move m d hρ hε₀) (modeRemovalBeta_pos hε₀).le (fun i => modeRemovalBias_le i hε₀) F hF hLip
  exact hout.trans (modeAmplitudeError_bound d Lip.coe_nonneg hε)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientCoverTilt
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_density_mass (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ) (_hD : Integrable D μ)
    (_hDmass : (∫ x, D x ∂μ) = 1)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    |selectedResidueDensityMass stride G V
      (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) - 1| ≤
      2 * η + ε := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_haar_approximation m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth D hD hDmass η hη happrox
  obtain ⟨hZ, he⟩ := hcomparison hP hn hd U μ hC hCP frequency hbound c hB hBP hcoefficients
    p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    (fun x => (D x : ℂ)) hD.ofReal hη happrox
  refine ⟨hZ, ?_⟩
  rw [integral_complex_ofReal, hDmass, Complex.ofReal_one] at he
  rw [← selectedResidueDensityMass_complex stride G V hV hZ
    (fun z => D (affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ)))),
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at he
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_cover_tilted_family_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (F : Bool → Type*) [∀ b, Fintype (F b)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ b, F b → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ b a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency b a j d t : ℝ)| ≤ C)
    (c : ∀ b, F b → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : ∀ b, (∑ a, ‖c b a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (cover : ℕ) (_hcover : 0 < cover) (_hcoverP : (cover : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ) (_hD : Integrable D μ)
    (_hDmass : (∫ x, D x ∂μ) = 1) (_hD0 : ∀ x, 0 ≤ D x)
    (f : CoefficientTorus (K := K) U → ℂ) (_hf : AEStronglyMeasurable f μ)
    (_hfbound : ∀ x, ‖f x‖ ≤ 1)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ b x,
      ‖(D x : ℂ) * (if b then f x else 1) - coefficientTorusFourierSum U (frequency b) (c b) x‖ ≤ η)
    (_hsmall : 2 * η + ε ≤ 1 / 2),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ∃ hDpos : 0 < selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ)))),
    |selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ)))) - 1| ≤ 2 * η + ε ∧
    (1 / 2 ≤ selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ))))) ∧
    (selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ)))) ≤ 3 / 2) ∧
    ‖(∑' z, ((selectedResidueDensityPMF stride G V hV hZ
        (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ))))
        (fun _z => _hD0 _) hDpos z).toReal : ℂ) *
          f (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, (D x : ℂ) * f x ∂μ)‖ ≤ 4 * (2 * η + ε) := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_cover_haar_approximation m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm cover hcover hcoverP stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    D hD hDmass hD0 f hf hfbound η hη happrox hsmall
  let sample (z : Option K × I → ℤ) := affineCoefficientCoverSample U p hm cover (fun k j => (z (k, j) : ℝ))
  obtain ⟨hZ, he0⟩ := hcomparison hP hn hd U μ hC hCP (frequency false) (hbound false)
    (c false) hB hBP (hcoefficients false) p hp hm cover hcover hcoverP stride hs hS hSP hρ hε hρP hεP hstride
    H hsize hrank hR G hG V hV hwidth (fun x => (D x : ℂ)) hD.ofReal hη
    (fun x => by simpa using happrox false x)
  have hmass : |selectedResidueDensityMass stride G V (fun z => D (sample z)) - 1| ≤ 2 * η + ε := by
    rw [integral_complex_ofReal, hDmass, Complex.ofReal_one] at he0
    rw [← selectedResidueDensityMass_complex stride G V hV hZ (fun z => D (sample z)),
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at he0
    exact he0
  have hlower : 1 / 2 ≤ selectedResidueDensityMass stride G V (fun z => D (sample z)) := by
    have := (abs_le.mp hmass).1
    linarith
  have hupper : selectedResidueDensityMass stride G V (fun z => D (sample z)) ≤ 3 / 2 := by
    have := (abs_le.mp hmass).2
    linarith
  have hDpos : 0 < selectedResidueDensityMass stride G V (fun z => D (sample z)) := by linarith
  refine ⟨hZ, hDpos, hmass, hlower, hupper, ?_⟩
  obtain ⟨hZ', he1⟩ := hcomparison hP hn hd U μ hC hCP (frequency true) (hbound true)
    (c true) hB hBP (hcoefficients true) p hp hm cover hcover hcoverP stride hs hS hSP hρ hε hρP hεP hstride
    H hsize hrank hR G hG V hV hwidth (fun x => (D x : ℂ) * f x)
    (density_mul_integrable μ D hD f hf hfbound) hη
    (fun x => by simpa using happrox true x)
  have he := selectedResidueDensityPMF_error stride G V hV hZ
    (fun z => D (sample z)) (fun z => hD0 _) hDpos (fun z => f (sample z))
    hlower he1 hmass (norm_density_integral_le_one μ D hD hD0 hDmass f hfbound)
  convert he using 1; ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarginalTailModeling
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_model_of_marginal_excess {Ω : Type*} [Fintype Ω]
    (p q : FiniteProbabilityWeights Ω) (hp : ∀ x, 0 < p.weight x)
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) (hSbound : ∀ Q ∈ S, ∀ x, ‖Q x‖ ≤ 1)
    {K C B beta tau ε : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * q.mean (fun x => ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K * (2*C) / tau) →
      tau / B ^ 2 ≤ X psi → ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (hexcess : p.excessMass q C ≤ ε)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (Ω → ℂ)) (c : Fin n → ℝ) (e : Ω → ℂ),
      (∀ i, Q i ∈ S) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      X e ≤ 2*tau + 2*K*(B + 2/beta)*ε ∧
      (n : ℝ) ≤ 1 + 4 * (K * (2*C)) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let G := Finset.univ.filter (fun x => p.relativeDensity q x ≤ 2*C)
  have htail : p.mean (fun x => if x ∈ G then 0 else p.relativeDensity q x) ≤ 2*ε := by
    rw [p.relativeDensity_tail_mass q hp]
    exact FiniteProbabilityWeights.mass_above_double_cap_le_of_excess p q hexcess
  have hbound (v : Ω → ℂ) : X v ≤ K * p.mean (fun x => p.relativeDensity q x * ‖v x‖) := by
    rw [p.mean_relativeDensity q hp]
    exact hX v
  obtain ⟨n, hn, Q, c, e, hQ, hdecomp, hc, he, hlen⟩ :=
    exists_model_with_tail_error p G X (p.relativeDensity q) hS hSn hSbound hK
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC) hB hbeta htau
      (p.relativeDensity_nonneg q) (fun x hx => (Finset.mem_filter.mp hx).2)
      hbound hdetect b hb
  refine ⟨n, hn, Q, c, e, hQ, hdecomp, hc, ?_, hlen⟩
  have hscale : 0 ≤ K*(B + 2/beta) := by positivity
  have hsmall := mul_le_mul_of_nonneg_left htail hscale
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CenteredFiniteSliceResidualEnvelope
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_sampled_slice_model {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    (r : FiniteProbabilityWeights X) (hr : ∀ x, 0 < r.weight x)
    {atoms : Set (X → ℂ)} (hbal : Balanced ℂ atoms) (hatoms : atoms.Nonempty)
    (hatomBound : ∀ Q ∈ atoms, ∀ x, ‖Q x‖ ≤ 1)
    {K C B beta tau ε : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1)
    (hdetect : ∀ psi : X → ℂ, (∀ x, ‖psi x‖ ≤ K * (2*C) / tau) →
      tau / B^2 ≤ sampledSliceSeminorm p F S w psi →
        ∃ Q ∈ atoms, beta ≤ ‖r.correlation psi Q‖)
    (hexcess : r.excessMass (p.siteLaw F) C ≤ ε)
    (b : X → ℂ) (hb : ∀ x, ‖b x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (X → ℂ)) (c : Fin n → ℝ) (e : X → ℂ),
      (∀ i, Q i ∈ atoms) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2/beta ∧
      sampledSliceSeminorm p F S w e ≤ 2*tau + 2*K*(B+2/beta)*ε ∧
      (n : ℝ) ≤ 1 + 4*(K*(2*C))^2/(beta^2*tau^2) :=
  exists_model_of_marginal_excess r (p.siteLaw F) hr (sampledSliceSeminorm p F S w)
    hbal hatoms hatomBound hK hC hB hbeta htau
    (sampledSliceSeminorm_le_siteLaw p F S w hsize hw) hdetect hexcess b hb

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable (μ : Measure C) [IsProbabilityMeasure μ]
variable (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ z, Measurable (fun c => (law c).weight z))

include hweight

theorem centeredFiniteMarginal_excessMass_le_of_ae (reference : FiniteProbabilityWeights Ω)
    (cap ε : ℝ) (h : ∀ᵐ c ∂μ, reference.excessMass (law c) cap ≤ ε) :
    reference.excessMass (centeredFiniteMarginal μ law hweight) cap ≤ ε := by
  apply (centeredFiniteMarginal_excessMass_le μ law hweight reference cap).trans
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono_ae (centeredFinite_excessMass_integrable μ law hweight reference cap)
      (integrable_const ε) h

theorem centeredFiniteMarginal_excessMass_le_of_uniform (reference : FiniteProbabilityWeights Ω)
    (cap ε : ℝ) (h : ∀ c, reference.excessMass (law c) cap ≤ ε) :
    reference.excessMass (centeredFiniteMarginal μ law hweight) cap ≤ ε :=
  centeredFiniteMarginal_excessMass_le_of_ae μ law hweight reference cap ε (ae_of_all μ h)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

section LieModules

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem sectionCorrectedPolynomial_coefficientBound
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    {H K : ℕ} (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (hS : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) K)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp : CoefficientBound (b.baseChange ℝ) T A p)
    (hq : CoefficientBound (c.baseChange ℝ) T B q) :
    CoefficientBound (b.baseChange ℝ) T
      (A + (((Fintype.card κ : ℝ) + 1) * (K + 1)) *
        ((((Fintype.card ι : ℝ) + 1) * (H + 1)) * A + B))
      (sectionCorrectedPolynomial φ S p q) := by
  apply (coefficientBound_iff_norm _ T hT (by positivity) _).mpr
  intro α
  exact sectionCorrectedPolynomial_coefficient_norm b c φ S hφ hS p q T A B α
    ((coefficientBound_iff_norm _ T hT hA p).mp hp α)
    ((coefficientBound_iff_norm _ T hT hB q).mp hq α)

end LieModules

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_step_one_character :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L 1 d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ f : D.Space → ℂ,
        (letI := D.metricSpace; LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ f) ∧
        (∀ x, ‖f x‖ = 1) ∧
        ∀ z : D.RealGroup, f (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z := by
  obtain ⟨C, hC, hseed⟩ := exists_native_central_seed 1
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD η hη hint
  let := D.metricSpace
  obtain ⟨K, hK, f, hLip, _, heq⟩ := hseed D hp hD η hη hint
  have heq' (z : D.RealGroup) : f (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z :=
    heq z (by rw [D.filtration.realification.subgroup_one]; trivial)
  refine ⟨f, hLip.weaken hK, ?_, heq'⟩
  intro x
  induction x using Quotient.inductionOn with
  | h z => rw [heq', logCharacter_norm]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.TripleProductBasisBounds
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem pi_layer_span (weight : ∀ i, Fin (d i) → ℕ)
    (hF : ∀ i n, (D i).filtration.layer n =
      Submodule.span ℚ ((D i).basis '' {k | n ≤ weight i k})) (n : ℕ) :
    (pi D).filtration.layer n =
      Submodule.span ℚ ((pi D).basis '' {k | n ≤ productBasisWeight weight k}) := by
  classical
  ext x
  change x ∈ (NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer n ↔ _
  rw [NilpotentLieFiltration.mem_pi_layer]
  constructor
  · intro hx
    apply (pi D).basis.mem_span_image.mpr
    intro k hk
    have hcoeff : (pi D).basis.repr x k ≠ 0 := Finsupp.mem_support_iff.mp hk
    rw [productFinBasis_repr D] at hcoeff
    let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
    have hm := hx z.1
    rw [hF z.1 n] at hm
    exact (D z.1).basis.mem_span_image.mp hm (Finsupp.mem_support_iff.mpr hcoeff)
  · intro hx i
    rw [hF i n]
    apply (D i).basis.mem_span_image.mpr
    intro k hk
    let q := (Fintype.equivFin (Σ i, Fin (d i))) ⟨i, k⟩
    have hq : (Fintype.equivFin (Σ i, Fin (d i))).symm q = ⟨i, k⟩ :=
      Equiv.symm_apply_apply _ _
    have hrepr : (pi D).basis.repr x q = (D i).basis.repr (x i) k :=
      (productFinBasis_repr D x q).trans
        (congrArg (fun z : Σ i, Fin (d i) => (D z.1).basis.repr (x z.1) z.2) hq)
    have hcoeff : (pi D).basis.repr x q ≠ 0 := by
      rw [hrepr]
      exact Finsupp.mem_support_iff.mp hk
    have hw := (pi D).basis.mem_span_image.mp hx (Finsupp.mem_support_iff.mpr hcoeff)
    change n ≤ productBasisWeight weight q at hw
    have hweight : productBasisWeight weight q = weight i k :=
      congrArg (fun z : Σ i, Fin (d i) => weight z.1 z.2) hq
    exact hw.trans_eq hweight

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

universe u v

namespace Erdos3

namespace RationalFilteredNilmanifold

open Module
open scoped TensorProduct

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

variable {H : Type u} [LieRing H] [LieAlgebra ℚ H]

theorem optionProductMap_logHeight {κ : Type*} (b : Basis κ ℚ H)
    (φ₀ : H →ₗ⁅ℚ⁆ L₀) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i) {p : ℝ}
    (h₀ : ∀ i j, rationalLogHeight (D₀.basis.repr (φ₀ (b j)) i) ≤ p)
    (hφ : ∀ a i j, rationalLogHeight ((D a).basis.repr (φ a (b j)) i) ≤ p) :
    ∀ i j, rationalLogHeight ((optionProduct D₀ D).basis.repr (optionProductMap φ₀ φ (b j)) i) ≤ p := by
  intro i j
  dsimp only [optionProduct]
  rw [productFinBasis_repr]
  generalize hz : (Fintype.equivFin (Σ i : Option ι, Fin (optionDimension d₀ d i))).symm i = z
  rcases z with ⟨a, k⟩
  cases a with
  | none => exact h₀ k j
  | some a => exact hφ a k j

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeProductOrbitMetric
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem productSpaceEquiv_lipschitz :
    letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    letI := (pi D).metricSpace
    LipschitzWith (productMetricBound d) (productSpaceEquiv D) := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (productMetricBound d).coe_nonneg dist_nonneg)).mpr
  intro i
  have hc : coordinateLipschitzBound (d i) (Fintype.card (Σ j, Fin (d j))) 1 ≤ productMetricBound d := by
    have heq : coordinateLipschitzBound (d i) (Fintype.card (Σ j, Fin (d j))) 1 =
        coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1 := by
      unfold coordinateLipschitzBound
      congr 1
      ring
    rw [heq]
    unfold productMetricBound
    exact Finset.single_le_sum
      (f := fun j : ι => coordinateLipschitzBound (Fintype.card (Σ k, Fin (d k))) (d j) 1)
      (s := Finset.univ) (fun _ _ => zero_le) (Finset.mem_univ i)
  exact ((productProjection_lipschitz D i).dist_le_mul x y).trans
    (mul_le_mul_of_nonneg_right (show (coordinateLipschitzBound (d i) (Fintype.card (Σ j, Fin (d j))) 1 : ℝ) ≤
      productMetricBound d from hc) dist_nonneg)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L Y W J : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing Y] [LieAlgebra ℚ Y] [LieRing W] [LieAlgebra ℚ W] {s : ℕ}
  (F : NilpotentLieFiltration L s) (π : L →ₗ⁅ℚ⁆ Y)
  (eta : J → L →ₗ[ℚ] ℚ) (js : List J)

theorem mem_pivotAnnihilatorIdeal (x : L) :
    x ∈ F.pivotAnnihilatorIdeal π eta js ↔
      x ∈ F.layer s ∧ π x = 0 ∧ ∀ j ∈ js, eta j x = 0 := by
  change x ∈ finiteFrequencyKernel (F.layer s ⊓ LinearMap.ker π.toLinearMap) eta js ↔ _
  rw [mem_finiteFrequencyKernel]
  change ((x ∈ F.layer s ∧ π x = 0) ∧ ∀ j ∈ js, eta j x = 0) ↔ _
  exact and_assoc

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I V : Type*} {N : I → ℕ} {q : ℕ}

variable [Fintype I] [DecidableEq I]

theorem comap_isDenseCommonStrideBox [Fintype V] [DecidableEq V]
    (A : ResidueBoxSlice N q) (hq : 0 < q) {c : ℝ}
    (hA : IsDenseCommonStrideBox N c A.integerPoints) (e : V → I) :
    IsDenseCommonStrideBox (fun v => N (e v)) c (A.comap e).integerPoints := by
  refine ⟨fun v => ((A.comap e).start v : ℤ), q, (A.comap e).length,
    hq, ?_, (A.comap e).progression_inside, ?_,
    (A.comap e).integerPoints_eq_commonStrideBox⟩
  · intro v
    exact A.length_pos_of_dense hA (e v)
  · intro v
    exact A.length_lower_of_dense hq hA (e v)

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {K : Type*} (oldKeep keep : K → Prop)

variable {oldKeep keep} {N : K → ℕ} {q oldq : ℕ}

noncomputable def extendAxes
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (A : ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) oldq)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (A.start i.val : ℤ) oldq (A.length i.val)) :
    ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) q where
  start i := if hi : keep i.val then S.start ⟨i.val, hi⟩ else (fixed ⟨i, hi⟩).toNat
  length i := if hi : keep i.val then S.length ⟨i.val, hi⟩ else 1
  inside i j hj := by
    by_cases hi : keep i.val
    · simpa only [dif_pos hi] using
        S.inside ⟨i.val, hi⟩ j (by simpa only [dif_pos hi] using hj)
    · have hj0 : j = 0 := by
        simpa only [dif_neg hi, Nat.lt_one_iff] using hj
      have hf := Finset.mem_Ico.mp (A.progression_inside i (hfixed ⟨i, hi⟩))
      simpa only [dif_neg hi, hj0, mul_zero, add_zero] using
        (show (fixed ⟨i, hi⟩).toNat < N i.val by omega)

attribute [local irreducible] integerProgressionSupport

variable [Fintype K]

theorem extendAxes_integerPoints
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (A : ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) oldq)
    (hsub : ∀ i, keep i → oldKeep i)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (A.start i.val : ℤ) oldq (A.length i.val)) :
    (@extendAxes K oldKeep keep N q oldq S A fixed hfixed).integerPoints =
      S.integerPoints.image (axisInsertion oldKeep keep fixed) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    let t : ∀ i : {i // keep i}, Fin (S.length i) := fun i =>
      ⟨(j (axisInclusion oldKeep keep hsub i)).val, by
        simpa [extendAxes, axisInclusion, i.property] using
          (j (axisInclusion oldKeep keep hsub i)).isLt⟩
    refine Finset.mem_image.mpr ⟨S.integerPoint t,
      Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩, ?_⟩
    funext i
    by_cases hi : keep i.val
    · simp [axisInsertion, integerPoint, point, extendAxes, hi, t, axisInclusion]
    · have hj0 : (j i).val = 0 := by
        have := (j i).isLt
        simpa only [extendAxes, dif_neg hi, Nat.lt_one_iff] using this
      have hf := (Finset.mem_Ico.mp (A.progression_inside i (hfixed ⟨i, hi⟩))).1
      simp [axisInsertion, integerPoint, point, extendAxes, hi, hj0,
        Int.toNat_of_nonneg hf]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hy
    let j : ∀ i, Fin ((@extendAxes K oldKeep keep N q oldq S A fixed hfixed).length i) := fun i =>
      if hi : keep i.val then
        ⟨(t ⟨i.val, hi⟩).val, by
          simp only [extendAxes, dif_pos hi]
          exact (t ⟨i.val, hi⟩).isLt⟩
      else ⟨0, by simp [extendAxes, hi]⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    funext i
    by_cases hi : keep i.val
    · simp [axisInsertion, integerPoint, point, extendAxes, hi, j]
    · have hf := (Finset.mem_Ico.mp (A.progression_inside i (hfixed ⟨i, hi⟩))).1
      simp [axisInsertion, integerPoint, point, extendAxes, hi, j,
        Int.toNat_of_nonneg hf]

theorem expect_extendAxes
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (A : ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) oldq)
    (hsub : ∀ i, keep i → oldKeep i)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (A.start i.val : ℤ) oldq (A.length i.val))
    {W : Type*} [AddCommMonoid W] [Module ℚ≥0 W]
    (f : ({i // oldKeep i} → ℤ) → W) :
    (𝔼 x ∈ (@extendAxes K oldKeep keep N q oldq S A fixed hfixed).integerPoints, f x) =
      𝔼 x ∈ S.integerPoints, f (axisInsertion oldKeep keep fixed x) := by
  rw [S.extendAxes_integerPoints (N := N) A hsub fixed hfixed]
  exact Finset.expect_image (axisInsertion_injective oldKeep keep hsub fixed).injOn

theorem extendAxes_dense
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (A : ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) oldq)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (A.start i.val : ℤ) oldq (A.length i.val))
    (hq : 0 < q) {outCost shortCost : ℝ}
    (hS : IsDenseCommonStrideBox (fun i : {i // keep i} => N i.val)
      outCost S.integerPoints)
    (hshort : ∀ i : {i // oldKeep i}, ¬keep i.val →
      (N i.val : ℝ) ≤ Real.exp shortCost) :
    IsDenseCommonStrideBox (fun i : {i // oldKeep i} => N i.val)
      (max outCost shortCost) (@extendAxes K oldKeep keep N q oldq S A fixed hfixed).integerPoints := by
  let T := @extendAxes K oldKeep keep N q oldq S A fixed hfixed
  refine ⟨fun i => (T.start i : ℤ), q, T.length, hq, ?_,
    T.progression_inside, ?_, T.integerPoints_eq_commonStrideBox⟩
  · intro i
    by_cases hi : keep i.val
    · simpa only [T, extendAxes, dif_pos hi] using S.length_pos_of_dense hS ⟨i.val, hi⟩
    · simp [T, extendAxes, hi]
  · intro i
    by_cases hi : keep i.val
    · calc
        _ ≤ Real.exp (-outCost) * (N i.val : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (neg_le_neg (le_max_left _ _))) (Nat.cast_nonneg _)
        _ ≤ T.length i := by
          simpa only [T, extendAxes, dif_pos hi] using
            S.length_lower_of_dense hq hS ⟨i.val, hi⟩
    · simp only [T, extendAxes, dif_neg hi, Nat.cast_one]
      calc
        _ ≤ Real.exp (-shortCost) * (N i.val : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))) (Nat.cast_nonneg _)
        _ ≤ Real.exp (-shortCost) * Real.exp shortCost :=
          mul_le_mul_of_nonneg_left (hshort i hi) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorTranslationDegreeSymbol
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

theorem exists_translation_coordinate_polynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hPslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) P u ∈ weightedSupportLT w d) :
    ∃ p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1),
      ∀ u : U → ℝ,
        bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
            (fun _ : U => 1) u p) =
          ⟨fun i => eval u (A i), specializeMajorParameters (RingHom.id ℝ) P u⟩ := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  let F := weightedFiltration w d hwd
  let b := weightedBasis w d hw
  let ω := weightedBasisGrade w d
  have hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}) :=
    weightedFiltration_layer_eq_span w d hw hwd
  let Acoord : WeightedBasisIndex w d → MvPolynomial U ℝ := Sum.elim A (fun _ => 0)
  let Pcoord : WeightedBasisIndex w d → MvPolynomial U ℝ :=
    Sum.elim (fun _ => 0) (fun α => polynomialSlotCoefficient α.val P)
  have hAcoord : ∀ i, Acoord i ∈ weightedSupportLE (fun _ : U => 1) (ω i) := by
    intro i
    cases i with
    | inl i => exact (mem_weightedSupportLE_one_iff _ _).mpr (hA i)
    | inr α => exact Submodule.zero_mem _
  have hPcoord : ∀ i, Pcoord i ∈ weightedSupportLE (fun _ : U => 1) (ω i) := by
    intro i
    cases i with
    | inl i => exact Submodule.zero_mem _
    | inr α => exact polynomialSlotCoefficient_degree (fun _ : U => 1) w hP α.val
  let a := F.realCoordinatePolynomialOrbit b ω hlayers (fun _ : U => 1) Acoord hAcoord
  let q := F.realCoordinatePolynomialOrbit b ω hlayers (fun _ : U => 1) Pcoord hPcoord
  have ha (u : U → ℝ) : bchRealTranslationHom w d hwd
      (F.realification.polynomialOrbitRealEval (fun _ : U => 1) u a) =
        ⟨fun i => eval u (A i), 0⟩ := by
    let g := F.realification.polynomialOrbitRealEval (fun _ : U => 1) u a
    have hs := realShearEmbedding_shape_of_coordinates w d hw g.coord
      (fun i => eval u (A i)) (0 : weightedSupportLT (R := ℝ) w d) ?_ ?_
    · exact bchRealTranslationHom_pure_base_of_shape w d hwd g.coord _ hs.1
        (by simpa only [ZeroMemClass.coe_zero, map_zero] using hs.2)
    · intro i
      exact F.realCoordinatePolynomialOrbit_eval_coordinates b ω hlayers _ Acoord hAcoord u (Sum.inl i)
    · intro α
      have h := F.realCoordinatePolynomialOrbit_eval_coordinates b ω hlayers _ Acoord hAcoord u (Sum.inr α)
      simpa only [Acoord, Sum.elim_inr, map_zero, ZeroMemClass.coe_zero,
        MvPolynomial.coeff_zero] using h
  have hq (u : U → ℝ) : bchRealTranslationHom w d hwd
      (F.realification.polynomialOrbitRealEval (fun _ : U => 1) u q) =
        ⟨0, specializeMajorParameters (RingHom.id ℝ) P u⟩ := by
    let g := F.realification.polynomialOrbitRealEval (fun _ : U => 1) u q
    let Pu : weightedSupportLT (R := ℝ) w d :=
      ⟨specializeMajorParameters (RingHom.id ℝ) P u, hPslot u⟩
    have hs := realShearEmbedding_shape_of_coordinates w d hw g.coord 0 Pu ?_ ?_
    · exact bchRealTranslationHom_pure_polynomial_of_shape w d hwd g.coord Pu.val
        (fun i => by simpa only [Pi.zero_apply, map_zero] using hs.1 i) hs.2
    · intro i
      have h := F.realCoordinatePolynomialOrbit_eval_coordinates b ω hlayers _ Pcoord hPcoord u (Sum.inl i)
      simpa only [Pcoord, Sum.elim_inl, map_zero, Pi.zero_apply] using h
    · intro α
      have h := F.realCoordinatePolynomialOrbit_eval_coordinates b ω hlayers _ Pcoord hPcoord u (Sum.inr α)
      change (b.baseChange ℝ).repr g.coord (Sum.inr α) = eval u (polynomialSlotCoefficient α.val P) at h
      rw [h]
      simpa only [MvPolynomial.aeval_eq_eval, Pu, specializeMajorParameters,
        RingHom.comp_id, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq,
        Algebra.algebraMap_self, MvPolynomial.eval₂_id, MvPolynomial.coe_eval₂Hom] using
        polynomialSlotCoefficient_eval u α.val P
  refine ⟨a * q, fun u => ?_⟩
  rw [map_mul, map_mul, ha, hq]
  apply PolynomialTranslationGroupOver.ext <;> simp

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OptionMarkedSurjective
namespace OAI

section

universe u v

namespace Erdos3

open scoped TensorProduct

variable {ι : Type v} {L₀ M₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing M₀] [LieAlgebra ℚ M₀]
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}

open NilpotentLieFiltration

theorem optionMarkedLieMap_mem_layer (F₀ : NilpotentLieFiltration L₀ s)
    (G₀ : NilpotentLieFiltration M₀ s) (F : ∀ i, NilpotentLieFiltration (L i) s)
    (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (hφ : ∀ n x, x ∈ F₀.layer n → φ x ∈ G₀.layer n)
    (n : ℕ) (x : ∀ i : Option ι, optionLieSpace L₀ L i)
    (hx : x ∈ (pi (optionFiltrations F₀ F)).layer n) :
    optionMarkedLieMap φ x ∈ (pi (optionFiltrations G₀ F)).layer n := by
  apply (mem_pi_layer _ _ _).mpr
  intro i
  cases i with
  | none => exact hφ n _ ((mem_pi_layer _ _ _).mp hx none)
  | some i => exact (mem_pi_layer _ _ _).mp hx (some i)

end Erdos3

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {Partner : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ a, LieRing (Partner a)] [∀ a, LieAlgebra ℚ (Partner a)]
    {s dL dM : ℕ} {d : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s dL)
    (Q : RationalFilteredNilmanifold M s dM)
    (E : ∀ a, RationalFilteredNilmanifold (Partner a) s (d a))
    (φ : L →ₗ⁅ℚ⁆ M)

theorem optionMarkedLieMap_native_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hφ : ∀ i j, rationalLogHeight (Q.basis.repr (φ (D.basis j)) i) ≤ p) :
    ∀ i j, rationalLogHeight ((optionProduct Q E).basis.repr
      (optionMarkedLieMap (L := Partner) φ ((optionProduct D E).basis j)) i) ≤ p := by
  classical
  intro i j
  dsimp only [optionProduct]
  rw [productFinBasis_repr]
  generalize hz :
    (Fintype.equivFin (Σ a : Option Pivot, Fin (optionDimension dM d a))).symm i = z
  rcases z with ⟨a, k⟩
  cases a with
  | none =>
    change rationalLogHeight (Q.basis.repr
      (φ (productFinBasis (optionFactors D E) j none)) k) ≤ p
    rw [productFinBasis, Basis.reindex_apply]
    generalize hy :
      (Fintype.equivFin (Σ a : Option Pivot, Fin (optionDimension dL d a))).symm j = y
    rcases y with ⟨b, l⟩
    rw [Pi.basis_apply]
    cases b with
    | none =>
      rw [Pi.single_eq_same]
      exact hφ k l
    | some b =>
      rw [Pi.single_eq_of_ne (by simp : (none : Option Pivot) ≠ some b)]
      change rationalLogHeight (Q.basis.repr (φ (0 : L)) k) ≤ p
      rw [map_zero, map_zero]
      change rationalLogHeight (0 : ℚ) ≤ p
      simpa [rationalLogHeight] using hp
  | some a =>
    change rationalLogHeight ((E a).basis.repr
      (liePiEval (R := ℚ) (some a) ((optionProduct D E).basis j)) k) ≤ p
    exact rationalLogHeight_le_of_height
      (productProjection_matrix_height (optionFactors D E) (some a) j k)
      (by simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr hp)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedTopQuotient
namespace OAI

section

namespace Erdos3

open Module

theorem lieQuotientProjection_basis_logHeight
    {L M ι κ β γ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] [Fintype ι] [Fintype κ] [Fintype β]
    (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (b : Basis β ℚ (L ⧸ I)) (c : Basis γ ℚ (M ⧸ J))
    (φ : L →ₗ⁅ℚ⁆ M) (hIJ : ∀ x ∈ I, φ x ∈ J)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hβ : (Fintype.card β : ℝ) ≤ p)
    (hI : ∀ i j, rationalLogHeight (b.repr (lieQuotientMap I (e i)) j) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p)
    (hJ : ∀ i j, rationalLogHeight (c.repr (lieQuotientMap J (f i)) j) ≤ p) :
    ∀ i j, rationalLogHeight (c.repr (lieQuotientProjection I J φ hIJ (b i)) j) ≤
      quotientInducedMapHeightBudget p := by
  let H := ⌈Real.exp p⌉₊
  obtain ⟨S, hsection, hSH⟩ := exists_bounded_linear_image_section e b
    (lieQuotientMap I).toLinearMap (one_le_ceil_exp p)
    (fun i j => rationalHeightLE_ceil_exp (hI j i))
  have hright (x : L ⧸ I) : lieQuotientMap I (S x) = x := by
    obtain ⟨y, rfl⟩ := lieQuotientMap_surjective I x
    exact congrArg (fun T : L →ₗ[ℚ] (L ⧸ I) => T y) hsection
  have hcost : (rationalKernelHeight (Fintype.card β) H : ℝ) ≤ Real.exp ((p + 3) ^ 7) := by
    have h := rationalKernelHeight_le_budget (Fintype.card β) H
      (show 0 ≤ p + 1 by linarith) (hβ.trans (by linarith)) (ceil_exp_le_exp_add_one hp)
    simpa only [show p + 1 + 2 = p + 3 by ring] using h
  have hS (i : β) (j : ι) : rationalLogHeight (e.repr (S (b i)) j) ≤ (p + 3) ^ 7 :=
    rationalLogHeight_le_of_height (hSH j i) hcost
  let q := p + (p + 3) ^ 7 + 1
  have hseven : 0 ≤ (p + 3) ^ 7 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith only [hseven]
  have hsevenq : (p + 3) ^ 7 ≤ q := by dsimp [q]; linarith only [hp]
  have hmarked (i : β) (j : κ) : rationalLogHeight (f.repr (φ (S (b i))) j) ≤ (q + 2) ^ 4 :=
    linearMap_coordinate_logHeight e f φ.toLinearMap hq (hι.trans hpq)
      (fun a k => (hφ a k).trans hpq) (S (b i)) (fun a => (hS i a).trans hsevenq) j
  let t := (q + 2) ^ 4 + q
  have hfour : 0 ≤ (q + 2) ^ 4 := by positivity
  have ht : 0 ≤ t := add_nonneg hfour hq
  have hqt : q ≤ t := le_add_of_nonneg_left hfour
  have hpowt : (q + 2) ^ 4 ≤ t := le_add_of_nonneg_right hq
  intro i j
  have hinduced : lieQuotientProjection I J φ hIJ (b i) = lieQuotientMap J (φ (S (b i))) := by
    simpa only [hright] using lieQuotientProjection_mk I J φ hIJ (S (b i))
  rw [hinduced]
  exact linearMap_coordinate_logHeight f c (lieQuotientMap J).toLinearMap ht
    (hκ.trans (hpq.trans hqt)) (fun a k => (hJ a k).trans (hpq.trans hqt))
    (φ (S (b i))) (fun a => (hmarked i a).trans hpowt) j

end Erdos3

end

section

namespace Erdos3
open Module

theorem quotientInducedMark_basis_logHeight
    {L M ι κ β : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] [Fintype ι] [Fintype β]
    (I : LieIdeal ℚ L) (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (b : Basis β ℚ (L ⧸ I)) (φ : L →ₗ⁅ℚ⁆ M)
    (hker : ∀ x ∈ I, φ x = 0) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hβ : (Fintype.card β : ℝ) ≤ p)
    (hI : ∀ i j, rationalLogHeight (b.repr (lieQuotientMap I (e i)) j) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p) :
    ∀ i j, rationalLogHeight (f.repr (quotientInducedMark I φ hker (b i)) j) ≤
      quotientInducedMarkHeightBudget p := by
  let H := ⌈Real.exp p⌉₊
  obtain ⟨sectionMap, hsection, hheight⟩ := exists_bounded_linear_image_section e b
    (lieQuotientMap I).toLinearMap (one_le_ceil_exp p)
    (fun i j => rationalHeightLE_ceil_exp (hI j i))
  have hright (x : L ⧸ I) : lieQuotientMap I (sectionMap x) = x := by
    obtain ⟨y, rfl⟩ := lieQuotientMap_surjective I x
    exact congrArg (fun T : L →ₗ[ℚ] (L ⧸ I) => T y) hsection
  have hcost : (rationalKernelHeight (Fintype.card β) H : ℝ) ≤
      Real.exp ((p + 3) ^ 7) := by
    have h := rationalKernelHeight_le_budget (Fintype.card β) H
      (show 0 ≤ p + 1 by linarith) (hβ.trans (by linarith))
      (ceil_exp_le_exp_add_one hp)
    simpa only [show p + 1 + 2 = p + 3 by ring] using h
  have hS (i : β) (j : ι) :
      rationalLogHeight (e.repr (sectionMap (b i)) j) ≤ (p + 3) ^ 7 :=
    rationalLogHeight_le_of_height (hheight j i) hcost
  let q := p + (p + 3) ^ 7 + 1
  have hseven : 0 ≤ (p + 3) ^ 7 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hsevenq : (p + 3) ^ 7 ≤ q := by dsimp [q]; linarith
  intro i j
  have hinduced : quotientInducedMark I φ hker (b i) = φ (sectionMap (b i)) := by
    simpa only [hright] using quotientInducedMark_mk I φ hker (sectionMap (b i))
  rw [hinduced]
  have hbound := linearMap_coordinate_logHeight e f φ.toLinearMap hq (hι.trans hpq)
    (fun a k => (hφ a k).trans hpq) (sectionMap (b i))
    (fun a => (hS i a).trans hsevenq) j
  change rationalLogHeight (f.repr (φ (sectionMap (b i))) j) ≤ (q + 2) ^ 4 at hbound
  convert hbound using 1
  unfold quotientInducedMarkHeightBudget q
  congr 1
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_vertical_decomposition_preserving_bounds (T : D.Niltest w)
    {p rho : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (hrho : 0 < rho)
    (hrhop : rho⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, (U j).ComplexityLE p ∧ (U j).orbit = T.orbit ∧
        (U j).normBound = T.normBound ∧ (U j).lipBound = T.lipBound) ∧
      (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j).observable (z • x) =
          character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
      (∀ j, (∃ x, (U j).observable x ≠ 0) → ∀ z : D.RealGroup,
        z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional (eta j) z.coord = n) ∧
      (∀ x, ‖(∑ j, (U j).observable x) - T.observable x‖ ≤ rho) ∧
      ∀ x : σ → ℤ, ‖(∑ j, (U j).eval x) - T.eval x‖ ≤ rho := by
  let := D.metricSpace
  have hK : (T.lipBound : ℝ) ≤ Real.exp p := by
    have h := observable_budget hT
    have hB := T.normBound.coe_nonneg
    linarith
  obtain ⟨J, inst, eta, v, hcard, hheight, hv, hchar, _, herr⟩ :=
    D.exists_controlled_vertical_decomposition hp hT.1 T.observable T.lipBound T.normBound
      T.lipschitz T.norm_le hK rho hrho hrhop
  let U : J → D.Niltest w := fun j =>
    { orbit := T.orbit
      observable := v j
      normBound := T.normBound
      lipBound := T.lipBound
      norm_le := (hv j).2
      lipschitz := (hv j).1 }
  refine ⟨J, inst, eta, U, hcard, hheight, fun _ => ⟨hT, rfl, rfl, rfl⟩, hchar, ?_, herr, ?_⟩
  · intro j hne z hz hGamma
    exact vertical_frequency_integral_on_lattice D.filtration D.realLattice (eta j) (v j)
      (hchar j) hne z hz hGamma
  · intro x
    exact herr (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x T.orbit))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductComponentCoordinates
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productFinBasis_repr_component (x : ∀ i, L i) (a : ι) (k : Fin (d a)) :
    (D a).basis.repr (x a) k =
      (pi D).basis.repr x (Fintype.equivFin (Σ i, Fin (d i)) ⟨a, k⟩) := by
  symm
  exact (productFinBasis_repr D x _).trans
    (congrArg (fun z : Σ i, Fin (d i) => (D z.1).basis.repr (x z.1) z.2)
      (Equiv.symm_apply_apply _ _))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OptionComplementCover
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : Option ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def optionProductSpaceEquiv :
    (pi D).Space ≃ (D none).Space × (pi (fun i => D (some i))).Space :=
  ((productSpaceEquiv D).trans Equiv.piOptionEquivProd).trans
    (Equiv.prodCongr (Equiv.refl _) (productSpaceEquiv (fun i => D (some i))).symm)

theorem optionProductSpaceEquiv_apply (x : (pi D).Space) :
    optionProductSpaceEquiv D x =
      (productSpaceEquiv D x none,
        (productSpaceEquiv (fun i => D (some i))).symm (fun i => productSpaceEquiv D x (some i))) := rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [LieRing H] [LieAlgebra ℚ H]
  {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {r t : ℕ} {d : ι → ℕ} (F : NilpotentLieFiltration H r)
  (D : ∀ i, RationalFilteredNilmanifold (L i) t (d i))

omit [DecidableEq ι] in
theorem productProjectionHom_realificationMap (φ : ∀ i, H →ₗ⁅ℚ⁆ L i)
    (x : F.realification.Group) (i : ι) :
    productProjectionHom D i
      (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (pi D).filtration.lowerCentralSeries_eq_bot) (liePiMap φ) x) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (D i).filtration.lowerCentralSeries_eq_bot) (φ i) x := by
  apply NilpotentLieBCHGroup.ext
  exact realification_liePiEval_liePiMap φ x.coord i

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [LieRing H] [LieAlgebra ℚ H]
  {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {r t : ℕ} {d : Option ι → ℕ} (F : NilpotentLieFiltration H r)
  (D : ∀ i, RationalFilteredNilmanifold (L i) t (d i))

theorem optionProductSpaceEquiv_realificationMap (φ : ∀ i, H →ₗ⁅ℚ⁆ L i)
    (x : F.realification.Group) :
    optionProductSpaceEquiv D
      (QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (pi D).filtration.lowerCentralSeries_eq_bot) (liePiMap φ) x)) =
      (QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
          (hM := (D none).filtration.lowerCentralSeries_eq_bot) (φ none) x),
        QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
          (hM := (pi (fun i => D (some i))).filtration.lowerCentralSeries_eq_bot)
          (liePiMap (fun i => φ (some i))) x)) := by
  rw [optionProductSpaceEquiv_apply]
  apply Prod.ext
  · simp only [productSpaceEquiv_mk, productProjectionHom_realificationMap]
  · apply (productSpaceEquiv (fun i => D (some i))).injective
    rw [Equiv.apply_symm_apply]
    funext i
    simp only [productSpaceEquiv_mk, productProjectionHom_realificationMap]

omit [DecidableEq ι] in
theorem lowered_productProjectionHom_realificationMap {s n : ℕ}
    (Q : RationalFilteredNilmanifold (L none) s n) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i)
    (x : F.realification.Group) :
    changeStep (D none).filtration.realification.lowerCentralSeries_eq_bot
      Q.filtration.realification.lowerCentralSeries_eq_bot
      (productProjectionHom D none (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (pi D).filtration.lowerCentralSeries_eq_bot) (liePiMap φ) x)) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (φ none) x := by
  rw [productProjectionHom_realificationMap]
  rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelProjectionPresentPivotIdeal
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Classical

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

theorem finiteFrequencyKernel_presentPivots
    (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    {r : ℕ} (code : Fin r → Option J) :
    finiteFrequencyKernel P (fun k => eta (kernelProjectionSelectedPivot code k))
      (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList =
      frequencyCodeKernel P eta code := by
  ext x
  rw [mem_finiteFrequencyKernel, mem_frequencyCodeKernel]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h i j hij
    let k : KernelProjectionPresentPivot code := ⟨i, ⟨j, hij⟩⟩
    have hselected : kernelProjectionSelectedPivot code k = j := by
      exact Option.some.inj ((kernelProjectionSelectedPivot_spec code k).symm.trans hij)
    simpa only [hselected] using h k (Finset.mem_toList.mpr (Finset.mem_univ k))
  · intro h k _
    exact h k.val (kernelProjectionSelectedPivot code k)
      (kernelProjectionSelectedPivot_spec code k)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

def fiberFullParameters
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (u : ∀ k, Fin (S.length k)) (i : X) : Fin (S.fiberParameterLength i) :=
  ⟨if hi : keep i then (u ⟨i, hi⟩).val else 0, by
    by_cases hi : keep i
    · simpa only [fiberParameterLength, dif_pos hi] using (u ⟨i, hi⟩).isLt
    · simp only [fiberParameterLength, dif_neg hi, Nat.zero_lt_one]⟩

def fiberFullParameterEquiv
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q) :
    (∀ k, Fin (S.length k)) ≃ (∀ i, Fin (S.fiberParameterLength i)) where
  toFun := S.fiberFullParameters
  invFun := S.fiberKeptParameters
  left_inv u := by
    funext k
    apply Fin.ext
    simp only [fiberKeptParameters, fiberFullParameters, dif_pos k.property]
  right_inv v := by
    funext i
    apply Fin.ext
    by_cases hi : keep i
    · simp only [fiberFullParameters, fiberKeptParameters, dif_pos hi]
    · have hv : (v i).val < 1 := by
        simpa only [fiberParameterLength, dif_neg hi] using (v i).isLt
      simp only [fiberFullParameters, dif_neg hi]
      omega

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
variable {keep : G ⊕ P → Prop} [DecidablePred keep] {N : G ⊕ P → ℕ} {q : ℕ}

def fiberKernelParameterEquiv
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hkernel : ∀ i, keep (Sum.inl i)) :
    (∀ i, Fin (S.fiberParameterLength (Sum.inl i))) ≃
      (∀ i, Fin (S.length ⟨Sum.inl i, hkernel i⟩)) where
  toFun g i := ⟨(g i).val, by
    simpa only [fiberParameterLength, dif_pos (hkernel i)] using (g i).isLt⟩
  invFun g i := ⟨(g i).val, by
    simpa only [fiberParameterLength, dif_pos (hkernel i)] using (g i).isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3.ScalarSiteExpansion
open scoped BigOperators NNReal Classical
universe u v
variable {S : Type u} [Fintype S]

noncomputable def atCeilScale (e : ScalarSiteExpansion.{u,v} S) (K d : ℕ) (γ : ℝ) :
    ScalarSiteExpansion.{u,v} S :=
  e.rescale (((⌈γ * (K : ℝ)⌉₊ : ℝ) / K) ^ d : ℂ) ((⌈γ * (K : ℝ)⌉₊ : ℝ) / K)

end Erdos3.ScalarSiteExpansion

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedProbabilityGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def allocatedGridAmbientCoordinates (z : JetAmbientIndex O J → ℝ) :
    ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, O a.val.1 → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => fun t => (mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
      ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, t, k⟩))).2 i

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeModelOrbit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s d)
  (h : D.rationalModelCoordinates = E.rationalModelCoordinates)

noncomputable def rationalModelEquiv : L ≃ₗ⁅ℚ⁆ M :=
  { D.basis.repr.trans E.basis.repr.symm with
    map_lie' {x y} := by
      apply E.basis.repr.injective
      ext k
      change E.basis.repr (E.basis.repr.symm (D.basis.repr ⁅x, y⁆)) k = _
      rw [LinearEquiv.apply_symm_apply, lie_coordinate_formula, lie_coordinate_formula]
      apply Finset.sum_congr rfl
      intro ij _
      have hc : lieStructureConstants D.basis ij.1 ij.2 k =
          lieStructureConstants E.basis ij.1 ij.2 k := congrFun h (.inl (ij.1, ij.2, k))
      change lieStructureConstants D.basis ij.1 ij.2 k * D.basis.repr x ij.1 * D.basis.repr y ij.2 =
        lieStructureConstants E.basis ij.1 ij.2 k *
          E.basis.repr (E.basis.repr.symm (D.basis.repr x)) ij.1 *
          E.basis.repr (E.basis.repr.symm (D.basis.repr y)) ij.2
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hc] }

theorem rationalModelEquiv_repr (x : L) :
    E.basis.repr (D.rationalModelEquiv E h x) = D.basis.repr x :=
  E.basis.repr.apply_symm_apply _

theorem rationalModelEquiv_basis (i : Fin d) :
    D.rationalModelEquiv E h (D.basis i) = E.basis i := by
  apply E.basis.repr.injective
  rw [rationalModelEquiv_repr]
  simp only [Basis.repr_self]

theorem rationalModelEquiv_paddedLayerVector (i : Fin (s + 1)) (k : Fin d) :
    D.rationalModelEquiv E h (D.paddedLayerVector i k) = E.paddedLayerVector i k := by
  apply E.basis.repr.injective
  rw [rationalModelEquiv_repr]
  ext j
  exact congrFun h (.inr (i, k, j))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonRationalModelCoordinates
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_common_rational_model_coordinates
    {G : Type*} {L : G → Type*} [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)]
    {s d : ℕ} (D : ∀ h, RationalFilteredNilmanifold (L h) s d)
    (H : Finset G) (hH : H.Nonempty) {p : ℝ} (hp : 0 ≤ p)
    (hD : ∀ h ∈ H, (D h).GeometryComplexityLE p) :
    ∃ h₀ ∈ H, ∃ H' : Finset G, H' ⊆ H ∧ h₀ ∈ H' ∧
      (∀ h ∈ H', (D h).rationalModelCoordinates = (D h₀).rationalModelCoordinates) ∧
      Real.exp (-(3 * (d ^ 3 + (s + 1) * d ^ 2 : ℕ) * (p + 2))) * H.card ≤ (H'.card : ℝ) := by
  let S : Set (RationalModelCoordinateIndex s d → ℚ) :=
    {c | ∀ z, rationalLogHeight (c z) ≤ p}
  obtain ⟨hfinite, hcount⟩ := finite_card_bounded_height_arrays S ⌈Real.exp p⌉₊
    (fun _ hc z => rationalHeightLE_ceil_exp (hc z))
  have hcount' : (S.ncard : ℝ) ≤ Real.exp (3 * (d ^ 3 + (s + 1) * d ^ 2 : ℕ) * (p + 2)) := by
    have hh := (Nat.cast_le.mpr hcount).trans
      (rational_log_height_count_exp_bound (Fintype.card (RationalModelCoordinateIndex s d)) hp)
    have hdim : Fintype.card (RationalModelCoordinateIndex s d) = d ^ 3 + (s + 1) * d ^ 2 := by
      simp only [RationalModelCoordinateIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      ring
    simpa only [hdim] using hh
  obtain ⟨c, _, H', hsub, hnonempty, hcode, hlarge⟩ :=
    exists_exponential_constant_fiber H hH (fun h => (D h).rationalModelCoordinates)
      S hfinite (fun h hh => (D h).rationalModelCoordinates_height hp (hD h hh)) hcount'
  obtain ⟨h₀, hh₀⟩ := hnonempty
  exact ⟨h₀, hsub hh₀, H', hsub, hh₀,
    (fun h hh => (hcode h hh).trans (hcode h₀ hh₀).symm), hlarge⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteStageNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedFiniteForwardWork_eq (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardWork A stageCountConstant n x =
      (preparedFiniteForwardParameter A stageCountConstant n x + A) ^ A := by
  simp [preparedFiniteForwardWork, preparedFiniteForwardWorkPolynomial,
    preparedFiniteForwardParameter, Polynomial.eval₂_pow]

theorem preparedFiniteForwardCap_eq (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardCap A stageCountConstant n x =
      (4 * preparedFiniteForwardParameter A stageCountConstant n x +
        4 * preparedFiniteForwardWork A stageCountConstant n x + 16 + A) ^ A := by
  simp [preparedFiniteForwardCap, preparedFiniteForwardCapPolynomial,
    preparedFiniteForwardParameter, preparedFiniteForwardWork, Polynomial.eval₂_pow]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateCommonFastGeometry
namespace OAI

section

namespace Erdos3
open Module
open scoped Matrix TensorProduct Classical

theorem exists_bounded_submodule_quotient_section_with_coordinates
    {ι η V : Type*} [Fintype ι] [Fintype η] [DecidableEq ι]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (U : Submodule ℚ V) (v : η → V)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hHpos : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card η : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ (eQ : Basis (Fin d) ℚ (V ⧸ U)) (S : (V ⧸ U) →ₗ[ℚ] V) (qS : ℕ),
        Function.RightInverse S U.mkQ ∧
        Function.RightInverse (S.baseChange ℝ) (U.mkQ.baseChange ℝ) ∧
        0 < qS ∧ (qS : ℝ) ≤ Real.exp ((p + 2) ^ 47) ∧
        (∀ i j, |(b.baseChange ℝ).repr
          (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Real.exp ((p + 2) ^ 45)) ∧
        (∀ j, (fun i => (b.baseChange ℝ).repr
          (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS) ∧
        ∀ j i, RationalHeightLE (((eQ.coord j).comp U.mkQ) (b i))
          ⌈Real.exp ((p + 2) ^ 7)⌉₊ := by
  obtain ⟨d, hd, D, T, hker, hDT, hD, hT⟩ :=
    exists_submodule_quotient_presentation_exp_height b U v hspan hHpos hv hp hrows hcols hH
  obtain ⟨eQ, S, hright, hrightR, _hentryQ, hentryR, hcoord⟩ :=
    exists_submoduleQuotientSectionBasis_with_coordinates b U D T hker hDT
  have hdim : (Fintype.card (Fin d) : ℝ) ≤ p := by
    simp only [Fintype.card_fin]
    exact (Nat.cast_le.mpr hd).trans hrows
  obtain ⟨habs, qS, _heq, hqS, hqSbound, hgrid⟩ :=
    rational_section_entry_budget T hp hrows hdim hT
  refine ⟨d, hd, eQ, S, qS, hright, hrightR, hqS, hqSbound, ?_, ?_, ?_⟩
  · intro i j
    rw [hentryR]
    exact habs i j
  · intro j
    choose z hz using fun i => hgrid i j
    refine ⟨z, ?_⟩
    funext i
    change (z i : ℝ) = (qS : ℝ) * (b.baseChange ℝ).repr
      (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i
    rw [hentryR]
    exact (hz i).symm
  · intro j i
    change RationalHeightLE (eQ.repr (U.mkQ (b i)) j) _
    rw [hcoord]
    exact ⟨Nat.cast_le.mp ((hD j i).1.trans (Nat.le_ceil _)),
      Nat.cast_le.mp ((hD j i).2.trans (Nat.le_ceil _))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardTreeStorage
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteForwardModelPrecision
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x gainLog stageLog : ℝ) : ℝ :=
  preparedFiniteForwardPrefixLog A stageCountConstant n x + gainLog +
    preparedFiniteForwardWork A stageCountConstant n x + stageLog + 6

noncomputable def preparedFiniteForwardSourcePrecision
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x gainLog stageLog : ℝ) : ℝ :=
  preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
    2 * preparedFiniteForwardWork A stageCountConstant n x + 1

theorem preparedFiniteForward_model_precision_bounds
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x gainLog stageLog : ℝ}
    (hx : 0 ≤ x) (hg : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x) :
    let b := preparedFiniteForwardParameter A stageCountConstant n x
    let w := preparedFiniteForwardWork A stageCountConstant n x
    let u := preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog
    let sourceU := preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog
    0 ≤ u ∧ 0 ≤ sourceU ∧ sourceU = u + 2 * w + 1 ∧
      preparedFiniteForwardPrefixLog A stageCountConstant n x + gainLog + w + stageLog + 6 ≤ u ∧
      sourceU + w ≤ 4 * b + 4 * w + 16 := by
  intro b w u sourceU
  have hp := preparedFiniteForward_prefix_bounds A stageCountConstant n hx
  have hw : 0 ≤ w := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hbase : x ≤ b := by
    have heq := preparedFiniteForwardParameter_prefix A stageCountConstant n x
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    change x ≤ preparedFiniteForwardParameter A stageCountConstant n x
    linarith only [heq, hp.1.1, hp.2.1, hn]
  have hu : 0 ≤ u := by
    dsimp only [u, preparedFiniteForwardModelPrecision]
    linarith only [hp.2.1, hg.1, hw, hstage.1]
  have hs : sourceU = u + 2 * w + 1 := rfl
  refine ⟨hu, by linarith only [hs, hu, hw], hs, le_rfl, ?_⟩
  have hueq : u = preparedFiniteForwardPrefixLog A stageCountConstant n x +
      gainLog + w + stageLog + 6 := rfl
  have hb : 0 ≤ b := hx.trans hbase
  have hg' : gainLog ≤ b := hg.2.trans hbase
  have ht' : stageLog ≤ b := hstage.2.trans hbase
  linarith only [hs, hueq, hp.2.2, hg', ht', hb]

theorem preparedFiniteForward_phase_cap
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n Cphase : ℕ) {x gainLog stageLog : ℝ}
    (hx : 0 ≤ x) (hg : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (hphase : Cphase ≤ A) :
    (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
      preparedFiniteForwardWork A stageCountConstant n x + Cphase) ^ Cphase ≤
        preparedFiniteForwardCap A stageCountConstant n x := by
  have hp := preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hstage
  have hb := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hw := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hC : (0 : ℝ) ≤ Cphase := Nat.cast_nonneg _
  rw [preparedFiniteForwardCap_eq]
  apply (pow_le_pow_left₀ (by linarith only [hp.2.1, hw, hC])
    (show preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
      preparedFiniteForwardWork A stageCountConstant n x + Cphase ≤
      4 * preparedFiniteForwardParameter A stageCountConstant n x +
        4 * preparedFiniteForwardWork A stageCountConstant n x + 16 + A by
      have hC' : (Cphase : ℝ) ≤ A := Nat.cast_le.mpr hphase
      linarith only [hp.2.2.2.2, hC']) Cphase).trans
  exact pow_le_pow_right₀ (by linarith only [hb, hw, hA]) hphase

theorem preparedFiniteForward_model_scalar_bounds
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n count : ℕ) {x : ℝ}
    (hA : 2 ≤ A) (hx : 0 ≤ x) (hcount : (count : ℝ) ≤ x) :
    let b := preparedFiniteForwardParameter A stageCountConstant n x
    let w := preparedFiniteForwardWork A stageCountConstant n x
    0 ≤ w ∧ b ≤ w ∧ (count : ℝ) ≤ Real.exp w ∧ b * count ≤ w := by
  intro b w
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hw : 0 ≤ w := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hxb : x ≤ b := le_preparedFiniteForwardParameter A stageCountConstant n hx
  have hshift : b ≤ b + A := le_add_of_nonneg_right (Nat.cast_nonneg A)
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hbase : 1 ≤ b + A := by linarith only [hb, hAreal]
  have hbw : b ≤ w := by
    rw [show w = (b + A) ^ A from preparedFiniteForwardWork_eq A stageCountConstant n x]
    have hAone : 1 ≤ A := by omega
    have hpower : b + A ≤ (b + A) ^ A := by
      simpa only [pow_one] using (pow_le_pow_right₀ hbase hAone)
    exact hshift.trans hpower
  have hsquare : b ^ 2 ≤ w := by
    rw [show w = (b + A) ^ A from preparedFiniteForwardWork_eq A stageCountConstant n x]
    exact (pow_le_pow_left₀ hb hshift 2).trans (pow_le_pow_right₀ hbase hA)
  refine ⟨hw, hbw, ?_, ?_⟩
  · have hc : (count : ℝ) ≤ w := hcount.trans (hxb.trans hbw)
    have he := Real.add_one_le_exp w
    linarith only [hc, he]
  · exact (mul_le_mul_of_nonneg_left (hcount.trans hxb) hb).trans
      (by simpa only [pow_two] using hsquare)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForward_controlled_slice_bounds
    (A Cslice : ℕ) (stageCountConstant : ℕ → ℕ) (n count : ℕ) {x : ℝ}
    (hA : 2 ≤ A) (hC : Cslice + 1 ≤ A)
    (hx : 0 ≤ x) (hcount : (count : ℝ) ≤ x) :
    let b := preparedFiniteForwardParameter A stageCountConstant n x
    let w := preparedFiniteForwardWork A stageCountConstant n x
    let pSlice := (b + Cslice) ^ Cslice
    0 ≤ pSlice ∧ pSlice ≤ w ∧ pSlice * count ≤ w := by
  intro b w pSlice
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hA' : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hCnat : Cslice ≤ A := (Nat.le_succ _).trans hC
  have hC' : (Cslice : ℝ) ≤ A := Nat.cast_le.mpr hCnat
  have hbase : 1 ≤ b + A := by linarith only [hb, hA']
  have hbase0 : 0 ≤ b + A := le_trans (by norm_num) hbase
  have hslice0 : 0 ≤ pSlice := pow_nonneg (add_nonneg hb (Nat.cast_nonneg Cslice)) Cslice
  have hpow : pSlice ≤ (b + A) ^ Cslice :=
    pow_le_pow_left₀ (add_nonneg hb (Nat.cast_nonneg Cslice))
      (add_le_add (le_refl b) hC') Cslice
  have hcb : (count : ℝ) ≤ b + A := by
    have hxb : x ≤ b := le_preparedFiniteForwardParameter A stageCountConstant n hx
    have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    linarith only [hcount, hxb, hA0]
  have hw : w = (b + A) ^ A := preparedFiniteForwardWork_eq A stageCountConstant n x
  refine ⟨hslice0, hpow.trans ?_, ?_⟩
  · rw [hw]
    exact pow_le_pow_right₀ hbase hCnat
  · rw [hw]
    calc
      pSlice * count ≤ (b + A) ^ Cslice * (b + A) :=
        mul_le_mul hpow hcb (Nat.cast_nonneg count) (pow_nonneg hbase0 Cslice)
      _ = (b + A) ^ (Cslice + 1) := (pow_succ _ _).symm
      _ ≤ (b + A) ^ A := pow_le_pow_right₀ hbase hC

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem le_preparedFiniteForwardCumulative
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (depth : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (hA : 1 ≤ A) (hdepth : 0 < depth) :
    x ≤ preparedFiniteForwardCumulative A stageCountConstant depth x := by
  have hcap : x ≤ preparedFiniteForwardCap A stageCountConstant 0 x := by
    rw [preparedFiniteForwardCap_eq, preparedFiniteForwardParameter_zero]
    have hw := preparedFiniteForwardWork_nonneg A stageCountConstant 0 hx
    have hbase : 1 ≤ 4 * x +
        4 * preparedFiniteForwardWork A stageCountConstant 0 x + 16 + A := by
      linarith only [hx, hw, Nat.cast_nonneg (α := ℝ) A]
    have hshift : x ≤ 4 * x +
        4 * preparedFiniteForwardWork A stageCountConstant 0 x + 16 + A := by
      linarith only [hx, hw, Nat.cast_nonneg (α := ℝ) A]
    exact hshift.trans (by simpa only [pow_one] using pow_le_pow_right₀ hbase hA)
  exact hcap.trans (preparedFiniteForwardCap_le_cumulative A stageCountConstant hx hdepth)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedFiniteForwardPairedSourcePrecision
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    (x gainLog stageLog : ℝ) : ℝ :=
  preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
    if isDirect then
      (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + Cdirect) ^ Cdirect
    else 0

@[simp] theorem preparedFiniteForwardPairedSourcePrecision_model
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x gainLog stageLog : ℝ) :
    preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n false x gainLog stageLog =
      preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog := by
  simp only [preparedFiniteForwardPairedSourcePrecision, Bool.false_eq_true, ↓reduceIte, add_zero]

@[simp] theorem preparedFiniteForwardPairedSourcePrecision_direct
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x gainLog stageLog : ℝ) :
    preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n true x gainLog stageLog =
      preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
          preparedFiniteForwardWork A stageCountConstant n x + Cdirect) ^ Cdirect := by
  simp only [preparedFiniteForwardPairedSourcePrecision, ↓reduceIte]

theorem preparedFiniteForwardPairedSourcePrecision_nonneg
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    0 ≤ preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n isDirect x gainLog stageLog := by
  have hsource := (preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs).2.1
  have hwork := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  cases isDirect <;> simp only [preparedFiniteForwardPairedSourcePrecision_model,
    preparedFiniteForwardPairedSourcePrecision_direct] <;> positivity

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedUniformEarlyRadiusWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedFiniteForward_shiftedPower_le_work (A C : ℕ)
    (stageCountConstant : ℕ → ℕ) (stage : ℕ) {x : ℝ}
    (hA : 2 ≤ A) (hC : C ≤ A) (hx : 0 ≤ x) :
    (x + C) ^ C ≤ preparedFiniteForwardWork A stageCountConstant stage x := by
  have hp := preparedFiniteForwardParameter_nonneg A stageCountConstant stage hx
  have hxp := le_preparedFiniteForwardParameter A stageCountConstant stage hx
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hCreal : (C : ℝ) ≤ A := Nat.cast_le.mpr hC
  rw [preparedFiniteForwardWork_eq]
  exact (pow_le_pow_left₀ (add_nonneg hx (Nat.cast_nonneg C))
    (add_le_add hxp hCreal) C).trans
      (pow_le_pow_right₀ (by linarith only [hp, hAreal]) hC)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem slicedFixedUniformSitePolynomial_eval (m : ℕ) (p E : Polynomial ℕ) (x : ℝ) :
    (slicedFixedUniformSitePolynomial m p E).eval₂ (Nat.castRingHom ℝ) x =
      slicedFixedUniformSiteLog m (p.eval₂ (Nat.castRingHom ℝ) x) (E.eval₂ (Nat.castRingHom ℝ) x) := by
  simp only [slicedFixedUniformSitePolynomial, slicedFixedUniformSiteLog,
    Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_finsetSum, slicedGridSiteLog_eval]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceSubtypeSites
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {N : I → ℕ} {q : ℕ}

theorem subtypeSites_image_val (A : ResidueBoxSlice N q) :
    A.subtypeSites.image Subtype.val = A.integerPoints := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact (A.mem_subtypeSites t).mp ht
  · intro hx
    exact Finset.mem_image.mpr ⟨⟨x, A.integerPoints_subset_integerBox hx⟩,
      (A.mem_subtypeSites _).mpr hx, rfl⟩

theorem expect_subtypeSites (A : ResidueBoxSlice N q)
    {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V] (f : (I → ℤ) → V) :
    (𝔼 t ∈ A.subtypeSites, f t.val) = 𝔼 x ∈ A.integerPoints, f x := by
  classical
  rw [← A.subtypeSites_image_val]
  exact (Finset.expect_image Subtype.val_injective.injOn).symm

theorem subtypeSites_nonempty_of_integerPoints (A : ResidueBoxSlice N q)
    (h : A.integerPoints.Nonempty) : A.subtypeSites.Nonempty := by
  classical
  rw [← A.subtypeSites_image_val, Finset.image_nonempty] at h
  exact h

theorem subtypeSites_dense (A : ResidueBoxSlice N q) {cost : ℝ}
    (h : IsDenseCommonStrideBox N cost A.integerPoints) :
    IsDenseCommonStrideBox N cost (A.subtypeSites.image Subtype.val) := by
  classical
  rw [A.subtypeSites_image_val]
  exact h

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateOptionJointConclusion
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

variable {I : Type*} [Fintype I] [DecidableEq I] {N : I → ℕ} {q : ℕ}

theorem length_gt_of_dense_exp_side (Q : ResidueBoxSlice N q)
    (hq : 0 < q) {densityCost : ℝ}
    (hdense : IsDenseCommonStrideBox N densityCost Q.integerPoints)
    (degree : ℕ) (i : I)
    (hside : Real.exp densityCost * ((degree + 1 : ℕ) : ℝ) ≤ (N i : ℝ)) :
    degree < Q.length i := by
  have hlength := Q.length_lower_of_dense hq hdense i
  have h := mul_le_mul_of_nonneg_left hside (Real.exp_nonneg (-densityCost))
  have hexp : Real.exp (-densityCost) * Real.exp densityCost = 1 := by
    rw [← Real.exp_add]
    simp
  rw [← mul_assoc, hexp, one_mul] at h
  have hnat : degree + 1 ≤ Q.length i := by exact_mod_cast h.trans hlength
  omega

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FullTaggedRationalRetraction
namespace OAI

section

namespace Erdos3

variable {T S : Type*} [Fintype T] [Fintype S]

theorem rationalMatrix_real_range_eq_coordinateSpan (P : Matrix T S ℚ) :
    LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
      realRationalCoordinateSpan (LinearMap.range P.mulVecLin) := by
  rw [Matrix.range_mulVecLin P]
  exact (Matrix.range_mulVecLin (Matrix.of (fun i j => (P i j : ℝ)))).trans
    (realRationalCoordinateSpan_span P.col).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformExternalMarkedAffineSliceFreezingDictionary
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

variable {ι : Type*} {N : ι → ℕ} {q : ℕ}

def affineIntegerPoint (A : ResidueBoxSlice N q) (origin : ι → ℤ) (step : ℕ)
    (j : ∀ i, Fin (A.length i)) : ι → ℤ :=
  fun i => origin i + step * (A.point j i).val

theorem affineIntegerPoint_residue (A : ResidueBoxSlice N q)
    (origin : ι → ℤ) (step : ℕ) (j : ∀ i, Fin (A.length i)) :
    (fun i => (A.affineIntegerPoint origin step j i : ZMod q)) =
      fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q) := by
  funext i
  simp only [affineIntegerPoint, point, Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul,
    Int.cast_natCast]
  simp

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3
open scoped BigOperators

theorem exists_long_affine_residue_cell_frozen_score_with_cell
    {ι I J : Type*} [Fintype ι] [DecidableEq ι] (N : ι → ℕ)
    (hN : ∀ i, 0 < N i) (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q)
    (origin : ι → ℤ) (step : ℕ) (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    (hparent : ∀ i n, n < N i → |(origin i : ℝ) + step * n| ≤ T i)
    (hparentwidth : ∀ i, (step : ℝ) * N i ≤ 2 * T i)
    (hlarge : ∀ i, 2 * (q : ℝ) ≤ (1 / (Q : ℝ)) * N i)
    (score : (ι → ℤ) → ℝ) (f : (ι → ℤ) → ℂ)
    (frozen : I → J → (ι → ℤ) → ℂ)
    (leftLabel : (ι → Fin (Q + 1)) → I) (rightLabel : (ι → ZMod q) → J)
    {B τ ε θ S : ℝ} (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hθ : 0 < θ)
    (hscoreBound : ∀ x : ι → ℤ, (∀ i, |(x i : ℝ)| ≤ T i) → |score x| ≤ 1)
    (hcap : ∀ x : ι → ℤ, (∀ i, |(x i : ℝ)| ≤ T i) → score x * (f x).re ≤ B)
    (hfreeze : ∀ a (x : ι → ℤ), (∀ i, |(x i : ℝ)| ≤ T i) →
      (∀ i, |(x i : ℝ) - normalizedRealBoxGrid T Q a i| ≤ T i * (2 / Q)) →
      ‖f x - frozen (leftLabel a) (rightLabel (fun i => (x i : ZMod q))) x‖ ≤ ε)
    (hscore : S ≤ 𝔼 x : (∀ i, Fin (N i)),
      score (affineParentIntegerPoint N origin step x) *
        (f (affineParentIntegerPoint N origin step x)).re)
    (hbudget : τ + ε + B * θ < S) :
    ∃ A : ResidueBoxSlice N q, (∀ i, 0 < A.length i) ∧
      (∀ i, θ * N i / (4 * q * Q * (Fintype.card ι + 1 : ℝ)) ≤ A.length i) ∧
      ∃ z : ι → Fin (Q + 1),
        (∀ (j : ∀ i, Fin (A.length i)) i,
          |(A.affineIntegerPoint origin step j i : ℝ) -
            normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q)) ∧
        (∀ j : ∀ i, Fin (A.length i),
          ‖f (A.affineIntegerPoint origin step j) -
            frozen (leftLabel z)
              (rightLabel (fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q)))
              (A.affineIntegerPoint origin step j)‖ ≤ ε) ∧
        τ < 𝔼 j : (∀ i, Fin (A.length i)),
          score (A.affineIntegerPoint origin step j) *
            (frozen (leftLabel z)
              (rightLabel (fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q)))
              (A.affineIntegerPoint origin step j)).re := by
  classical
  let point := affineParentIntegerPoint N origin step
  let residue := fun r : ι → ZMod q => fun i => (origin i : ZMod q) + (step : ZMod q) * r i
  let V := fun r z x => (frozen (leftLabel z) (rightLabel (residue r)) (point x)).re
  have hbound (x : ∀ i, Fin (N i)) (i) : |(point x i : ℝ)| ≤ T i := by
    simpa only [point, affineParentIntegerPoint, Int.cast_add, Int.cast_mul,
      Int.cast_natCast] using hparent i (x i).val (x i).isLt
  have hclose (r : ι → ZMod q) (z : ι → Fin (Q + 1)) (x : ∀ i, Fin (N i))
      (hr : ∀ i, ((x i).val : ZMod q) = r i)
      (hz : ∀ i, |(origin i : ℝ) + (step : ℝ) * (x i).val -
        normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q)) :
      dist (f (point x)).re (V r z x) ≤ ε := by
    have hres : (fun i => (point x i : ZMod q)) = residue r := by
      funext i
      simp only [point, affineParentIntegerPoint, Int.cast_add, Int.cast_mul,
        Int.cast_natCast, hr, residue]
    have hcell (i) : |(point x i : ℝ) - normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q) := by
      simpa only [point, affineParentIntegerPoint, Int.cast_add, Int.cast_mul,
        Int.cast_natCast] using hz i
    have hn := hfreeze z (point x) (hbound x) hcell
    rw [hres] at hn
    exact (show dist (f (point x)).re (V r z x) ≤
        ‖f (point x) - frozen (leftLabel z) (rightLabel (residue r)) (point x)‖ by
      simpa only [Real.dist_eq, V, Complex.sub_re] using
        Complex.abs_re_le_norm (f (point x) -
          frozen (leftLabel z) (rightLabel (residue r)) (point x))).trans hn
  obtain ⟨A, hlen, hlong, r, z, hr, hz, hs⟩ := exists_long_residue_cell_frozen_score
    N hN q Q hq hQ (fun i => (origin i : ℝ)) (step : ℝ) (Nat.cast_nonneg _)
    T hT hparent hparentwidth hlarge (fun x => score (point x)) (fun x => (f (point x)).re)
    V hB hτ hε hθ (fun x => hscoreBound (point x) (hbound x))
    (fun x => hcap (point x) (hbound x)) hclose hscore hbudget
  let jzero : ∀ i, Fin (A.length i) := fun i => ⟨0, hlen i⟩
  have hrstart : ∀ i, (A.start i : ZMod q) = r i := by
    intro i
    simpa only [ResidueBoxSlice.point, jzero, Nat.mul_zero, Nat.add_zero] using hr jzero i
  have hresidue : residue r =
      fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q) := by
    funext i
    simp only [residue, Int.cast_add, Int.cast_mul, Int.cast_natCast, hrstart]
  have hcell (j : ∀ i, Fin (A.length i)) (i) :
      |(A.affineIntegerPoint origin step j i : ℝ) -
        normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q) := by
    simpa only [ResidueBoxSlice.affineIntegerPoint, Int.cast_add, Int.cast_mul,
      Int.cast_natCast] using hz j i
  refine ⟨A, hlen, hlong, z, hcell, ?_, ?_⟩
  · intro j
    have hn := hfreeze z (A.affineIntegerPoint origin step j) (hbound (A.point j)) (hcell j)
    simpa only [A.affineIntegerPoint_residue origin step j] using hn
  · dsimp only [V] at hs
    rw [hresidue] at hs
    exact hs

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} {N : I → ℕ} {q r : ℕ}

theorem composeSlice_integerPoint (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (j : ∀ i, Fin (T.length i)) :
    (S.composeSlice T).integerPoint j = S.integerPoint (T.point j) := by
  unfold integerPoint
  rw [S.composeSlice_point T]

theorem composeSlice_integerPoint_affine (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (j : ∀ i, Fin (T.length i)) :
    (S.composeSlice T).integerPoint j =
      T.affineIntegerPoint (fun i => (S.start i : ℤ)) q j := by
  rw [S.composeSlice_integerPoint T]
  funext i
  simp only [integerPoint, point, affineIntegerPoint, Nat.cast_add, Nat.cast_mul]

variable [Fintype I] [DecidableEq I]

theorem composeSlice_integerPoints_eq_affine_image (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) :
    (S.composeSlice T).integerPoints =
      Finset.univ.image (T.affineIntegerPoint (fun i => (S.start i : ℤ)) q) := by
  unfold integerPoints
  apply Finset.image_congr
  intro j _
  exact S.composeSlice_integerPoint_affine T j

theorem composeSlice_integerPoints_subset (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) :
    (S.composeSlice T).integerPoints ⊆ S.integerPoints := by
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr
    ⟨T.point j, Finset.mem_univ _, (S.composeSlice_integerPoint T j).symm⟩

theorem expect_composeSlice_integerPoints (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (hq : 0 < q) (hr : 0 < r)
    {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V] (f : (I → ℤ) → V) :
    (𝔼 x ∈ (S.composeSlice T).integerPoints, f x) =
      𝔼 j : (∀ i, Fin (T.length i)),
        f (T.affineIntegerPoint (fun i => (S.start i : ℤ)) q j) := by
  rw [(S.composeSlice T).expect_integerPoints (Nat.mul_pos hq hr) f]
  apply Finset.expect_congr rfl
  intro j _
  exact congrArg f (S.composeSlice_integerPoint_affine T j)

theorem composeSlice_isDenseCommonStrideBox (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (hq : 0 < q) (hr : 0 < r)
    {cost loss : ℝ} (hS : IsDenseCommonStrideBox N cost S.integerPoints)
    (hT : ∀ i, (S.length i : ℝ) * Real.exp (-loss) ≤ (T.length i : ℝ)) :
    IsDenseCommonStrideBox N (cost + loss) (S.composeSlice T).integerPoints := by
  refine ⟨fun i => ((S.composeSlice T).start i : ℤ), q * r,
    (S.composeSlice T).length, Nat.mul_pos hq hr, ?_,
    (S.composeSlice T).progression_inside, ?_,
    (S.composeSlice T).integerPoints_eq_commonStrideBox⟩
  · intro i
    have hpos : (0 : ℝ) < T.length i :=
      (mul_pos (Nat.cast_pos.mpr (S.length_pos_of_dense hS i))
        (Real.exp_pos _)).trans_le (hT i)
    exact_mod_cast hpos
  · exact S.composeSlice_length_lower T (S.length_lower_of_dense hq hS) hT

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMarkedFreezingPhysicalData
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem nativeMarkedFreezingPhysicalParameter_bounds {p : ℝ} (hp : 0 ≤ p) (C : ℕ) :
    p ≤ nativeMarkedFreezingPhysicalParameter p C ∧
      (p + C) ^ C ≤ nativeMarkedFreezingPhysicalParameter p C ∧
      (p + 3) ^ 7 ≤ nativeMarkedFreezingPhysicalParameter p C ∧
      p + 1 ≤ nativeMarkedFreezingPhysicalParameter p C := by
  have hbase : 1 ≤ p + 3 := by linarith
  have hpow : (p + 3) ^ 7 ≤ (p + 3) ^ 36 := pow_le_pow_right₀ hbase (by decide)
  have hinput : p + 1 ≤ (p + 3) ^ 36 := by
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      (le_power_budget (show 0 ≤ p + 1 by linarith) (by decide : 1 ≤ 36))
  have hbudget : 0 ≤ (p + C) ^ C := by positivity
  have hfirst : (p + 3) ^ 36 ≤ nativeMarkedFreezingPhysicalParameter p C :=
    le_add_of_nonneg_right hbudget
  refine ⟨(by linarith [hinput.trans hfirst]), ?_, hpow.trans hfirst, hinput.trans hfirst⟩
  exact le_add_of_nonneg_left (by positivity)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ConcreteAffineMeshBoundary
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def integerBoxMesh (lo hi : I → ℤ)
    (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (z : ∀ i, Finset.Ico (lo i) (hi i)) : ∀ i, (P i).Label :=
  physicalBoxCell lo (fun i => (hi i - lo i).toNat) P (integerBoxMeshPoint lo hi z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedTrimmedSliceFamily
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

namespace ResidueBoxSlice
variable {J : Type*} [Fintype J] [decJ : DecidableEq J] {N : J → ℕ} {q : ℕ}

noncomputable def scalarParameterEquiv (S : ResidueBoxSlice N q) :
    (∀ j, Finset.Ico (0 : ℤ) (S.length j : ℤ)) ≃ (∀ j, Fin (S.length j)) where
  toFun x j := ⟨(x j).val.toNat, by
    have := Finset.mem_Ico.mp (x j).property
    omega⟩
  invFun t j := ⟨((t j).val : ℤ), by
    exact Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by exact_mod_cast (t j).isLt⟩⟩
  left_inv x := by
    funext j
    apply Subtype.ext
    have := (Finset.mem_Ico.mp (x j).property).1
    exact Int.toNat_of_nonneg this
  right_inv t := by
    funext j
    apply Fin.ext
    simp

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelPrincipalFiberSliceLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G D : Type*} [Fintype G] [DecidableEq G] [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (LG : G → ℕ) (L : PrincipalTupleIndex B h → ℕ)

namespace ResidueBoxSlice

variable {B h LG L}
variable {keep : G ⊕ PrincipalTupleIndex B h → Prop} [DecidablePred keep] {q : ℕ}
variable (S : ResidueBoxSlice (fun k : {k // keep k} => Sum.elim LG L k.val) q)
variable (hlen : ∀ k, 0 < S.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < ((Sum.elim LG L k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

omit [Fintype G] [DecidableEq G] [Fintype D] [DecidableEq D]
  [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] [DecidablePred keep] in
theorem fiberKernelProgression_contained (g : G) :
    integerProgressionSupport (S.start ⟨Sum.inl g, hkernel g⟩ : ℤ) (q : ℤ)
        (S.length ⟨Sum.inl g, hkernel g⟩) ⊆ Finset.Ico (0 : ℤ) (LG g : ℤ) := by
  apply integerProgressionSupport_subset_of_fin
  intro t
  constructor
  · positivity
  · exact_mod_cast S.inside ⟨Sum.inl g, hkernel g⟩ t.val t.isLt

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagProjectionComplement
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {T : Type*} [Fintype T]

theorem rationalTagProjectionComplement_ker
    (P : Matrix T T ℚ) (V : Submodule ℚ (T → ℚ))
    (hrange : LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
      realRationalCoordinateSpan V)
    (hfix : ∀ x ∈ realRationalCoordinateSpan V,
      Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = x) :
    LinearMap.ker (rationalTagProjectionComplement P) = realRationalCoordinateSpan V := by
  ext x
  change x - Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = 0 ↔
    x ∈ realRationalCoordinateSpan V
  constructor
  · intro hx
    rw [sub_eq_zero] at hx
    rw [hx, ← hrange]
    exact ⟨x, rfl⟩
  · intro hx
    rw [hfix x hx, sub_self]

theorem rationalTagProjectionComplement_idempotent
    (P : Matrix T T ℚ) (V : Submodule ℚ (T → ℚ))
    (hrange : LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
      realRationalCoordinateSpan V)
    (hfix : ∀ x ∈ realRationalCoordinateSpan V,
      Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = x)
    (x : T → ℝ) :
    rationalTagProjectionComplement P (rationalTagProjectionComplement P x) =
      rationalTagProjectionComplement P x := by
  let L := Matrix.mulVecLin (fun i j => (P i j : ℝ))
  have hmem : L x ∈ realRationalCoordinateSpan V := by
    rw [← hrange]
    exact ⟨x, rfl⟩
  have hLL : L (L x) = L x := hfix _ hmem
  change x - L x - L (x - L x) = x - L x
  rw [map_sub, hLL, sub_self, sub_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseCanonicalTopology
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open PolynomialTranslationLie
open scoped TensorProduct

@[instance_reducible]
noncomputable def canonicalTopology (s : ℕ) :
    TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra weight s) :=
  moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)

theorem canonicalTopologicalAddGroup (s : ℕ) :
    letI := canonicalTopology s
    IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight s) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)
  exact IsModuleTopology.topologicalAddGroup ℝ _

theorem canonicalContinuousSMul (s : ℕ) :
    letI := canonicalTopology s
    ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)
  infer_instance

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedFiniteForwardPolynomialCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteForward_polynomial_cap (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog : ℝ}, C ≤ A → 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      P.eval₂ (Nat.castRingHom ℝ)
        (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
          preparedFiniteForwardWork A stageCountConstant n x) ≤
        preparedFiniteForwardCap A stageCountConstant n x := by
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro A stageCountConstant n x gainLog stageLog hCA hx hg hs
  have hprec := preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs
  have hw := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  exact (hpoly _ (add_nonneg hprec.2.1 hw)).trans
    (preparedFiniteForward_phase_cap A stageCountConstant n C hx hg hs hCA)

theorem exists_preparedFiniteForward_composed_phase_cap (Cnative Cmajor : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog pMajor : ℝ}, C ≤ A → 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x → 0 ≤ pMajor →
      pMajor ≤ (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + Cnative) ^ Cnative →
      (pMajor + Cmajor) ^ Cmajor ≤ preparedFiniteForwardCap A stageCountConstant n x := by
  let P : Polynomial ℕ := ((Polynomial.X + Polynomial.C Cnative) ^ Cnative +
    Polynomial.C Cmajor) ^ Cmajor
  obtain ⟨C, hC, hpoly⟩ := exists_preparedFiniteForward_polynomial_cap P
  refine ⟨C, hC, ?_⟩
  intro A stageCountConstant n x gainLog stageLog pMajor hCA hx hg hs hp hbound
  apply le_trans (pow_le_pow_left₀ (add_nonneg hp (Nat.cast_nonneg Cmajor))
    (add_le_add hbound (le_refl (Cmajor : ℝ))) Cmajor)
  simpa [P, Polynomial.eval₂_pow] using hpoly A stageCountConstant n hCA hx hg hs

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialSliceInterpolation
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ V : Type*} [Finite σ] [AddCommGroup V] [Module ℚ V]
  [Module ℝ V] [IsScalarTower ℚ ℝ V]

theorem eq_of_eval₂_eq_on_residueBoxSlice
    {N : σ → ℕ} {step : ℕ} (A : ResidueBoxSlice N step) (hstep : 0 < step)
    {d : ℕ} {p q : VectorPolynomial σ ℚ V}
    (hp : DegreeLE (fun _ => 1) d p) (hq : DegreeLE (fun _ => 1) d q)
    (hlen : ∀ i, d < A.length i)
    (heval : ∀ j : ∀ i, Fin (A.length i),
      eval₂ (fun i => (A.integerPoint j i : ℝ)) p =
        eval₂ (fun i => (A.integerPoint j i : ℝ)) q) :
    p = q := by
  refine eq_of_eval₂_eq_on_grid A.length
    (fun i j => ((A.start i + step * j.val : ℕ) : ℝ)) ?_ hp hq hlen ?_
  · intro i j k h
    apply Fin.ext
    dsimp only at h
    have hnat : A.start i + step * j.val = A.start i + step * k.val := by
      exact_mod_cast h
    exact Nat.eq_of_mul_eq_mul_left hstep (Nat.add_left_cancel hnat)
  · intro j
    simpa only [ResidueBoxSlice.integerPoint, ResidueBoxSlice.point, Int.cast_natCast]
      using heval j

end Erdos3.VectorPolynomial

end

end OAI
end


