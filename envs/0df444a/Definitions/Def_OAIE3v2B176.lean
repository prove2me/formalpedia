-- Prove2me | Definitions.Def_OAIE3v2B176
-- name    : OAIE3v2B176
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:37:46.410496+00:00
-- url     : https://prove2.me/theorems/e0566883-5654-46e6-977b-bd2c0a462f4f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 178 of 311
-- statement:
--   Definitions bundle 178 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B152`, `OAIE3v2B157`, `OAIE3v2B158`, `OAIE3v2B159` of this split.
--
--   Modules: `Dynamics/PreparedFiniteForwardLaterWorkBudget.lean`, `Dynamics/PreparedFiniteForwardPairedResourceBudget.lean`, `Estimates/AllocatedEnormousProfiles.lean`, `Estimates/NativeFrozenComparison.lean`, `Estimates/NativeOrbitOuterControl.lean`, `Estimates/OptionMarkedSurjective.lean`, `Estimates/PreparedFiniteForwardFixedCenterThreshold.lean`, `Estimates/PreparedFiniteNestedSourceArrays.lean`, `Estimates/PreparedScalarNestedPowerDetection.lean`, `Estimates/RefilteredReconstructionDiagram.lean`, `Estimates/SampledNativeModel.lean`, `Estimates/StrongRefiltrationReconstruction.lean`, `Fourier/AnchoredCoefficientFourierNormalization.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeBudget.lean`, `Geometry/CenteredCoefficientDeckChartMeasurable.lean`, `Geometry/PhysicalFactorCoordinates.lean`, `Lattices/AffineCoefficientAmplitudeCongruenceRemoval.lean`, `Lattices/AffineCoefficientAmplitudeDensityTest.lean`, `Lattices/ResidueBoxSliceCoordinateDisintegration.lean`, `Lattices/UniformExternalMarkedAffineSliceFreezingDictionary.lean`, `Linear/AllocatedKernelScaleWithCutoff.lean`, `Linear/AllocatedModularRankActualRead.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/ExternalKernelPrecenterNativePointPartners.lean`, `Linear/JointFrameCoefficientCoverSample.lean`, `Linear/RationalTagProjectionComplement.lean`, `Linear/SpatialMatrixBlockWideProbability.lean`, `Polynomial/PreparedFiniteNestedForwardAllDegreePaddedSource.lean`, `Probability/AllocatedDensityParameterBounds.lean`, `Probability/AllocatedFixedPositiveDensity.lean`, `Probability/AllocatedJointMaskedDensityComparison.lean`, `Probability/AllocatedProgressionDensityIdentity.lean`, `Probability/PositiveDensityNormalization.lean`, `Sampling/PrecenterForecastNativeAtomDictionary.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B152
import Definitions.Def_OAIE3v2B157
import Definitions.Def_OAIE3v2B158
import Definitions.Def_OAIE3v2B159

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientAmplitudeCongruenceRemoval
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem exists_affine_coefficient_amplitude_residue_uniform_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (F : (Option K × I → ℝ) → ℂ) (_hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (_hLip : LipschitzWith Lip F) (_hLipP : (Lip : ℝ) ≤ Real.exp P),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      (F (fun t => (residueLatticeArray residue stride z t : ℝ) / V t) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ)))‖ ≤ ε := by
  obtain ⟨A₀, _, hbudget⟩ := exists_mode_residue_threshold_exp_budget m
  obtain ⟨A, hA, habsorb⟩ := exists_natPolynomial_eval_budget
    ((2 * Polynomial.X + 2 + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth F hF Lip hLip hLipP
  let P' := 2 * P + 2
  have hPP : P ≤ P' := by dsimp [P']; linarith
  have hP' : 0 ≤ P' := hP.trans hPP
  have hExp := Real.exp_le_exp.mpr hPP
  have hacc := modeAmplitudeAccuracy_pos Lip.coe_nonneg hε
  have haccexp : 1 / modeAmplitudeAccuracy Lip ε ≤ Real.exp P' :=
    modeAmplitudeAccuracy_inv_le_exp hP Lip.coe_nonneg hLipP hε hεP
  have hcut : (P' + A₀) ^ A₀ ≤ (P + A) ^ A := by
    simpa [P', Polynomial.eval₂_pow] using habsorb P hP
  obtain ⟨hside, hrankBudget⟩ := hbudget (Fintype.card I) (Fintype.card (Option K × I))
    P' C 1 S ρ (modeAmplitudeAccuracy Lip ε) hP' (hn.trans hPP) (hd.trans hPP)
    hC (hCP.trans hExp) zero_le_one (Real.one_le_exp hP') hS (hSP.trans hExp)
    hρ (hρP.trans hExp) hacc haccexp
  exact affine_coefficient_amplitude_residue_removal_at_error U hC frequency hbound hbad
    p hp hm stride hs hS hρ hε hstride F hF hLip H
    (fun k => hside.trans ((Real.exp_le_exp.mpr hcut).trans (hsize k))) hrank
    (hrankBudget.trans ((Real.exp_le_exp.mpr hcut).trans hR)) residue V hV hwidth

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem exists_affine_coefficient_amplitude_ambient_residue_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (F : (Option K × I → ℝ) → ℂ) (_hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (_hLip : LipschitzWith Lip F) (_hLipP : (Lip : ℝ) ≤ Real.exp P),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      (F (fun t => (z t : ℝ) / V t) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (z (k, j) : ℝ)))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_coefficient_amplitude_residue_uniform_removal m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth F hF Lip hLip hLipP
  obtain ⟨hZ, hrem⟩ := hremove hP hn hd U hC hCP frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth F hF hLip hLipP
  refine ⟨hZ, ?_⟩
  rw [residueSmoothPMF_expectation]
  exact hrem

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem exists_affine_coefficient_amplitude_congruence_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (F : (Option K × I → ℝ) → ℂ) (_hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (_hLip : LipschitzWith Lip F) (_hLipP : (Lip : ℝ) ≤ Real.exp P),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
      (F (fun t => (z t : ℝ) / V t) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (z (k, j) : ℝ)))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_coefficient_amplitude_ambient_residue_removal m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR G hG V hV hwidth F hF Lip hLip hLipP
  have hh (r : G) := hremove hP hn hd U hC hCP frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR (columnResidueRepresentative stride r.val) V hV hwidth F hF hLip hLipP
  choose hZ hrem using hh
  exact selectedResidueSmoothPMF_bound_of_cells stride hs G hG V hV hZ _ hrem

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AnchoredCoefficientFourierNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_affine_coefficient_amplitude_fourier_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
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
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (amplitude : (Option K × I → ℝ) → ℂ) (_hamp : ∀ x, ‖amplitude x‖ ≤ 1)
    {Lip : ℝ≥0} (_hLip : LipschitzWith Lip amplitude) (_hLipP : (Lip : ℝ) ≤ Real.exp P),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (amplitude (fun t => (z t : ℝ) / V t) * ∑ a, c a * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
          p (fun k j => (z (k, j) : ℝ)))) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        amplitude (fun t => (z t : ℝ) / V t)) *
      (∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0)‖ ≤ ε := by
  classical
  obtain ⟨A₀, _, hremove⟩ := exists_affine_coefficient_amplitude_congruence_removal m
  obtain ⟨A₁, _, hthreshold⟩ := exists_mode_residue_threshold_exp_budget m
  obtain ⟨A, hA, hbudget⟩ := exists_fourier_uniform_budget A₀ A₁
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth amplitude hamp Lip hLip hLipP
  let P' := 2 * P + 2
  let δ := fourierModeError B ε
  have hPP : P ≤ P' := by dsimp [P']; linarith
  have hEP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP
  have hδ : 0 < δ := fourierModeError_pos hB hε
  have hδP : 1 / δ ≤ Real.exp P' := fourierModeError_inv_le_exp hP hB hBP hε hεP
  obtain ⟨hb₀, hb₁⟩ := hbudget P hP
  obtain ⟨hside, _⟩ := hthreshold (Fintype.card I) (Fintype.card (Option K × I))
    P' C 1 S ρ δ (hP.trans hPP) (hn.trans hPP) (hd.trans hPP) hC (hCP.trans hEP)
    zero_le_one (Real.one_le_exp (hP.trans hPP)) hS (hSP.trans hEP) hρ (hρP.trans hEP) hδ hδP
  have hZ := selectedResidueSmoothWeight_pos_of_threshold m zero_le_one
    hS hρ hδ stride hs hstride H (fun j => hside.trans (hb₁.trans (hsize j))) G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  have hdiscard (a : F) (hbad : ¬affineCoefficientModeTrivial U (frequency a)) :
      ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (amplitude (fun t => (z t : ℝ) / V t) * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
          p (fun k j => (z (k, j) : ℝ)))‖ ≤ δ := by
    obtain ⟨_, hr⟩ := hremove (hP.trans hPP) (hn.trans hPP) (hd.trans hPP)
      U hC (hCP.trans hEP) (frequency a) (hbound a)
      ((not_affineCoefficientModeTrivial_iff U (frequency a)).mp hbad)
      p hp hm stride hs hS (hSP.trans hEP) hρ hδ (hρP.trans hEP) hδP hstride
      H (fun j => hb₀.trans (hsize j)) hrank (hb₀.trans hR) G hG V hV hwidth
      amplitude hamp hLip (hLipP.trans hEP)
    exact hr
  have hproj := selectedResidueSmoothPMF_weighted_fourier_normalization stride G V hV hZ
    (fun z => amplitude (fun t => (z t : ℝ) / V t)) c
    (fun a z => layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
      p (fun k j => (z (k, j) : ℝ)))
    (fun a => affineCoefficientModeTrivial U (frequency a)) hcoefficients hδ.le
    (fun a ha z => layeredCoefficientCharacter_eq_one_of_trivial U (frequency a) ha p hp hm
      (fun k j => (z (k, j) : ℝ))) hdiscard
  exact hproj.trans (fourierModeError_cost_le hB hε)

end Erdos3.VectorPolynomial

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

theorem finiteSplitPoint_mem_integerPoints
    (A : ResidueBoxSlice N q) (keep : I → Prop)
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i : {i // ¬keep i},
      fixed i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i))
    {x : {i // keep i} → ℤ} (hx : x ∈ (A.coordinateProjection keep).integerPoints) :
    finiteSplitPoint keep x fixed ∈ A.integerPoints := by
  apply (A.mem_integerPoints_iff _).mpr
  have hx' := ((A.coordinateProjection keep).mem_integerPoints_iff x).mp hx
  intro i
  by_cases hi : keep i
  · simpa only [finiteSplitPoint, dif_pos hi, coordinateProjection, comap] using hx' ⟨i, hi⟩
  · simpa only [finiteSplitPoint, dif_neg hi] using hfixed ⟨i, hi⟩

theorem exists_coordinate_fiber_score
    (A : ResidueBoxSlice N q) (hq : 0 < q) (hlength : ∀ i, 0 < A.length i)
    (keep : I → Prop) (score : (I → ℤ) → ℝ) {a : ℝ}
    (hmean : a ≤ 𝔼 x ∈ A.integerPoints, score x) :
    ∃ fixed : {i // ¬keep i} → ℤ,
      (∀ i : {i // ¬keep i},
        fixed i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i)) ∧
      (∀ x ∈ (A.coordinateProjection keep).integerPoints,
        finiteSplitPoint keep x fixed ∈ A.integerPoints) ∧
      a ≤ 𝔼 x ∈ (A.coordinateProjection keep).integerPoints,
        score (finiteSplitPoint keep x fixed) := by
  let e := Equiv.piEquivPiSubtypeProd keep (fun i => Fin (A.length i))
  let : ∀ i, Nonempty (Fin (A.length i)) := fun i => ⟨⟨0, hlength i⟩⟩
  let fixedOf (v : ∀ i : {i // ¬keep i}, Fin (A.length i)) : {i // ¬keep i} → ℤ :=
    fun i => ((A.start i + q * (v i).val : ℕ) : ℤ)
  have hsplit : (𝔼 j : (∀ i, Fin (A.length i)), score (A.integerPoint j)) =
      𝔼 v : (∀ i : {i // ¬keep i}, Fin (A.length i)),
        𝔼 u : (∀ i : {i // keep i}, Fin (A.length i)),
          score (finiteSplitPoint keep ((A.coordinateProjection keep).integerPoint u)
            (fixedOf v)) := by
    calc
      _ = 𝔼 uv : (∀ i : {i // keep i}, Fin (A.length i)) ×
          (∀ i : {i // ¬keep i}, Fin (A.length i)),
          score (finiteSplitPoint keep ((A.coordinateProjection keep).integerPoint uv.1)
            (fixedOf uv.2)) := by
        apply Fintype.expect_equiv e
        intro j
        congr 1
        funext i
        by_cases hi : keep i <;>
          simp [e, integerPoint, point, coordinateProjection, comap, fixedOf,
            finiteSplitPoint, hi, Equiv.piEquivPiSubtypeProd]
      _ = _ := by
        rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  rw [A.expect_integerPoints hq score, hsplit] at hmean
  obtain ⟨v, _, hv⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  have hfixed (i : {i // ¬keep i}) :
      fixedOf v i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i) := by
    simpa only [fixedOf, Nat.cast_add, Nat.cast_mul] using
      integerProgressionSupport_point (A.start i : ℤ) q (A.length i) hq
        (v i).val (v i).isLt
  refine ⟨fixedOf v, hfixed, ?_, ?_⟩
  · intro x hx
    exact A.finiteSplitPoint_mem_integerPoints keep (fixedOf v) hfixed hx
  · rw [(A.coordinateProjection keep).expect_integerPoints hq]
    exact hv

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {N : I → ℕ} {q : ℕ}

theorem coordinate_complexMean
    (A : ResidueBoxSlice N q) (hq : 0 < q) (hlength : ∀ i, 0 < A.length i)
    (keep : I → Prop) (f : (I → ℤ) → ℂ) :
    (𝔼 x ∈ A.integerPoints, f x) =
      𝔼 v : (∀ i : {i // ¬keep i}, Fin (A.length i)),
        𝔼 u ∈ (A.coordinateProjection keep).integerPoints,
          f (finiteSplitPoint keep u
            (fun i => ((A.start i + q * (v i).val : ℕ) : ℤ))) := by
  let e := Equiv.piEquivPiSubtypeProd keep (fun i => Fin (A.length i))
  let : ∀ i, Nonempty (Fin (A.length i)) := fun i => ⟨⟨0, hlength i⟩⟩
  let fixedOf (v : ∀ i : {i // ¬keep i}, Fin (A.length i)) : {i // ¬keep i} → ℤ :=
    fun i => ((A.start i + q * (v i).val : ℕ) : ℤ)
  have hsplit : (𝔼 j : (∀ i, Fin (A.length i)), f (A.integerPoint j)) =
      𝔼 v : (∀ i : {i // ¬keep i}, Fin (A.length i)),
        𝔼 u : (∀ i : {i // keep i}, Fin (A.length i)),
          f (finiteSplitPoint keep ((A.coordinateProjection keep).integerPoint u)
            (fixedOf v)) := by
    calc
      _ = 𝔼 uv : (∀ i : {i // keep i}, Fin (A.length i)) ×
          (∀ i : {i // ¬keep i}, Fin (A.length i)),
          f (finiteSplitPoint keep ((A.coordinateProjection keep).integerPoint uv.1)
            (fixedOf uv.2)) := by
        apply Fintype.expect_equiv e
        intro j
        congr 1
        funext i
        by_cases hi : keep i <;>
          simp [e, integerPoint, point, coordinateProjection, comap, fixedOf,
            finiteSplitPoint, hi, Equiv.piEquivPiSubtypeProd]
      _ = _ := by
        rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  rw [A.expect_integerPoints hq f, hsplit]
  apply Finset.expect_congr rfl
  intro v _
  exact ((A.coordinateProjection keep).expect_integerPoints hq
    (fun u => f (finiteSplitPoint keep u (fixedOf v)))).symm

theorem exists_coordinate_fiber_norm
    (A : ResidueBoxSlice N q) (hq : 0 < q) (hlength : ∀ i, 0 < A.length i)
    (keep : I → Prop) (f : (I → ℤ) → ℂ) :
    ∃ fixed : {i // ¬keep i} → ℤ,
      (∀ i : {i // ¬keep i},
        fixed i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i)) ∧
      (∀ x ∈ (A.coordinateProjection keep).integerPoints,
        finiteSplitPoint keep x fixed ∈ A.integerPoints) ∧
      ‖𝔼 x ∈ A.integerPoints, f x‖ ≤
        ‖𝔼 u ∈ (A.coordinateProjection keep).integerPoints,
          f (finiteSplitPoint keep u fixed)‖ := by
  let : ∀ i, Nonempty (Fin (A.length i)) := fun i => ⟨⟨0, hlength i⟩⟩
  let fixedOf (v : ∀ i : {i // ¬keep i}, Fin (A.length i)) : {i // ¬keep i} → ℤ :=
    fun i => ((A.start i + q * (v i).val : ℕ) : ℤ)
  have hmean : ‖𝔼 x ∈ A.integerPoints, f x‖ ≤
      𝔼 v : (∀ i : {i // ¬keep i}, Fin (A.length i)),
        ‖𝔼 u ∈ (A.coordinateProjection keep).integerPoints,
          f (finiteSplitPoint keep u (fixedOf v))‖ := by
    rw [A.coordinate_complexMean hq hlength keep f]
    exact RCLike.norm_expect_le (K := ℂ)
  obtain ⟨v, _, hv⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  have hfixed (i : {i // ¬keep i}) :
      fixedOf v i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i) := by
    simpa only [fixedOf, Nat.cast_add, Nat.cast_mul] using
      integerProgressionSupport_point (A.start i : ℤ) q (A.length i) hq
        (v i).val (v i).isLt
  exact ⟨fixedOf v, hfixed,
    fun _ hx => A.finiteSplitPoint_mem_integerPoints keep (fixedOf v) hfixed hx, hv⟩

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OptionMarkedSurjective
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

theorem optionMarkedLieMap_piRealOrbit_log
    {ι : Type v} [Fintype ι] {L₀ M₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing M₀] [LieAlgebra ℚ M₀]
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
    {s d₀ e₀ : ℕ} {d : ι → ℕ} {σ : Type*} {w : σ → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀)
    (Q₀ : RationalFilteredNilmanifold M₀ s e₀)
    (E : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (g : ∀ i, (optionFactors D₀ E i).filtration.realification.PolynomialOrbit w)
    (h : ∀ i, (optionFactors Q₀ E i).filtration.realification.PolynomialOrbit w)
    (hnone : VectorPolynomial.map
      ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) (g none).log =
        (h none).log)
    (hsome : ∀ i, (g (some i)).log = (h (some i)).log) :
    VectorPolynomial.map
      ((realificationLieHom (optionMarkedLieMap φ)).toLinearMap.restrictScalars ℚ)
      (piRealOrbit (fun i => (optionFactors D₀ E i).filtration) g).log =
        (piRealOrbit (fun i => (optionFactors Q₀ E i).filtration) h).log := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [coefficients_map]
  apply ((Pi.basis (fun i => (optionFactors Q₀ E i).basis)).baseChange ℝ).repr.injective
  ext ⟨i, k⟩
  rw [realification_pi_basis_repr, realification_pi_basis_repr]
  change ((optionFactors Q₀ E i).basis.baseChange ℝ).repr
    (realificationLieHom (liePiEval i)
      (realificationLieHom (optionMarkedLieMap φ)
        (coefficients (piRealOrbit (fun i => (optionFactors D₀ E i).filtration) g).log α))) k =
    ((optionFactors Q₀ E i).basis.baseChange ℝ).repr
      (realificationLieHom (liePiEval i)
        (coefficients (piRealOrbit (fun i => (optionFactors Q₀ E i).filtration) h).log α)) k
  rw [piRealOrbit_coefficient]
  cases i with
  | none =>
    rw [realification_optionMarkedLieMap_none, piRealOrbit_coefficient]
    have hα := congrArg (fun q => coefficients q α) hnone
    erw [coefficients_map] at hα
    exact congrArg (fun x => (Q₀.basis.baseChange ℝ).repr x k) hα
  | some i =>
    rw [realification_optionMarkedLieMap_some, piRealOrbit_coefficient]
    exact congrArg (fun q => ((E i).basis.baseChange ℝ).repr (coefficients q α) k)
      (hsome i)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {J : Type v} [Fintype J] {L : Type u} {M : J → Type u} {Y : Type*}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  [LieRing Y] [LieAlgebra ℚ Y] {s d₀ dQ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)
  (Q : RationalFilteredNilmanifold
    (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) s dQ)
  (hQ : Q.filtration = D.filtration.quotientLie
    (D.filtration.pivotAnnihilatorIdeal π eta js)
    (by rw [D.filtration.terminal]; exact bot_le))

include hQ

theorem optionNativePivotQuotientMap_mem_layer (k : ℕ)
    (x : ∀ i : Option J, optionLieSpace L M i)
    (hx : x ∈ (optionProduct D E).filtration.layer k) :
    optionMarkedLieMap (L := M)
      (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)) x ∈
        (optionProduct Q E).filtration.layer k := by
  have hcoord := (mem_pi_layer (fun i => (optionFactors D E i).filtration) k x).mp hx
  apply (mem_pi_layer (fun i => (optionFactors Q E i).filtration) k _).mpr
  intro i
  cases i with
  | none =>
    change lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js) (x none) ∈
      Q.filtration.layer k
    rw [hQ]
    exact ⟨x none, hcoord none, rfl⟩
  | some j => exact hcoord (some j)

theorem optionNativePivotQuotientMap_layer_surjective (k : ℕ)
    (y : ∀ i : Option J,
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i)
    (hy : y ∈ (optionProduct Q E).filtration.layer k) :
    ∃ x ∈ (optionProduct D E).filtration.layer k,
      optionMarkedLieMap (L := M)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)) x = y := by
  have hcoord := (mem_pi_layer (fun i => (optionFactors Q E i).filtration) k y).mp hy
  have hy₀ : y none ∈ Q.filtration.layer k := hcoord none
  rw [hQ] at hy₀
  obtain ⟨x₀, hx₀, hxy₀⟩ := hy₀
  let x : ∀ i : Option J, optionLieSpace L M i
    | none => x₀
    | some j => y (some j)
  refine ⟨x, ?_, ?_⟩
  · apply (mem_pi_layer (fun i => (optionFactors D E i).filtration) k x).mpr
    intro i
    cases i with
    | none => exact hx₀
    | some j => exact hcoord (some j)
  · funext i
    cases i with
    | none => exact hxy₀
    | some j => rfl

variable (U : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)

noncomputable def optionNativeCommonPivotQuotientFast :
    LieSubalgebra ℚ (optionProduct Q E).filtration.AssociatedGraded :=
  U.map ((optionProduct D E).filtration.associatedGradedMap
    (optionProduct Q E).filtration
    (optionMarkedLieMap (L := M)
      (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)))
    (optionNativePivotQuotientMap_mem_layer D E π eta js Q hQ))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledNativeModel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct Pointwise BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {σ X : Type*} {w : σ → ℕ} {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {f : X → ℂ}

def twistedNativeSampleFunctions {I : Type*} (w : σ → ℕ) (degree : ℕ) (p : ℝ)
    (sample : X → σ → ℤ) (twist : I → X → ℂ) : Set (X → ℂ) :=
  {f | f = 0 ∨ ∃ i g, Nonempty (NativeSampleModel w degree p sample g) ∧
    f = fun x => star (twist i x) * g x}

theorem twistedNativeSampleFunctions_zero {I : Type*} (twist : I → X → ℂ) :
    (0 : X → ℂ) ∈ twistedNativeSampleFunctions w degree p sample twist := Or.inl rfl

theorem twistedNativeSampleFunctions_norm {I : Type*} (twist : I → X → ℂ)
    (htwist : ∀ i x, ‖twist i x‖ ≤ 1)
    (hf : f ∈ twistedNativeSampleFunctions w degree p sample twist) (x : X) : ‖f x‖ ≤ 1 := by
  rcases hf with rfl | ⟨i, g, ⟨G⟩, rfl⟩
  · simp
  · rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (htwist i x)).trans (G.norm_le x)

end Erdos3

end

section

namespace Erdos3.NativeSampleModel

open CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [instance] VerticalExpansion.finite

end Erdos3.NativeSampleModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOrbitOuterControl
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold

theorem exists_native_orbit_coefficient_control :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      {D : RationalFilteredNilmanifold L s d}
      {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p),
      0 ≤ p → D.GeometryComplexityLE p → (∀ i, 0 < A i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        D.filtration.PolynomialRationalGrid D.basis (fun _ : σ => 1) m R.rational ∧
        D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A
          (Real.exp ((p + C) ^ C)) R.slow := by
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + 2) ^ 3 + X + (X + 3) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ s d D g eta A p R hp hD hA
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p := by
    rw [Fintype.card_fin, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1
  have hdimD : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hD.1
  let m := matrixDenominator (fun i j => D.basis.repr (R.basis j) i) * R.denominator
  have hmb : (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + p) :=
    NilpotentLieFiltration.original_coordinate_denominator_bound R.basis D.basis hp hdim hdimD
      R.basis_height R.denominator R.denominator_bound
  have hcost : (p + 2) ^ 3 + p + (p + 3) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hden : (p + 2) ^ 3 + p ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (sq_nonneg _)).trans hcost
  have hslow : (p + 3) ^ 2 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hcost
  have hs := D.filtration.polynomialSlowBound_change_basis_exp R.basis D.basis
    (fun _ : σ => 1) A hA hp hdim R.basis_height R.slow R.slow_bound
  exact ⟨m, Nat.mul_pos (matrixDenominator_pos _) R.denominator_pos,
    hmb.trans (Real.exp_le_exp.mpr hden),
    D.filtration.polynomialRationalGrid_change_basis R.basis D.basis
      (fun _ : σ => 1) R.denominator R.rational R.rational_grid,
    D.filtration.polynomialSlowBound_mono D.basis (fun _ : σ => 1) A hA
      (Real.exp_le_exp.mpr hslow) R.slow hs⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

include henormous in
theorem allocatedEnormous_active : S.value^(j.val+1) < basisAxisScale (basis j) i :=
  (Nat.pow_le_pow_right S.positive ((layerDegree_le_tailDegree j).trans (Nat.le_succ _))).trans_lt henormous

include henormous in
theorem allocatedEnormous_principalScale (d) (hd : d ∈ layerIntegerPrincipalSlots (G := G) B j i) :
    monomialScale (layerSamplerBox B U basis S) d.val = (S.value : ℝ)^(j.val+1) := by
  rw [show monomialScale (layerSamplerBox B U basis S) d.val =
      (integerAxisSideLength (j.val+1) (basisAxisScale (basis j) i) S.value
        (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) : ℝ)^(j.val+1) from
      layerSamplerSides_integer_principal B U basis R S.value j i d hd]
  simp only [integerAxisSideLength, allocatedEnormous_active B U basis S j i henormous, ↓reduceIte]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : I j)

local notation "centers" => allocatedContinuousProfileCenters (G := G) B R j i
local notation "widths" => allocatedContinuousProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1

noncomputable def allocatedContinuousKernelDensity
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (O → ℝ) → ℝ :=
  affineSelectedJetDensity s
    (normalizedPivotEquiv ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s) hA
      (fun o => kernelScale (s o)) (fun _ => 1)
      (fun o => kernelJetCoefficientScale_pos G (j.val+1) (by exact_mod_cast S.positive) zero_lt_one (s o))
      (fun _ => zero_lt_one))
    (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
      (fun d => kernelScale d.val) (fun _ => 1)))
    (allocatedNonkernelExponent B j) input fixedReal rows (centers ∘ reindex) (widths ∘ reindex) y

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B K I : Type*} [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)

include hA in
theorem selectedJointDensityMass_bounds (D : B → (K × I → ℤ) → ℝ) {a b : ℝ}
    (hD : ∀ x, selectedResidueDensityMass modulus T W (D x) ∈ Set.Icc a b) :
    selectedJointDensityMass A modulus T W D ∈ Set.Icc a b := by
  rw [selectedJointDensityMass, ← FiniteProbabilityWeights.uniformFinset_mean A hA]
  exact (FiniteProbabilityWeights.uniformFinset A hA).mean_mem_Icc _ (fun x => hD x.val)

include hA in
theorem selectedJointDensityMass_close (D : B → (K × I → ℤ) → ℝ) {ε : ℝ}
    (hD : ∀ x, |selectedResidueDensityMass modulus T W (D x)-1| ≤ ε) :
    |selectedJointDensityMass A modulus T W D-1| ≤ ε := by
  rw [selectedJointDensityMass, ← FiniteProbabilityWeights.uniformFinset_mean A hA]
  exact (FiniteProbabilityWeights.uniformFinset A hA).abs_mean_sub_const_le _ 1 ε (fun x => hD x.val)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFixedPositiveDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

include hC hV hσ1 Cinv hCinv hchart hsmall

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include ν in
theorem allocatedCoefficientDensity_positive_spec :
    Continuous (allocatedCoefficientDensity B U b hb o hR hσ S) ∧
      (∀ x, allocatedCoefficientDensity B U b hb o hR hσ S x ∈
        Set.Icc (0 : ℝ) ((allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
          Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m))) ∧
      Integrable (allocatedCoefficientDensity B U b hb o hR hσ S) μ ∧
      (∫ x, allocatedCoefficientDensity B U b hb o hR hσ S x ∂μ) = 1 ∧
      (allocatedCoefficientSource B U b hR hσ S).map (canonicalCoefficientSample U b hb o) =
        realDensityMeasure μ (allocatedCoefficientDensity B U b hb o hR hσ S) := by
  have h := allocatedCoefficientDensity_spec B U b hb o hR hσ S hσ1 Cinv hCinv hchart hsmall μ ν
  exact ⟨allocatedCoefficientDensity_continuous B U b hb o hR hσ S C V hC hV
      hσ1 Cinv hCinv hchart hsmall,
    allocatedCoefficientDensity_bounds B U b hb o hR hσ S C V hC hV
      hσ1 Cinv hCinv hchart hsmall, h.2.2⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalFactorCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial
variable {X : Type*} {m : ℕ} {J : Fin m → Type*}

noncomputable def physicalMaskedFactorInput (period : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ) :
    (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle) :=
  ((fun a => (eval t (p a.1) a.2.2 : UnitAddCircle)),
    (fun a => ((eval t (p a.1) a.2 / period : ℝ) : UnitAddCircle)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedDensityParameterBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a)
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

noncomputable def allocatedNormalizedLongJetFactor (y : activeInput → ℝ) :
    ∀ a : {a // ¬grid a}, (O a.val.1 → ℝ) → ℝ
  | ⟨⟨j, .inl i⟩, _⟩ => allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y
  | ⟨⟨j, .inr i⟩, _⟩ => allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y

noncomputable def allocatedNormalizedLongJetDensity (y : activeInput → ℝ) :
    (realOutput → ℝ) → ℝ :=
  sigmaAxisWeight (allocatedNormalizedLongJetFactor B U basis S x u rows s hA y)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefilteredReconstructionDiagram
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def refilteredReconstructionMap (a : ι)
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) :
    let H := (pi D).filtration.gradedRefiltrationSubalgebra W
    H →ₗ⁅ℚ⁆ (H ⧸ ((pi D).filtration.gradedRefiltration W).layerIdeal s) ×
      (∀ i : {i : ι // i ≠ a}, L i.val) :=
  (lieQuotientMap (((pi D).filtration.gradedRefiltration W).layerIdeal s)).prod
    (liePiMap (fun i : {i : ι // i ≠ a} =>
      (liePiEval i.val).comp ((pi D).filtration.gradedRefiltrationSubalgebra W).incl))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFrozenComparison
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

theorem RationalFilteredNilmanifold.frozen_refiltered_group_action
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra U) s e)
    (hEF : E.filtration = D.filtration.gradedRefiltration U)
    (a r : D.RealGroup) (z : E.RealGroup)
    (hz : z ∈ E.filtration.realification.subgroup s) (x : E.RealGroup) :
    a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra U).incl (z * x) * r =
    realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra U).incl z *
      (a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra U).incl x * r) := by
  let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot) (D.filtration.gradedRefiltrationSubalgebra U).incl
  have hz' : (φ z).coord ∈ D.filtration.realGradedRefiltrationLayer U s := by
    apply (D.filtration.mem_native_refiltration_layer U s z.coord).mp
    have h : z.coord ∈ E.filtration.realification.layer s := hz
    simpa only [hEF] using h
  have hcomm := D.filtration.realification.top_commutes (φ z)
    (D.filtration.realGradedRefiltrationLayer_le U s hz') a
  change a * φ (z * x) * r = φ z * (a * φ x * r)
  calc
    a * φ (z * x) * r = (a * φ z) * φ x * r := by simp only [map_mul, mul_assoc]
    _ = (φ z * a) * φ x * r := by rw [← hcomm.eq]
    _ = φ z * (a * φ x * r) := by simp only [mul_assoc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.JointFrameCoefficientCoverSample
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

theorem substitute_translate_joint_frame {K X V : Type*} [Fintype K]
    [AddCommGroup V] [Module ℝ V] (p : VectorPolynomial X ℝ V)
    (a : X → ℤ) (z : Option K × X → ℤ) :
    substitute (affineParameterSubstitution (fun k v => (z (k,v) : ℝ)))
      (translate (fun v => (a v : ℝ)) p) =
    substitute (affineParameterSubstitution
      (fun k v => (jointIntegerFrame (a,z) k v : ℝ))) p := by
  change substitute _ (substitute (fun v => MvPolynomial.X v + MvPolynomial.C (a v : ℝ)) p) = _
  rw [substitute_comp]
  apply congrArg (fun f : X → MvPolynomial K ℝ => substitute f p)
  funext v
  simp only [map_add, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    affineParameterSubstitution, rowPolynomial, jointIntegerFrame, Int.cast_add, map_add,
    MvPolynomial.algebraMap_eq]
  ring

theorem affineSampleCoefficientArray_joint_frame {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (a : X → ℤ) (z : Option K × X → ℤ) :
    affineSampleCoefficientArray U (fun j => translate (fun v => (a v : ℝ)) (p j))
      (fun j => coefficients_translate_mem (U j) (fun v => (a v : ℝ)) (p j) (hm j))
      (fun k v => (z (k,v) : ℝ)) =
    affineSampleCoefficientArray U p hm (fun k v => (jointIntegerFrame (a,z) k v : ℝ)) := by
  funext s
  apply Subtype.ext
  simp only [affineSampleCoefficientArray_val, substitute_translate_joint_frame]

theorem affineSampleCoefficientTorus_joint_frame {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (a : X → ℤ) (z : Option K × X → ℤ) :
    affineSampleCoefficientTorus U (fun j => translate (fun v => (a v : ℝ)) (p j))
      (fun j => coefficients_translate_mem (U j) (fun v => (a v : ℝ)) (p j) (hm j))
      (fun k v => (z (k,v) : ℝ)) =
    affineSampleCoefficientTorus U p hm (fun k v => (jointIntegerFrame (a,z) k v : ℝ)) :=
  congrArg (QuotientAddGroup.mk' (coefficientIntegerLattice U))
    (affineSampleCoefficientArray_joint_frame U p hm a z)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

@[simp] theorem candidateNestedForwardSeed_succ (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outer : ℕ) (x : ℝ) :
    candidateNestedForwardSeed A constants innerDepth (outer + 1) x =
      preparedFiniteForwardWork A constants innerDepth
        (candidateNestedForwardSeed A constants innerDepth outer x) := by
  simp only [candidateNestedForwardSeed, candidateNestedForwardSeedPolynomial,
    Polynomial.eval₂_comp, preparedFiniteForwardWork]

theorem candidateNestedForwardSeed_nonneg (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outer : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ candidateNestedForwardSeed A constants innerDepth outer x :=
  natPolynomial_eval_nonneg _ hx

theorem candidateNestedForwardSeed_monotone (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth : ℕ) {x : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x) :
    Monotone (fun outer => candidateNestedForwardSeed A constants innerDepth outer x) := by
  apply monotone_nat_of_le_succ
  intro outer
  rw [candidateNestedForwardSeed_succ, preparedFiniteForwardWork_eq]
  let y := candidateNestedForwardSeed A constants innerDepth outer x
  have hy : 0 ≤ y := candidateNestedForwardSeed_nonneg A constants innerDepth outer hx
  have hparam := le_preparedFiniteForwardParameter A constants innerDepth hy
  have hp0 := preparedFiniteForwardParameter_nonneg A constants innerDepth hy
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  calc
    y ≤ preparedFiniteForwardParameter A constants innerDepth y + A := by linarith only [hparam, hAreal]
    _ = (preparedFiniteForwardParameter A constants innerDepth y + A) ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith only [hp0, hAreal]) (by omega)

theorem le_candidateNestedForwardSeed (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outer : ℕ) {x : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x) :
    x ≤ candidateNestedForwardSeed A constants innerDepth outer x := by
  simpa only [candidateNestedForwardSeed_zero] using
    candidateNestedForwardSeed_monotone A constants innerDepth hA hx (Nat.zero_le outer)

theorem candidateNestedForwardWork_le_next_seed
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outer inner : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (hi : inner ≤ innerDepth) :
    preparedFiniteForwardWork A constants inner
      (candidateNestedForwardSeed A constants innerDepth outer x) ≤
        candidateNestedForwardSeed A constants innerDepth (outer + 1) x := by
  rw [candidateNestedForwardSeed_succ, preparedFiniteForwardWork_eq, preparedFiniteForwardWork_eq]
  have hy := candidateNestedForwardSeed_nonneg A constants innerDepth outer hx
  have hp := preparedFiniteForwardParameter_nonneg A constants inner hy
  exact pow_le_pow_left₀ (by positivity)
    (add_le_add (preparedFiniteForwardParameter_monotone A constants hy hi) le_rfl) A

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForwardInnerDetectionThreshold_bound
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
      4 * preparedFiniteForwardWork A stageCountConstant n x + 8)) ≤
        Real.exp (-gainLog) / 2 := by
  have hp := (preparedFiniteForward_prefix_bounds A stageCountConstant n hx).2.1
  have hw := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hfloor : gainLog + 1 ≤
      2 * preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
        4 * preparedFiniteForwardWork A stageCountConstant n x + 8 := by
    dsimp only [preparedFiniteForwardModelPrecision]
    linarith only [hp, hw, hg.1, hs.1]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hhalf : 2 * Real.exp (-(gainLog + 1)) ≤ Real.exp (-gainLog) := by
    calc
      _ ≤ Real.exp 1 * Real.exp (-(gainLog + 1)) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hthreshold := Real.exp_le_exp.mpr (neg_le_neg hfloor)
  linarith only [hthreshold, hhalf]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteNestedSourceRequired
    {Slot : Type*} [Fintype Slot]
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth cutoff : ℕ)
    (x anchorGoodRequired conditionalRequired : ℝ) (detectorRequired : Slot → ℝ) : ℝ :=
  1 + max 0 anchorGoodRequired + max 0 conditionalRequired +
    (∑ slot, max 0 (detectorRequired slot)) +
    ∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
      max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardLaterWorkBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForward_local_shiftedPower_le_later_work
    (A C Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hA : 2 ≤ A) (hC : C ≤ A) (hn : 1 ≤ n) :
    let t := preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
      0 false x gainLog stageLog + preparedFiniteForwardWork A stageCountConstant 0 x
    (t + C) ^ C ≤ preparedFiniteForwardWork A stageCountConstant n x := by
  intro t
  have hcap : (t + C) ^ C ≤ preparedFiniteForwardCap A stageCountConstant 0 x := by
    simpa only [t, preparedFiniteForwardPairedSourcePrecision_model] using
      preparedFiniteForward_phase_cap A stageCountConstant 0 C hx hg hs hC
  have hnext : preparedFiniteForwardCap A stageCountConstant 0 x ≤
      preparedFiniteForwardParameter A stageCountConstant 1 x := by
    rw [preparedFiniteForwardParameter_succ]
    have hparameter := preparedFiniteForwardParameter_nonneg A stageCountConstant 0 hx
    have hbranch := preparedFiniteForwardBranch_nonneg A stageCountConstant 0 hx
    linarith only [hparameter, hbranch]
  have hlater := preparedFiniteForwardParameter_monotone A stageCountConstant hx hn
  have hwork := (preparedFiniteForward_model_scalar_bounds A stageCountConstant n 0 hA hx
    (by simpa only [Nat.cast_zero] using hx)).2.1
  exact hcap.trans (hnext.trans (hlater.trans hwork))

theorem exists_preparedFiniteForward_local_polynomial_le_later_work
    (Cbase : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog f : ℝ},
      0 ≤ x → gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x → C ≤ A → 1 ≤ n →
      let t := preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
        0 false x gainLog stageLog + preparedFiniteForwardWork A stageCountConstant 0 x
      f ∈ Set.Icc 0 ((t + Cbase) ^ Cbase) →
      P.eval₂ (Nat.castRingHom ℝ) f ≤ preparedFiniteForwardWork A stageCountConstant n x := by
  let Q := P.comp ((Polynomial.X + Polynomial.C Cbase) ^ Cbase)
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro A Cdirect stageCountConstant n x gainLog stageLog f hx hg hs hCA hn t hf
  have ht : 0 ≤ t := add_nonneg
    (preparedFiniteForwardPairedSourcePrecision_nonneg A Cdirect stageCountConstant 0 false hx hg hs)
    (preparedFiniteForwardWork_nonneg A stageCountConstant 0 hx)
  have heval : P.eval₂ (Nat.castRingHom ℝ) f ≤
      P.eval₂ (Nat.castRingHom ℝ) ((t + Cbase) ^ Cbase) := by
    simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hf.1 hf.2 k) (Nat.cast_nonneg _)
  have hbound : P.eval₂ (Nat.castRingHom ℝ) ((t + Cbase) ^ Cbase) ≤ (t + C) ^ C := by
    simpa [Q, Polynomial.eval₂_comp, Polynomial.eval₂_pow] using hpoly t ht
  exact heval.trans (hbound.trans
    (preparedFiniteForward_local_shiftedPower_le_later_work A C Cdirect stageCountConstant n
      hx hg hs (hC.trans hCA) hCA hn))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardPairedResourceBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteForwardPairedResource_budget (Cdirect Cresource : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog : ℝ}, 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      (preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n true x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + Cresource) ^ Cresource ≤
      (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + (X + Polynomial.C Cdirect) ^ Cdirect +
    Polynomial.C Cresource) ^ Cresource
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro A stageCountConstant n x gainLog stageLog hx hg hs
  let t := preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
    preparedFiniteForwardWork A stageCountConstant n x
  have ht : 0 ≤ t := add_nonneg
    (preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs).2.1
    (preparedFiniteForwardWork_nonneg A stageCountConstant n hx)
  have heq : preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n true x gainLog stageLog +
      preparedFiniteForwardWork A stageCountConstant n x + Cresource =
      t + (t + Cdirect) ^ Cdirect + Cresource := by
    rw [preparedFiniteForwardPairedSourcePrecision_direct]
    dsimp only [t]
    ring
  rw [heq]
  simpa [P, X, Polynomial.eval₂_pow, t] using hpoly t ht

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedProgressionDensityIdentity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] in
def CoefficientDeckDensityLaw
    (source : Measure (CoefficientSamplerArrays (K := K) I n))
    (density : CoefficientTorus (K := K) U → ℝ) (d : ℕ) [NeZero d] : Prop :=
    (source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
      (fun x : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d =>
        canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) x.1 x.2) =
      realDensityMeasure μ (fun y => density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedJointMaskedDensityComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def allocatedMaskedTiltedConstant (m : ℕ) : ℕ :=
  Classical.choose (exists_affine_coefficient_cover_tilted_family_comparison.{0, 0, 0, 0} m)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CenteredCoefficientDeckChartMeasurable
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped Classical

variable {K X : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem affineCoefficientCoverSample_center_measurable {C : Type*} [MeasurableSpace C]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j)
    (c : C → ∀ j, U j) (hc : Measurable c) (a : X → ℤ)
    (z : Option K × X → ℤ) (q : ℕ) :
    Measurable (fun center => affineCoefficientCoverSample U
      (fun j => translate (fun x => (a x : ℝ)) (subtractConstant (c center j).val (poly j)))
      (fun j => coefficients_translate_mem (U j) (fun x => (a x : ℝ)) _
        (coefficients_subtractConstant_mem (U j) (c center j) (poly j) (hm j)))
      q (fun k x => (z (k,x) : ℝ))) := by
  have hcarray : Measurable (fun center => constantCoefficientArray (K := K) U
      (fun s => c center s.1)) := by
    apply measurable_pi_iff.mpr
    intro s
    by_cases hs : s.2.val = 0
    · simpa only [constantCoefficientArray, LinearMap.coe_mk, AddHom.coe_mk, hs, ite_true, Function.comp_def] using
        (measurable_pi_apply s.1).comp hc
    · simpa only [constantCoefficientArray, LinearMap.coe_mk, AddHom.coe_mk, hs, ite_false] using
        (measurable_const : Measurable (fun _ : C => (0 : U s.1)))
  have hcentered : Measurable (fun center => centeredAffineCoefficientArray U poly hm (c center)
      (fun k x => (jointIntegerFrame (a,z) k x : ℝ))) :=
    measurable_const.sub hcarray
  have hq := (show Continuous (QuotientAddGroup.mk' (coefficientIntegerLattice (K := K) U)) from
    QuotientAddGroup.continuous_mk).measurable.comp (hcentered.const_smul (q : ℝ)⁻¹)
  convert hq using 1
  funext center
  apply congrArg (fun v : CoefficientArray (K := K) U =>
    QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ)⁻¹ • v))
  exact (affineSampleCoefficientArray_joint_frame U
    (fun j => subtractConstant (c center j).val (poly j))
    (fun j => coefficients_subtractConstant_mem (U j) (c center j) (poly j) (hm j)) a z).trans
      (affineSampleCoefficientArray_subtractConstant U poly hm (c center) _)

variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [CompactSpace (CoefficientTorus (K := K) U)]

theorem coefficientDeckChartEvent_center_measurableSet {C : Type*} [MeasurableSpace C]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j)
    (c : C → ∀ j, U j) (hc : Measurable c) (a : X → ℤ)
    (z : Option K × X → ℤ) (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues K n E q → Prop) :
    MeasurableSet {center | coefficientDeckChartEvent U bW b hb o q event
      (affineCoefficientCoverSample U
        (fun j => translate (fun x => (a x : ℝ)) (subtractConstant (c center j).val (poly j)))
        (fun j => coefficients_translate_mem (U j) (fun x => (a x : ℝ)) _
          (coefficients_subtractConstant_mem (U j) (c center j) (poly j) (hm j)))
        q (fun k x => (z (k,x) : ℝ)))} :=
  (coefficientDeckChartEvent_measurableSet U bW b hb o q event).preimage
    (affineCoefficientCoverSample_center_measurable U poly hm c hc a z q)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem spatial_kernel_selected_raw {G P A R : Type*}
    [Fintype G] [Fintype P] [Fintype A] [CommRing R]
    (e : A ↪ G) (fixed : Option (G ⊕ P) → R) (c : A → R) :
    spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed) =
      (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range (spatialKernelRankSlot (P := P) e)),
        monomial (spatialRankExponent d) (fixed d)) +
      ∑ a, monomial (spatialRankExponent (spatialKernelRankSlot (P := P) e a)) (c a) := by
  unfold spatialRankPolynomial
  convert modularMonomialArrayPolynomial_selected (E := Option (G ⊕ P))
    (K := G ⊕ P) (R := R) (A := A) spatialRankExponent
    (spatialKernelRankSlot e) (spatialKernelRankSlot_injective (P := P) e) fixed c using 1
  congr 1
  apply Finset.sum_congr
  · congr 1
  · intro d _
    rfl

theorem spatialRankPolynomial_kernel_selected {G P A R : Type*}
    [Fintype G] [Fintype P] [Fintype A] [CommRing R]
    (e : A ↪ G) (fixed : Option (G ⊕ P) → R) (c : A → R) :
    spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed) =
      (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range (spatialKernelRankSlot (P := P) e)),
        monomial (spatialRankExponent d) (fixed d)) +
      ∑ a, c a • (X (.inl (e a)) : MvPolynomial (G ⊕ P) R) := by
  rw [spatial_kernel_selected_raw e fixed c, spatial_kernel_selected_sum e c]

theorem spatialRankPolynomial_kernel_selected_top {G P A R : Type*}
    [Fintype G] [Fintype P] [Fintype A] [CommRing R]
    (e : A ↪ G) (fixed : Option (G ⊕ P) → R) (c : A → R) :
    homogeneousComponent 1 (spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed)) =
      homogeneousComponent 1
        (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range (spatialKernelRankSlot (P := P) e)),
          monomial (spatialRankExponent d) (fixed d)) +
      ∑ a, c a • (X (.inl (e a)) : MvPolynomial (G ⊕ P) R) := by
  rw [spatialRankPolynomial_kernel_selected e fixed c, map_add]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_eq_C_mul, C_mul_X_eq_monomial]
  exact homogeneousComponent_eq_self (isHomogeneous_monomial _ (by simp))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ} {E : Fin m → Type*} {N : ℕ}

omit [Fintype K] in
theorem resampleCoefficientDeckCoordinate_apply {A : Type*}
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (c : A → ZMod N)
    (e : BoundedCoefficientExponent K (j.val + 1)) :
    resampleCoefficientDeckCoordinate r j i slot c j e i =
      Function.extend slot c (fun e => r j e i) e := by
  simp only [resampleCoefficientDeckCoordinate, Function.update_self]

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankActualRead
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem extend_selected_original {A K R : Type*} (slot : A → K)
    (hinj : Function.Injective slot) (c : K → R) :
    Function.extend slot (fun a => c (slot a)) c = c := by
  funext k
  by_cases hk : k ∈ Set.range slot
  · obtain ⟨a,rfl⟩ := hk
    exact hinj.extend_apply _ _ a
  · exact Function.extend_apply' _ _ k hk

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PrecenterForecastNativeAtomDictionary
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_precenter_forecast_finiteLaw_native_partners
    {Ω T X Branch K σ Θ : Type*}
    [Fintype Ω] [Fintype T] [Fintype K]
    (input : Branch → X → ℂ) (models : Branch → CenteredForecastModel X)
    (nativeWeight : σ → ℕ) (degree : ℕ) (budget : ℝ)
    (sample : X → σ → ℤ) (twist : Θ → X → ℂ)
    (hnative : ∀ b i, (models b).models i ∈
      twistedNativeSampleFunctions nativeWeight degree budget sample twist)
    (hmodel : ∀ b, input b =
      (∑ i, (models b).coefficient i • (models b).models i) + (models b).residual)
    {M termBound delta : ℝ} {rank : ℕ}
    (hM : 0 < M) (hterm : 1 ≤ termBound) (hdelta : 0 < delta)
    (hc : ∀ b, (∑ i, |(models b).coefficient i|) ≤ M)
    (hterms : ∀ b, ((models b).nterms : ℝ) ≤ termBound)
    (selectedBranch : K → Branch) (hrank : Fintype.card K ≤ rank)
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (hproductive : 0 < outer.mass productive)
    (localLaw : Ω → K → FiniteProbabilityWeights T)
    (physical : Ω → T → X) (weight : Ω → K → T → ℂ)
    (herr : ∀ a ∈ productive, ∀ k,
      ‖(localLaw a k).complexMean (fun t =>
        (models (selectedBranch k)).residual (physical a t) * weight a k t)‖ ≤ delta / 2)
    (hscore : ∀ a ∈ productive, ∀ k, delta ≤
      ‖(localLaw a k).complexMean (fun t =>
        input (selectedBranch k) (physical a t) * weight a k t)‖) :
    ∃ (fixedTwist : K → Θ) (nativeValue : K → X → ℂ)
      (_native : ∀ k, NativeSampleModel nativeWeight degree budget sample (nativeValue k))
      (retained : Finset Ω),
      retained ⊆ productive ∧ 0 < outer.mass retained ∧
      outer.mass productive / termBound ^ rank ≤ outer.mass retained ∧
      ∀ a ∈ retained, ∀ k, delta / (2 * M) ≤
        ‖(localLaw a k).complexMean (fun t =>
          (star (twist (fixedTwist k) (physical a t)) * nativeValue k (physical a t)) *
            weight a k t)‖ := by
  let selectedModel := fun k => models (selectedBranch k)
  let : ∀ k, Nonempty (Fin (selectedModel k).nterms) :=
    fun k => ⟨⟨0, (selectedModel k).positive⟩⟩
  let test := fun a k => (localLaw a k).sampledComplexTest (physical a) (weight a k)
  have heval (a) (k) (f : X → ℂ) : test a k f =
      (localLaw a k).complexMean (fun t => f (physical a t) * weight a k t) := rfl
  have hmodelComplex (k : K) : input (selectedBranch k) =
      (∑ i, ((selectedModel k).coefficient i : ℂ) • (selectedModel k).models i) +
        (selectedModel k).residual := hmodel (selectedBranch k)
  have hcComplex (k : K) : ∑ i, ‖((selectedModel k).coefficient i : ℂ)‖ ≤ M := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hc (selectedBranch k)
  obtain ⟨partner, retained, hsub, hmass, hcorr⟩ :=
    exists_fixed_linear_model_partners_of_pointwise_error outer productive
      (fun k => input (selectedBranch k)) (fun k => (selectedModel k).residual)
      (fun k => (selectedModel k).models)
      (fun k i => ((selectedModel k).coefficient i : ℂ)) test
      hmodelComplex hdelta hM hcComplex
      (by intro a ha k; rw [heval]; exact herr a ha k)
      (by intro a ha k; rw [heval]; exact hscore a ha k)
  have hmasspos : 0 < outer.mass retained :=
    (div_pos hproductive (Finset.prod_pos (fun k _ =>
      Nat.cast_pos.mpr Fintype.card_pos))).trans_le hmass
  have hne : retained.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmasspos
    linarith)
  obtain ⟨a₀, ha₀⟩ := hne
  have hchosen (k : K) : ∃ (t : Θ) (g : X → ℂ),
      Nonempty (NativeSampleModel nativeWeight degree budget sample g) ∧
      (selectedModel k).models (partner k) = fun x => star (twist t x) * g x := by
    rcases hnative (selectedBranch k) (partner k) with hzero | hgood
    · have hn := hcorr a₀ ha₀ k
      change delta / (2 * M) ≤ ‖test a₀ k ((models (selectedBranch k)).models (partner k))‖ at hn
      rw [hzero, map_zero, norm_zero] at hn
      have hpos : 0 < delta / (2 * M) := div_pos hdelta (by positivity)
      linarith
    · exact hgood
  choose fixedTwist nativeValue hnativeValue heq using hchosen
  refine ⟨fixedTwist, nativeValue, fun k => Classical.choice (hnativeValue k),
    retained, hsub, hmasspos, ?_, ?_⟩
  · apply le_trans _ hmass
    apply div_le_div_of_nonneg_left hproductive.le
      (Finset.prod_pos (fun k _ => Nat.cast_pos.mpr Fintype.card_pos))
    calc
      (∏ k, (Fintype.card (Fin (selectedModel k).nterms) : ℝ))
          ≤ ∏ _k : K, termBound := by
        apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        intro k _
        simpa only [Fintype.card_fin] using hterms (selectedBranch k)
      _ = termBound ^ Fintype.card K := by rw [Finset.prod_const, Finset.card_univ]
      _ ≤ termBound ^ rank := pow_le_pow_right₀ hterm hrank
  · intro a ha k
    have h := hcorr a ha k
    rw [heval, heq] at h
    exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ExternalKernelPrecenterNativePointPartners
namespace OAI

section

namespace Erdos3
open scoped BigOperators TensorProduct Classical

theorem exists_external_kernel_precenter_native_point_partners
    {L σ X Ω T I Freq NativeCoord Θ : Type*}
    [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype T] [Fintype I] [Nonempty I]
    {s d r : ℕ} (D : RationalFilteredNilmanifold L s d)
    {w : σ → ℕ}
    (U : Freq → X → D.Niltest w) (representative : I → X)
    {p B ε δ M termBound : ℝ}
    (hcomplex : ∀ f x, (U f x).ComplexityLE p)
    (hnet : ∀ f x, ∃ i, ∀ y, ‖(U f x).observable y -
      (U f (representative i)).observable y‖ ≤ ε)
    (input : X → ℂ) (models : (Freq × I) → CenteredForecastModel X)
    (nativeWeight : NativeCoord → ℕ) (degree : ℕ) (budget : ℝ)
    (sample : X → NativeCoord → ℤ) (twist : Θ → X → ℂ)
    (hnative : ∀ b i, (models b).models i ∈
      twistedNativeSampleFunctions nativeWeight degree budget sample twist)
    (hmodel : ∀ b, externalNetMaskFamily (fun f x => (U f x).observable)
      (fun f i => (U f (representative i)).observable) hnet input b =
        (∑ i, (models b).coefficient i • (models b).models i) + (models b).residual)
    (hc : ∀ b, (∑ i, |(models b).coefficient i|) ≤ M)
    (hterms : ∀ b, ((models b).nterms : ℝ) ≤ termBound)
    (hM : 0 < M) (hterm : 1 ≤ termBound)
    (code : Fin r → Option Freq)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights T)
    (localPoint : Ω → T → D.Space) (physical : Ω → T → X)
    (hB : 0 ≤ B) (hδ : 0 < δ) (herror : B * ε ≤ δ / 2)
    (hinput : ∀ x, ‖input x‖ ≤ B)
    (hresidual : ∀ a ∈ H, ∀ f i,
      ‖(localLaw a).complexMean (fun t => (models (f, i)).residual (physical a t) *
        (U f (representative i)).observable (localPoint a t))‖ ≤
          (δ / (2 * Fintype.card I)) / 2)
    (hscore : ∀ a ∈ H, ∀ i f, code i = some f → δ ≤
      ‖(localLaw a).complexMean (fun t => input (physical a t) *
        (U f (physical a t)).observable (localPoint a t))‖) :
    ∃ (chosen : KernelProjectionPresentPivot code → I)
      (fixedTwist : KernelProjectionPresentPivot code → Θ)
      (nativeValue : KernelProjectionPresentPivot code → X → ℂ)
      (_native : ∀ k, NativeSampleModel nativeWeight degree budget sample (nativeValue k))
      (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      outer.mass H / ((Fintype.card I : ℝ) ^ r * termBound ^ r) ≤ outer.mass retained ∧
      (∀ k, (U (kernelProjectionSelectedPivot code k)
        (representative (chosen k))).ComplexityLE p) ∧
      ∀ a ∈ retained, ∀ k, (δ / (2 * Fintype.card I)) / (2 * M) ≤
        ‖(localLaw a).complexMean (fun t =>
          (star (twist (fixedTwist k) (physical a t)) * nativeValue k (physical a t)) *
            (U (kernelProjectionSelectedPivot code k)
              (representative (chosen k))).observable (localPoint a t))‖ := by
  let K := KernelProjectionPresentPivot code
  let functions := fun (k : K) x => (U (kernelProjectionSelectedPivot code k) x).observable
  let centers := fun (k : K) i =>
    (U (kernelProjectionSelectedPivot code k) (representative i)).observable
  have hselected (a : Ω) (ha : a ∈ H) (k : K) : δ ≤
      ‖(localLaw a).complexMean (fun t => input (physical a t) *
        functions k (physical a t) (localPoint a t))‖ :=
    hscore a ha k.val (kernelProjectionSelectedPivot code k)
      (kernelProjectionSelectedPivot_spec code k)
  obtain ⟨chosen, masked, H', hmask, _, hsub, hpos, hmass, hlocal⟩ :=
    exists_simultaneous_external_pivot_masks functions centers
      (fun k => hnet (kernelProjectionSelectedPivot code k)) outer H hH
      (fun a _ => localLaw a) physical (fun a _ t => localPoint a t)
      input hB hδ herror hinput hselected
  have hmassRank : outer.mass H / (Fintype.card I : ℝ) ^ r ≤ outer.mass H' := by
    apply le_trans _ hmass
    apply div_le_div_of_nonneg_left (outer.mass_nonneg H)
      (pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _)
    exact pow_le_pow_right₀
      (by exact_mod_cast Fintype.card_pos : (1 : ℝ) ≤ Fintype.card I)
      (kernelProjectionPresentPivot_card_le code)
  let selectedBranch := fun k : KernelProjectionPresentPivot code =>
    (kernelProjectionSelectedPivot code k, chosen k)
  let family := externalNetMaskFamily (fun f x => (U f x).observable)
    (fun f i => (U f (representative i)).observable) hnet input
  have hfamily (k : KernelProjectionPresentPivot code) :
      family (selectedBranch k) = masked k := by
    funext x
    exact (hmask k x).symm
  obtain ⟨fixedTwist, nativeValue, native, retained, hretSub, hretPos, hretMass, hretScore⟩ :=
    exists_precenter_forecast_finiteLaw_native_partners family models
      nativeWeight degree budget sample twist hnative hmodel hM hterm
      (div_pos hδ (by positivity)) hc hterms selectedBranch
      (kernelProjectionPresentPivot_card_le code) outer H' hpos
      (fun a _ => localLaw a) physical
      (fun a k t => (U (kernelProjectionSelectedPivot code k)
        (representative (chosen k))).observable (localPoint a t))
      (fun a ha k => hresidual a (hsub ha) _ _)
      (by intro a ha k; rw [hfamily]; exact hlocal a ha k)
  refine ⟨chosen, fixedTwist, nativeValue, native, retained,
    fun a ha => hsub (hretSub ha), hretPos, ?_, fun k => hcomplex _ _, hretScore⟩
  calc
    outer.mass H / ((Fintype.card I : ℝ) ^ r * termBound ^ r)
        = (outer.mass H / (Fintype.card I : ℝ) ^ r) / termBound ^ r := by
      rw [div_div]
    _ ≤ outer.mass H' / termBound ^ r :=
      div_le_div_of_nonneg_right hmassRank (pow_nonneg (by linarith) _)
    _ ≤ outer.mass retained := hretMass

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

noncomputable section

variable {m : ℕ}
  {G X : Type*}
  [Fintype G]
  [Fintype X]
  {I J : Fin m → Type*}
  [∀ j, Fintype (I j)]
  [∀ j, Fintype (J j)]
  {n : Fin m → ℕ}
  {B : LayerSamplerAxis I n → Type*}
  [∀ a, Fintype (B a)]
  {U : ∀ j, Submodule ℝ (J j → ℝ)}
  {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
  {R σ : Fin m → ℝ}
  {S : LayerSamplerScale (G := G) B U b R σ}
  {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
  {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
  {hR : ∀ j, 0 < R j}
  {hσ : ∀ j, 0 < σ j}
  {N : X → ℕ}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
  {hm : ∀ j e, coefficients (poly j) e ∈ U j}
  {τ ξ : ℝ}
  {stride : X → ℕ}
  {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
  {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
  [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {A}
  {Deck : Fin m → Type*}
  {Ω Pivot : Type*}
  [Fintype Pivot]
  {LG LM : Type}
  [LieRing LG]
  [LieAlgebra ℚ LG]
  [LieRing LM]
  [LieAlgebra ℚ LM]
  [TopologicalSpace (ℝ ⊗[ℚ] LG)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)]
  [T2Space (ℝ ⊗[ℚ] LG)]
  {s d₀ t : ℕ}
  {D : RationalFilteredNilmanifold LG s d₀}
  {Fmark : NilpotentLieFiltration LM t}
  {φ : LG →ₗ⁅ℚ⁆ LM}
  {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
  {keep : LayerSamplerVariables G I n B → Prop}
  {cost p pLocal pNative r periodCap coverCap : ℝ}
  {Lip : ℝ≥0}

theorem exp_correlation_bound {q : ℝ}
    (hbudget : r + verticalDecompositionBudget q + 2 ≤ p) :
    Real.exp (-p) ≤ Real.exp (-r) / (2 * Real.exp (verticalDecompositionBudget q)) := by
  apply (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans
  apply (le_div_iff₀ (by positivity)).mpr
  have he : Real.exp (-(r + verticalDecompositionBudget q + 2)) *
      (2 * Real.exp (verticalDecompositionBudget q)) = 2 * Real.exp (-r - 2) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [he]
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ Real.exp 2 * Real.exp (-r - 2) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (-r) := by rw [← Real.exp_add]; congr 1; ring

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformExternalMarkedAffineSliceFreezingDictionary
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} {N : I → ℕ} {q r : ℕ}

variable [Fintype I] [DecidableEq I]

theorem composeSlice_isDenseCommonStrideBox_of_fraction (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (hq : 0 < q) (hr : 0 < r)
    {cost θ denominator : ℝ} (hS : IsDenseCommonStrideBox N cost S.integerPoints)
    (hθ : 0 < θ) (hdenominator : 0 < denominator)
    (hT : ∀ i, θ * S.length i / denominator ≤ (T.length i : ℝ)) :
    IsDenseCommonStrideBox N (cost + Real.log (denominator / θ))
      (S.composeSlice T).integerPoints := by
  apply S.composeSlice_isDenseCommonStrideBox T hq hr hS
  intro i
  simpa only [Real.exp_neg, Real.exp_log (div_pos hdenominator hθ), inv_div,
    ← mul_div_assoc, mul_comm (S.length i : ℝ) θ] using hT i

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientAmplitudeDensityTest
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_affine_coefficient_amplitude_density_test (m : ℕ) :
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
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (amplitude : (Option K × I → ℝ) → ℂ) (_hamp : ∀ x, ‖amplitude x‖ ≤ 1)
    {Lip : ℝ≥0} (_hLip : LipschitzWith Lip amplitude) (_hLipP : (Lip : ℝ) ≤ Real.exp P)
    (D : CoefficientTorus (K := K) U → ℝ) (_hD : Integrable D μ)
    (_hDmass : (∫ x, D x ∂μ) = 1)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (amplitude (fun t => (z t : ℝ) / V t) *
          (D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ))) : ℂ))) -
      ∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        amplitude (fun t => (z t : ℝ) / V t)‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hnormalization⟩ := exists_affine_coefficient_amplitude_fourier_normalization m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    amplitude hamp Lip hLip hLipP D hD hDmass η hη happrox
  obtain ⟨hZ, hfourier⟩ := hnormalization hP hn hd U hC hCP frequency hbound c hB hBP hcoefficients
    p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    amplitude hamp hLip hLipP
  refine ⟨hZ, ?_⟩
  apply selectedResidueSmoothPMF_weighted_coefficient_density U μ frequency c stride G V hV hZ
    (fun z => affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ)))
    (fun z => amplitude (fun t => (z t : ℝ) / V t)) (fun z _ => hamp _) D hD hDmass hη happrox
  simpa only [coefficientTorusFourierSum, coefficientTorusCharacter_sample U _ p hp hm] using hfourier

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedFiniteNestedForwardAllDegreePaddedSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable def preparedFiniteNestedForwardAllDegreeSeed
    {outerDepth innerDepth cutoff : ℕ} (A : ℕ) (constants : ℕ → ℕ) (x : ℝ)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : ℝ :=
  candidateNestedForwardSeed A constants innerDepth k.1.val x

@[simp] theorem preparedFiniteNestedForwardAllDegreeSeed_slot {outerDepth innerDepth cutoff : ℕ}
    (A : ℕ) (constants : ℕ → ℕ) (x : ℝ)
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeSeed A constants x (outer, inner, degree, direct) =
      candidateNestedForwardSeed A constants innerDepth outer.val x := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_seed
    (outerDepth innerDepth cutoff A : ℕ) (constants : ℕ → ℕ) (x : ℝ) :
    preparedFiniteNestedForwardAllDegreeSeed A constants x
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) =
      candidateNestedForwardSeed A constants innerDepth outerDepth x := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceArrays
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

noncomputable def preparedFiniteForwardInnerSourceExponent (Cdirect Cresource : ℕ) : ℕ :=
  Classical.choose (exists_preparedFiniteForwardPairedResource_budget Cdirect Cresource)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarNestedPowerDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedFiniteNestedForwardFixedCenterThreshold
    {outerDepth innerDepth cutoff : ℕ} (A : ℕ) (constants : ℕ → ℕ)
    (x gainLog stageLog : ℝ)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : ℝ :=
  let seed := preparedFiniteNestedForwardAllDegreeSeed A constants x k
  Real.exp (-(2 * preparedFiniteForwardModelPrecision A constants k.2.1.val seed gainLog stageLog +
    4 * preparedFiniteForwardWork A constants k.2.1.val seed + 8))

end Erdos3.VectorPolynomial

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

theorem rationalTagProjectionComplement_coordinate_exp_bound
    (P : Matrix T T ℚ) {p h : ℝ} (hp : 0 ≤ p) (hh : 0 ≤ h)
    (hdim : (Fintype.card T : ℝ) ≤ p)
    (hP : ∀ i j, rationalLogHeight (P i j) ≤ h) (x : T → ℝ) (i : T) :
    |rationalTagProjectionComplement P x i| ≤ Real.exp (p + h + 1) * ‖x‖ := by
  have hentry : ∀ i j, |(P i j : ℝ)| ≤ Real.exp h := fun i j =>
    (rational_abs_real_le_numerator (P i j)).trans
      ((rationalLogHeight_le_iff _ _).mp (hP i j)).1
  apply (rationalTagProjectionComplement_coordinate_bound P (Real.exp_nonneg _) hentry x i).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hdimexp : (Fintype.card T : ℝ) ≤ Real.exp p :=
    hdim.trans (by linarith [Real.add_one_le_exp p])
  have h1 : 1 ≤ Real.exp (p + h) := Real.one_le_exp_iff.mpr (add_nonneg hp hh)
  calc
    1 + (Fintype.card T : ℝ) * Real.exp h ≤ 1 + Real.exp p * Real.exp h := by gcongr
    _ = 1 + Real.exp (p + h) := by rw [Real.exp_add]
    _ ≤ 2 * Real.exp (p + h) := by linarith
    _ ≤ Real.exp 1 * Real.exp (p + h) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (p + h + 1) := by rw [← Real.exp_add]; congr 1; ring

theorem rationalTagProjectionComplement_denominator_grid
    (P : Matrix T T ℚ) (D l : ℕ)
    (hP : ∀ i j, ∃ z : ℤ, (D : ℝ) * (P i j : ℝ) = z)
    (x : T → ℝ) (hx : x ∈ realDenominatorGrid l) :
    rationalTagProjectionComplement P x ∈ realDenominatorGrid (D * l) :=
  real_matrix_complement_linearMap_specified_denominator_grid
    (fun i j => (P i j : ℝ)) D l hP x hx

theorem rationalTagProjectionComplement_integer_grid
    (P : Matrix T T ℚ) (D : ℕ)
    (hP : ∀ i j, ∃ z : ℤ, (D : ℝ) * (P i j : ℝ) = z)
    (x : T → ℤ) :
    ∃ z : T → ℤ, ∀ i,
      (D : ℝ) * rationalTagProjectionComplement P (fun j => (x j : ℝ)) i = (z i : ℝ) := by
  have hx : (fun j => (x j : ℝ)) ∈ realDenominatorGrid 1 :=
    ⟨x, by ext j; simp⟩
  obtain ⟨z, hz⟩ := rationalTagProjectionComplement_denominator_grid P D 1 hP _ hx
  refine ⟨z, fun i => ?_⟩
  have hi := congrFun hz i
  simpa only [mul_one, Pi.smul_apply, smul_eq_mul] using hi.symm

end Erdos3

end

end OAI
end


