-- Prove2me | Definitions.Def_OAIHecke78B000
-- name    : OAIHecke78B000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T19:23:52.448134+00:00
-- url     : https://prove2.me/theorems/60f8abed-ec4e-449a-8351-410aaa537755
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 1 of 16
-- statement:
--   Definitions bundle 1 of 16 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0) and from the vendored library modules of PrimeNumberTheoremAnd that OpenAI's development uses (with OpenAI's compatibility patches), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports no other bundle of this split. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Compat`, `CompatSimp`, `Arithmetic.EisensteinCoordinates`, `Mellin.ExponentialSmoothing`, `Mellin.LogProfiles`, `ChineseRemainder.AdditiveCharacters`, `GaussSum.ChineseRemainder`, `Arithmetic.EisensteinIdeals`, `GaussSum.FiniteFourier`, `Arithmetic.EisensteinEmbedding`, `Cusp.MatrixPhases`, `GaussSum.CubicNormalization`, `GaussSum.SexticNormalization`, `GaussSum.LocalProductAssembly`, `GaussSum.RamifiedTracePhase`, `Arithmetic.LatticeCount`, `GaussSum.QuadraticTrace`, `GaussSum.QuadraticNormalization`, `Mellin.LocalNonvanishing`, `Arithmetic.NormFiberMellin`, `Fourier.PositiveLogProfiles`, `Hecke.LocalEulerIdentities`, `Hecke.PrimeExtraction`, `Eisenstein.GreenIdentity`, `CubicSieve.PooledRows`, `CubicSieve.DyadicKernel`, `CubicSieve.ReopeningSeparation`, `RowCompletion.PolynomialHeight`, `Mellin.SixthPowerAverage`, `GaussSum.ActiveReindexing`, `CenteredExceptionalCount`, `FiniteFourier`, `FiniteConductor`, `CharacterTransport`, `ConductorBounds`, `ConductorPresentation`, `CubicSieve.Poisson`, `Descent.PhysicalExponents`, `Descent.Marks`, `Descent.Poisson`, `Descent.SourceHybrid`, `Descent.SecondSeparatedColumns`, `Descent.SecondGenerator`, `Descent.FirstModeColumns`, `Descent.FirstChildWindows`, `Descent.GlobalPrincipalMassPrefactor`, `Descent.FirstOriginalProfileLiveSupport`, `Descent.CompleteMarkedPool`, `Descent.CanonicalLongGeometry`, `Descent.SlotProducts`, `Reflection.Sector`, `Reflection.Moving`, `Reflection.ExtractedEnergy`, `Reflection.Shape`, `Reflection.KernelGeometry`, `Reflection.KernelSeparation`, `Reflection.MarkedRestriction`, `Reflection.SlotChoices`, `Reflection.TupleMasks`, `Reflection.SupportedChoices`, `Reflection.CubeSlotChoices`, `Reflection.CubeSlotSource`, `Reflection.ChoiceTransport`, `Reflection.ShapeWeights`, `Reflection.InactiveRows`, `Reflection.PunctureLists`, `Descent.ShortReflectedEnergy`, `Hecke.DetectorFourierSeparation`, `ThetaProduct`, `EisensteinTheta`, `Hecke.Theta`, `Hecke.Family`, `Hecke.Coordinates`, `LatticeSummability`, `Hecke.ThetaSeries`, `Hecke.FamilySeries`, `ResidueCharacter`, `IdealCharacter`, `Hecke.Operations`, `PeriodicThetaRegularity`, `ThetaRegularity`, `Hecke.Strip`, `Vendor.PrimeNumberTheoremAnd.Sobolev`, `Vendor.PrimeNumberTheoremAnd.Fourier`, `Vendor.PrimeNumberTheoremAnd.SmoothExistence`, `Vendor.PrimeNumberTheoremAnd.Wiener`, `IdealMangoldt`, `PrimeCounting.IdealPrimeMass`, `Hecke.PrimePowers`, `RayOrthogonality`, `RayQuotient`, `Moments.Correlation`, `Hecke.PrimeAmplitudeBins`, `Moments.FullCorrelation`, `Moments.CommonSupport`, `Detector.ScalarTable`, `PrimeCounting.AnnularPrimeMass`, `Detector.IdealFactorization`, `Detector.ZeroIndex`, `Detector.HighExcludedEuler`, `Detector.MarkedValuations`, `Detector.PrincipalProduct`, `Detector.PrincipalResidueActual`, `Dictionary.InverseRawRadial`, `Dictionary.InverseMarkedPadding`, `Dictionary.InverseMarkedReferenceTuples`, `Dictionary.InverseMarkedReferenceProducts`, `Inversion.InitialCommonRatios`, `Inversion.InitialOverlapFourier`, `Inversion.InitialOverlapIdealFourier`, `Inversion.InitialCommonProfile`, `Inversion.InitialCommonCutoff`, `Inversion.InitialExcludedPool`, `Moments.Rankin`, `Moments.RankinCount`, `Moments.HeckeWindowEnergy`, `Inversion.InitialExcludedPeriod`, `Moments.PartitionNorm`, `Moments.Forcing`, `Moments.LiveSupport`, `Moments.NonprincipalGate`, `Dictionary.InverseMarkedReferenceReindex`, `Dictionary.InverseMarkedReferenceArithmetic`, `Dictionary.InverseAssignedCount`, `Moments.DescentLedger`, `Moments.DyadicCount`, `Inversion.InitialDyadicAssemblySourceCaps`, `Inversion.InitialDyadicTailGates`, `Detector.HighRowsZero`, `PrimeRows.FirstTail`, `PrimeRows.MarkedProduct`, `Detector.SelectedPrimeSums`, `PrimeRows.CoarsePhysical`, `Detector.GaussianMellin`, `Detector.GaussianCompletion`, `Detector.GaussianPartition`, `Detector.GramCommonParam`, `Detector.LowCutoff`, `Detector.LowGramExceptional`, `Detector.GramFrequencySummation`, `Detector.LowActualIdealLists`, `Reflection.LowPunctureLists`, `Detector.LowGaussianRemote`, `Detector.PrincipalRemainderBounds`, `Detector.DetectorInverseMarkedField`, `Moments.ReflectedProfileMeasure`, `Dictionary.InverseRawRealRadial`, `Detector.DetectorInverseRawField`, `Moments.WholeDivisorShell`, `Moments.SlotRatios`, `Moments.RestrictedDomain`, `Moments.RestrictedSourceNormalization`, `Moments.FirstWholeKernel`, `Moments.SecondWholeKernel`, `Moments.SecondDyadicPartition`, `Moments.FirstPhysicalSourceSupport`, `Moments.AmplificationActiveFactor`, `Moments.AmplificationLiveEnergy`, `Moments.AmplificationChildEnergy`, `Moments.AmplificationErrorEnergy`, `Moments.AmplificationOriginalErrors`, `Moments.AmplificationEligibility`, `Moments.AmplificationRadicalFamily`, `Moments.OriginalRadialComparison`, `Energy.FirstAnnularAdmission`, `Moments.CommonLiveHeight`, `Moments.FixedQForcingCount`, `Moments.SecondFrozenSupported`, `Moments.SecondFrozenPhysical`, `Moments.SecondFrozenRatioCost`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B000

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Compat
  CompatSimp
  Arithmetic.EisensteinCoordinates
  Mellin.ExponentialSmoothing
  Mellin.LogProfiles
  ChineseRemainder.AdditiveCharacters
  GaussSum.ChineseRemainder
  Arithmetic.EisensteinIdeals
  GaussSum.FiniteFourier
  Arithmetic.EisensteinEmbedding
  Cusp.MatrixPhases
  GaussSum.CubicNormalization
  GaussSum.SexticNormalization
  GaussSum.LocalProductAssembly
  GaussSum.RamifiedTracePhase
  Arithmetic.LatticeCount
  GaussSum.QuadraticTrace
  GaussSum.QuadraticNormalization
  Mellin.LocalNonvanishing
  Arithmetic.NormFiberMellin
  Fourier.PositiveLogProfiles
  Hecke.LocalEulerIdentities
  Hecke.PrimeExtraction
  Eisenstein.GreenIdentity
  CubicSieve.PooledRows
  CubicSieve.DyadicKernel
  CubicSieve.ReopeningSeparation
  RowCompletion.PolynomialHeight
  Mellin.SixthPowerAverage
  GaussSum.ActiveReindexing
  CenteredExceptionalCount
  FiniteFourier
  FiniteConductor
  CharacterTransport
  ConductorBounds
  ConductorPresentation
  CubicSieve.Poisson
  Descent.PhysicalExponents
  Descent.Marks
  Descent.Poisson
  Descent.SourceHybrid
  Descent.SecondSeparatedColumns
  Descent.SecondGenerator
  Descent.FirstModeColumns
  Descent.FirstChildWindows
  Descent.GlobalPrincipalMassPrefactor
  Descent.FirstOriginalProfileLiveSupport
  Descent.CompleteMarkedPool
  Descent.CanonicalLongGeometry
  Descent.SlotProducts
  Reflection.Sector
  Reflection.Moving
  Reflection.ExtractedEnergy
  Reflection.Shape
  Reflection.KernelGeometry
  Reflection.KernelSeparation
  Reflection.MarkedRestriction
  Reflection.SlotChoices
  Reflection.TupleMasks
  Reflection.SupportedChoices
  Reflection.CubeSlotChoices
  Reflection.CubeSlotSource
  Reflection.ChoiceTransport
  Reflection.ShapeWeights
  Reflection.InactiveRows
  Reflection.PunctureLists
  Descent.ShortReflectedEnergy
  Hecke.DetectorFourierSeparation
  ThetaProduct
  EisensteinTheta
  Hecke.Theta
  Hecke.Family
  Hecke.Coordinates
  LatticeSummability
  Hecke.ThetaSeries
  Hecke.FamilySeries
  ResidueCharacter
  IdealCharacter
  Hecke.Operations
  PeriodicThetaRegularity
  ThetaRegularity
  Hecke.Strip
  Vendor.PrimeNumberTheoremAnd.Sobolev
  Vendor.PrimeNumberTheoremAnd.Fourier
  Vendor.PrimeNumberTheoremAnd.SmoothExistence
  Vendor.PrimeNumberTheoremAnd.Wiener
  IdealMangoldt
  PrimeCounting.IdealPrimeMass
  Hecke.PrimePowers
  RayOrthogonality
  RayQuotient
  Moments.Correlation
  Hecke.PrimeAmplitudeBins
  Moments.FullCorrelation
  Moments.CommonSupport
  Detector.ScalarTable
  PrimeCounting.AnnularPrimeMass
  Detector.IdealFactorization
  Detector.ZeroIndex
  Detector.HighExcludedEuler
  Detector.MarkedValuations
  Detector.PrincipalProduct
  Detector.PrincipalResidueActual
  Dictionary.InverseRawRadial
  Dictionary.InverseMarkedPadding
  Dictionary.InverseMarkedReferenceTuples
  Dictionary.InverseMarkedReferenceProducts
  Inversion.InitialCommonRatios
  Inversion.InitialOverlapFourier
  Inversion.InitialOverlapIdealFourier
  Inversion.InitialCommonProfile
  Inversion.InitialCommonCutoff
  Inversion.InitialExcludedPool
  Moments.Rankin
  Moments.RankinCount
  Moments.HeckeWindowEnergy
  Inversion.InitialExcludedPeriod
  Moments.PartitionNorm
  Moments.Forcing
  Moments.LiveSupport
  Moments.NonprincipalGate
  Dictionary.InverseMarkedReferenceReindex
  Dictionary.InverseMarkedReferenceArithmetic
  Dictionary.InverseAssignedCount
  Moments.DescentLedger
  Moments.DyadicCount
  Inversion.InitialDyadicAssemblySourceCaps
  Inversion.InitialDyadicTailGates
  Detector.HighRowsZero
  PrimeRows.FirstTail
  PrimeRows.MarkedProduct
  Detector.SelectedPrimeSums
  PrimeRows.CoarsePhysical
  Detector.GaussianMellin
  Detector.GaussianCompletion
  Detector.GaussianPartition
  Detector.GramCommonParam
  Detector.LowCutoff
  Detector.LowGramExceptional
  Detector.GramFrequencySummation
  Detector.LowActualIdealLists
  Reflection.LowPunctureLists
  Detector.LowGaussianRemote
  Detector.PrincipalRemainderBounds
  Detector.DetectorInverseMarkedField
  Moments.ReflectedProfileMeasure
  Dictionary.InverseRawRealRadial
  Detector.DetectorInverseRawField
  Moments.WholeDivisorShell
  Moments.SlotRatios
  Moments.RestrictedDomain
  Moments.RestrictedSourceNormalization
  Moments.FirstWholeKernel
  Moments.SecondWholeKernel
  Moments.SecondDyadicPartition
  Moments.FirstPhysicalSourceSupport
  Moments.AmplificationActiveFactor
  Moments.AmplificationLiveEnergy
  Moments.AmplificationChildEnergy
  Moments.AmplificationErrorEnergy
  Moments.AmplificationOriginalErrors
  Moments.AmplificationEligibility
  Moments.AmplificationRadicalFamily
  Moments.OriginalRadialComparison
  Energy.FirstAnnularAdmission
  Moments.CommonLiveHeight
  Moments.FixedQForcingCount
  Moments.SecondFrozenSupported
  Moments.SecondFrozenPhysical
  Moments.SecondFrozenRatioCost
-/

section

open Polynomial

theorem integrable_inv_one_add_mul_sq {b : ℝ} (hb : b ≠ 0) :
    MeasureTheory.Integrable fun x : ℝ ↦ (1 + (b * x) ^ 2)⁻¹ :=
  (integrable_inv_one_add_sq.comp_mul_left' hb).congr (by simp)

section SmoothUrysohn
open Set Function
open scoped Manifold ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ∞}

theorem exists_contDiff_support_eq_eq_one_iff {s t : Set E} (hs : IsOpen s) (ht : IsClosed t)
    (h : t ⊆ s) :
    ∃ f : E → ℝ, ContDiff ℝ n f ∧ range f ⊆ Icc 0 1 ∧ support f = s ∧ (∀ x, x ∈ t ↔ f x = 1) := by
  simpa [contMDiff_iff_contDiff] using exists_contMDiff_support_eq_eq_one_iff (I := 𝓘(ℝ, E)) hs ht h

end SmoothUrysohn

open scoped ContDiff in

lemma HasCompactSupport.exists_bound_iteratedFDeriv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F}
    (hf : HasCompactSupport f) (hf' : ContDiff 𝕜 ∞ f) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ m, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C := by
  have key i : ∃ C, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C :=
    (hf'.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hf.iteratedFDeriv i)
  choose A hA using key
  refine ⟨max 0 ((Finset.range (m + 1)).sup' ⟨0, by simp⟩ A), le_max_left _ _, fun i hi y ↦ ?_⟩
  grw [hA i y, ← le_max_right]
  exact Finset.le_sup' A (by grind)

theorem exists_sq_mul_squarefree {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
    (x : R) : ∃ e d : R, e ^ 2 * d = x ∧ Squarefree d := by
  induction x using WfDvdMonoid.induction_on_irreducible with
  | zero => exact ⟨0, 1, by simp, squarefree_one⟩
  | unit u hu => exact ⟨1, u, by simp, hu.squarefree⟩
  | mul z p hz hp ih =>
    obtain ⟨e, d, rfl, hd⟩ := ih
    by_cases hpd : p ∣ d
    · obtain ⟨d', rfl⟩ := hpd
      exact ⟨e * p, d', by simp only [pow_two]; ac_rfl, hd.of_mul_right⟩
    · refine ⟨e, d * p, by ac_rfl, ?_⟩
      rw [squarefree_mul_iff]
      exact ⟨(hp.isRelPrime_iff_not_dvd.mpr hpd).symm, hd, hp.squarefree⟩

@[fun_prop]
theorem Real.hasTemperateGrowth_sin :
    Real.sin.HasTemperateGrowth := by
  refine ⟨Real.contDiff_sin, fun n ↦ ⟨0, 1, fun x ↦ ?_⟩⟩
  simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using Real.abs_iteratedDeriv_sin_le_one n x

@[fun_prop]
theorem Real.hasTemperateGrowth_cos :
    Real.cos.HasTemperateGrowth := by
  refine ⟨Real.contDiff_cos, fun n ↦ ⟨0, 1, fun x ↦ ?_⟩⟩
  simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using Real.abs_iteratedDeriv_cos_le_one n x

@[fun_prop]
theorem Complex.hasTemperateGrowth_exp_mul_I :
    (fun x : ℝ ↦ Complex.exp (x * Complex.I)).HasTemperateGrowth := by
  simp only [Complex.exp_ofReal_mul_I]
  fun_prop

theorem IsOpenQuotientMap.secondCountableTopology {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {π : X → Y} [SecondCountableTopology X]
    (h : IsOpenQuotientMap π) : SecondCountableTopology Y :=
  h.isQuotientMap.secondCountableTopology h.isOpenMap

@[to_additive OAIHeckeCompat.addFiniteIndex_comap]
instance OAIHeckeCompat.finiteIndex_comap {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (H' : Subgroup G') [H'.FiniteIndex] : (H'.comap f).FiniteIndex :=
  ⟨by
    rw [Subgroup.index_comap]
    exact fun h => H'.index_ne_zero_of_finite <| H'.index_eq_zero_of_relIndex_eq_zero h⟩

theorem MeasureTheory.IntegrableOn.re {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
    {μ : MeasureTheory.Measure α} {s : Set α} {f : α → 𝕜}
    (hf : MeasureTheory.IntegrableOn f s μ) :
    MeasureTheory.IntegrableOn (fun x ↦ RCLike.re (f x)) s μ :=
  MeasureTheory.Integrable.re hf

theorem MeasureTheory.IntegrableOn.im {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
    {μ : MeasureTheory.Measure α} {s : Set α} {f : α → 𝕜}
    (hf : MeasureTheory.IntegrableOn f s μ) :
    MeasureTheory.IntegrableOn (fun x ↦ RCLike.im (f x)) s μ :=
  MeasureTheory.Integrable.im hf

namespace LinearMap

section extendOfIsometry

variable {𝕜 𝕜₂ E Eₗ F : Type*} [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂]
  [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup Eₗ] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ]
  [NormedAddCommGroup F] [Module 𝕜₂ F] [IsBoundedSMul 𝕜₂ F] [CompleteSpace F]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ₁₂] F) {e : E →ₗ[𝕜] Eₗ}

noncomputable def extendOfIsometry (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) :
    Eₗ →ₛₗᵢ[σ₁₂] F where
  toLinearMap := f.extendOfNorm e
  norm_map' := by
    refine h_dense.induction ?_ (isClosed_eq (by fun_prop) continuous_norm)
    rintro x ⟨y, rfl⟩
    norm_cast
    rw [LinearMap.extendOfNorm_eq h_dense (by use 1; simp [h_norm]), h_norm y]

@[simp]
theorem extendOfIsometry_eq (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) (x : E) :
    f.extendOfIsometry h_dense h_norm (e x) = f x :=
  LinearMap.extendOfNorm_eq h_dense ⟨1, fun x ↦ by simp [h_norm x]⟩ x

end extendOfIsometry

end LinearMap

@[to_additive]
theorem Subgroup.FiniteIndex.map_of_surjective {G G' : Type*} [Group G] [Group G']
    (H : Subgroup G) {f : G →* G'} [H.FiniteIndex] (hf : Function.Surjective f) :
    (H.map f).FiniteIndex where
  index_ne_zero :=
    ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero (H.index_map_dvd hf)
end

section

open scoped ContDiff

@[simp] theorem OAIHeckeCompat.natCast_le_infty (j : ℕ) : (j : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.2 le_top

@[simp] theorem OAIHeckeCompat.int_toNat_ofNat (n : ℕ) :
    (no_index (OfNat.ofNat n : ℤ)).toNat = OfNat.ofNat n := Int.toNat_natCast n
end

section

namespace OAI

open scoped BigOperators

namespace ShortDraft

abbrev EisensteinCoordinates := ℤ × ℤ

def eisensteinMul (x y : EisensteinCoordinates) : EisensteinCoordinates :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

def eisensteinNorm (x : EisensteinCoordinates) : ℤ :=
  x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2

theorem eisenstein_norm_mul (x y : EisensteinCoordinates) :
    eisensteinNorm (eisensteinMul x y) = eisensteinNorm x * eisensteinNorm y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  dsimp [eisensteinNorm, eisensteinMul]
  ring

theorem eisenstein_norm_nonneg (x : EisensteinCoordinates) :
    0 ≤ eisensteinNorm x := by
  rcases x with ⟨a, b⟩
  dsimp [eisensteinNorm]
  nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]

end ShortDraft

open MulChar AddChar

end OAI
end

section

namespace OAI

open scoped BigOperators
open MulChar AddChar

open scoped BigOperators

namespace AnalyticBridge

variable {Ω : Type*}

structure CRTChoice where
  J : ℕ
  C : ℕ
  e : ℕ
  v : ℕ
  s : ℕ
  J2 : ℕ
  b1 : ℕ
  b2 : ℕ
  A1 : ℕ
  A2 : ℕ
  d : ℕ
  kpp : ℕ
  deriving DecidableEq

end AnalyticBridge

open Filter Asymptotics MeasureTheory
open scoped Topology

end OAI
end

section

namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace FiniteRingSieve

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

noncomputable local instance : Fintype (MulChar R ℂ) := Fintype.ofFinite _

omit [DecidableEq R] in
theorem sum_chars_zero {a : R} (ha : a ≠ 1) :
    (∑ χ : MulChar R ℂ, χ a) = 0 := by
  obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity R ℂ ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' => rfl

theorem sum_chars (a : R) :
    (∑ χ : MulChar R ℂ, χ a) =
      if a = 1 then (Fintype.card Rˣ : ℂ) else 0 := by
  split_ifs with ha
  · subst a
    simp only [map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hc : Fintype.card (MulChar R ℂ) = Fintype.card Rˣ := by
      simpa only [Nat.card_eq_fintype_card] using
        MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity R ℂ
    exact_mod_cast hc
  · exact sum_chars_zero ha

theorem unit_char_orthogonal (u v : Rˣ) :
    (∑ χ : MulChar R ℂ, star (χ (u : R)) * χ (v : R)) =
      if u = v then (Fintype.card Rˣ : ℂ) else 0 := by
  calc
    _ = ∑ χ : MulChar R ℂ, χ ((u⁻¹ * v : Rˣ) : R) := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit,
        Units.val_mul, map_mul]
    _ = if ((u⁻¹ * v : Rˣ) : R) = 1 then (Fintype.card Rˣ : ℂ) else 0 :=
      sum_chars _
    _ = _ := by simp only [Units.val_eq_one, inv_mul_eq_one]

end FiniteRingSieve

open MeasureTheory Real
open scoped FourierTransform SchwartzMap

open scoped ContDiff

namespace FourierBridge

theorem schwartz_log_inversion (g : 𝓢(ℝ, ℂ)) (y : ℝ) :
    g y = ∫ t : ℝ,
      Complex.exp ((↑(2 * Real.pi * inner ℝ t y) * Complex.I)) * (𝓕 g) t := by
  have hinv : (𝓕⁻ (𝓕 g) : 𝓢(ℝ, ℂ)) = g := by simp
  have h := congrArg (fun f : 𝓢(ℝ, ℂ) => f y) hinv
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at h
  simpa only [smul_eq_mul] using h.symm

theorem fourier_coefficient_moment (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖ ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
        (SchwartzMap.seminorm ℝ (J + (volume : Measure ℝ).integrablePower) 0) (𝓕 g)) := by
  simpa using SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume (𝓕 g) J 0

theorem fourier_seminorm_from_derivative_integrals
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) :
    (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      (2 : ℝ) ^ k *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
          ∫ v : ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g v‖ := by
  have hpoint (w : ℝ) :=
    Real.pow_mul_norm_iteratedFDeriv_fourier_le
      (K := ⊤) (N := ⊤) (f := (g : ℝ → ℂ)) (g.smooth ⊤)
      (by intro a b ha hb; exact g.integrable_pow_mul_iteratedFDeriv volume a b)
      (k := 0) (n := k) (by simp) (by simp) w
  have hpoint' (w : ℝ) :
      ‖w‖ ^ k * ‖(𝓕 g) w‖ ≤
        (2 : ℝ) ^ k *
          ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
            ∫ v : ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g v‖ := by
    simpa [SchwartzMap.fourier_coe] using hpoint w
  apply SchwartzMap.seminorm_le_bound ℝ k 0 (𝓕 g) (by positivity)
  intro w
  simpa using hpoint' w

theorem uniform_fourier_seminorm_transfer
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (_hC : 0 ≤ C)
    (hsource : ∀ i ≤ k,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      (2 : ℝ) ^ k * (k + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C := by
  let V : ℝ := 2 ^ (volume : Measure ℝ).integrablePower *
    ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hI (i : ℕ) (hi : i ≤ k) :
      S * (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤ V * C := by
    have hbase := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume g 0 i
    have hbase' :
        (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤
          V * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) := by
      simpa [V] using hbase
    calc
      S * (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤
          S * (V * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)) :=
        mul_le_mul_of_nonneg_left hbase' hS
      _ = V * (S * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)) := by ring
      _ ≤ V * C := mul_le_mul_of_nonneg_left (hsource i hi) hV
  have hFourier := fourier_seminorm_from_derivative_integrals g k
  calc
    S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      S * ((2 : ℝ) ^ k *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
          ∫ t : ℝ, ‖t‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g t‖) :=
      mul_le_mul_of_nonneg_left hFourier hS
    _ = (2 : ℝ) ^ k *
      ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
        S * (∫ t : ℝ, ‖t‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g t‖) := by
      simp only [Finset.mul_sum]
      ring_nf
    _ ≤ (2 : ℝ) ^ k *
      ∑ _p ∈ Finset.range 1 ×ˢ Finset.range (k + 1), V * C := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : p.1 = 0 := by
        have hlt := Finset.mem_range.mp (Finset.mem_product.mp hp).1
        omega
      have hp2 : p.2 ≤ k := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
      simpa [hp0] using hI p.2 hp2
    _ = (2 : ℝ) ^ k * (k + 1) * V * C := by
      simp []
      ring
    _ = (2 : ℝ) ^ k * (k + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C := rfl

theorem uniform_fourier_coefficient_moment
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖) ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((2 : ℝ) ^ 0 * (0 + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C +
        (2 : ℝ) ^ (J + (volume : Measure ℝ).integrablePower) *
          (J + (volume : Measure ℝ).integrablePower + 1) *
          (2 ^ (volume : Measure ℝ).integrablePower *
            ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C) := by
  let p := (volume : Measure ℝ).integrablePower
  let V : ℝ := 2 ^ p * ∫ t : ℝ, (1 + ‖t‖) ^ (-(p : ℝ))
  let K := J + p
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hfourier_zero := uniform_fourier_seminorm_transfer g 0 S C hS hC
    (by intro i hi; exact hsource i (by omega))
  have hfourier_K := uniform_fourier_seminorm_transfer g K S C hS hC
    (by intro i hi; exact hsource i (by simpa [K, p] using hi))
  have hmoment := fourier_coefficient_moment g J
  calc
    S * (∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖) ≤
        S * (V * ((SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
          (SchwartzMap.seminorm ℝ K 0) (𝓕 g))) :=
      mul_le_mul_of_nonneg_left (by simpa [V, K, p] using hmoment) hS
    _ = V * (S * (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
        S * (SchwartzMap.seminorm ℝ K 0) (𝓕 g)) := by ring
    _ ≤ V * ((2 : ℝ) ^ 0 * (0 + 1) * V * C +
        (2 : ℝ) ^ K * (K + 1) * V * C) := by
      apply mul_le_mul_of_nonneg_left _ hV
      exact add_le_add (by simpa [V] using hfourier_zero)
        (by simpa [K, V] using hfourier_K)
    _ = _ := by simp [V, K, p, Nat.cast_add]

noncomputable def coefficientMomentBound (J : ℕ) (C : ℝ) : ℝ :=
  let p := (volume : Measure ℝ).integrablePower
  let V : ℝ := 2 ^ p * ∫ t : ℝ, (1 + ‖t‖) ^ (-(p : ℝ))
  V * (V * C + (2 : ℝ) ^ (J + p) * (J + p + 1) * V * C)

theorem coefficientMomentBound_nonneg (J : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ coefficientMomentBound J C := by
  unfold coefficientMomentBound
  positivity

theorem uniform_fourier_one_plus_moment
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) ≤
      (2 : ℝ) ^ J *
        (coefficientMomentBound 0 C + coefficientMomentBound J C) := by
  let b := 𝓕 g
  have hI0 : Integrable (fun t : ℝ => ‖b t‖) volume := by
    simpa using b.integrable_pow_mul volume 0
  have hIJ : Integrable (fun t : ℝ => ‖t‖ ^ J * ‖b t‖) volume :=
    b.integrable_pow_mul volume J
  have hIrhs : Integrable
      (fun t : ℝ => (2 : ℝ) ^ J *
        (‖b t‖ + ‖t‖ ^ J * ‖b t‖)) volume :=
    (hI0.add hIJ).const_mul _
  have hpoint (t : ℝ) :
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
        (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
    have hpow := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg t) J
    have htwo : (2 : ℝ) ^ (J - 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)
    calc
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
          (2 : ℝ) ^ (J - 1) * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ J * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ := by
        gcongr
      _ = (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
        simp; ring
  have hintegral :
      (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤
        (2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by
    calc
      _ ≤ ∫ t : ℝ, (2 : ℝ) ^ J *
          (‖b t‖ + ‖t‖ ^ J * ‖b t‖) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (by intro t; positivity))
          hIrhs (Filter.Eventually.of_forall hpoint)
      _ = (2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by
        rw [integral_const_mul, integral_add hI0 hIJ]
  have hbound0 := uniform_fourier_coefficient_moment g 0 S C hS hC
    (by intro i hi; exact hsource i (by omega))
  have hboundJ := uniform_fourier_coefficient_moment g J S C hS hC hsource
  calc
    S * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤
        S * ((2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖))) :=
      mul_le_mul_of_nonneg_left hintegral hS
    _ = (2 : ℝ) ^ J *
        (S * (∫ t : ℝ, ‖b t‖) +
          S * (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by ring
    _ ≤ (2 : ℝ) ^ J *
        (coefficientMomentBound 0 C + coefficientMomentBound J C) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · simpa [coefficientMomentBound, b] using hbound0
      · simpa [coefficientMomentBound, b] using hboundJ

noncomputable def logPhase (t y : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I)

theorem logPhase_add (t u v : ℝ) :
    logPhase t (u + v) = logPhase t u * logPhase t v := by
  unfold logPhase
  convert (preTransparency := .instances) Complex.exp_add _ _ using 1 ; push_cast ; ring_nf

theorem logPhase_zero (t : ℝ) : logPhase t 0 = 1 := by
  simp [logPhase]

theorem logPhase_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ℝ) (z : ι → ℝ) :
    logPhase t (∑ i ∈ s, z i) = ∏ i ∈ s, logPhase t (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [logPhase_zero]
  | @insert i s hi ih => simp [hi, logPhase_add, ih]

theorem coupled_cutoff_active
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (V : ℝ → ℂ) (a y M : ι → ℝ)
    (hwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hVone : ∀ s,
      |s| ≤ ∑ j : ι, |a j| * M j → V s = 1)
    (hprod : (∏ j : ι, W j (y j)) ≠ 0) :
    V (∑ j : ι, a j * y j) = 1 := by
  classical
  apply hVone
  calc
    |∑ j : ι, a j * y j| ≤ ∑ j : ι, |a j * y j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : ι, |a j| * M j := by
      apply Finset.sum_le_sum
      intro j hj
      have hnonzero : W j (y j) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hprod) j (Finset.mem_univ j)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hwindow j (y j) hnonzero) (abs_nonneg _)

theorem exists_complex_smooth_cutoff (T : ℝ) (hT : 0 ≤ T) :
    ∃ V : ℝ → ℂ,
      HasCompactSupport V ∧
      ContDiff ℝ ∞ V ∧
      (∀ s, |s| ≤ T → V s = 1) ∧
      tsupport V ⊆ Set.Icc (-(T + 1)) (T + 1) ∧
      V 0 = 1 := by
  let U : Set ℝ := Set.Ioo (-(T + 1)) (T + 1)
  let K : Set ℝ := Set.Icc (-T) T
  have hU : IsOpen U := isOpen_Ioo
  have hK : IsClosed K := isClosed_Icc
  have hKU : K ⊆ U := by
    intro s hs
    rcases hs with ⟨hleft, hright⟩
    constructor <;> linarith
  obtain ⟨f, hf, _, hsupport, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hU hK hKU
  let V : ℝ → ℂ := fun s => (f s : ℂ)
  have hf' : ContDiff ℝ ∞ f := by simpa using hf
  have hVs : ContDiff ℝ ∞ V := Complex.ofRealCLM.contDiff.comp hf'
  have hVsupport : Function.support V = Function.support f := by
    ext s
    simp [V, Function.mem_support]
  have hVsupportI : Function.support V ⊆
      Set.Icc (-(T + 1)) (T + 1) := by
    intro s hs
    rw [hVsupport, hsupport] at hs
    exact ⟨hs.1.le, hs.2.le⟩
  have hVtsupportI : tsupport V ⊆
      Set.Icc (-(T + 1)) (T + 1) :=
    closure_minimal hVsupportI isClosed_Icc
  have hVc : HasCompactSupport V :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hVsupportI
  have hone' : ∀ s, |s| ≤ T → V s = 1 := by
    intro s hs
    have hsK : s ∈ K := by simpa [K, abs_le] using hs
    have hfs : f s = 1 := (hone s).mp hsK
    simp [V, hfs]
  exact ⟨V, hVc, hVs, hone', hVtsupportI,
    hone' 0 (by simpa using hT)⟩

theorem exists_complex_smooth_cutoff_with_derivative_bounds
    (T : ℝ) (K : ℕ) (hT : 0 ≤ T) :
    ∃ (V : ℝ → ℂ) (CW : ℝ),
      HasCompactSupport V ∧ ContDiff ℝ ∞ V ∧
      (∀ s, |s| ≤ T → V s = 1) ∧
      0 ≤ CW ∧
      (∀ i ≤ K, ∀ y, ‖iteratedFDeriv ℝ i V y‖ ≤ CW) ∧
      (∀ y,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V y‖ ≠ 0) →
          Real.exp (-(T + 1)) ≤ Real.exp y ∧
          Real.exp y ≤ Real.exp (T + 1) ∧ |y| ≤ T + 1) := by
  obtain ⟨V, hVc, hVs, hVone, hVsupport, _⟩ :=
    exists_complex_smooth_cutoff T hT
  obtain ⟨CW, hCW, hVderiv⟩ :=
    hVc.exists_bound_iteratedFDeriv hVs K
  refine ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, ?_⟩
  intro y hy
  obtain ⟨i, hi, hnonzero⟩ := hy
  have hyderiv : y ∈ Function.support (iteratedFDeriv ℝ i V) := by
    simpa [Function.mem_support] using hnonzero
  have hysupport : y ∈ tsupport V :=
    (support_iteratedFDeriv_subset i) hyderiv
  have hyinterval := hVsupport hysupport
  have hylower : -(T + 1) ≤ y := hyinterval.1
  have hyupper : y ≤ T + 1 := hyinterval.2
  constructor
  · exact Real.exp_le_exp.mpr hylower
  constructor
  · exact Real.exp_le_exp.mpr hyupper
  · exact abs_le.mpr ⟨hylower, hyupper⟩

noncomputable def schwartzDerivativeDecayConstant
    (F : 𝓢(ℝ, ℂ)) (M K : ℕ) : ℝ :=
  (2 : ℝ) ^ M *
    ∑ i ∈ Finset.range (K + 1),
      ((SchwartzMap.seminorm ℝ 0 i) F +
        (SchwartzMap.seminorm ℝ M i) F)

end FourierBridge

end OAI
end

section

namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

namespace ShortDraftTrace

open Complex
open scoped ComplexConjugate

section Generic

variable (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
  (hconj : conj ω = ω ^ 2)

include hω hconj

omit hconj in
lemma lam_ne_zero : (1 + 2 * ω : ℂ) ≠ 0 := by
  intro h
  have hw : ω = -(1 : ℂ) / 2 := by linear_combination h / 2
  rw [hw] at hω
  norm_num at hω

lemma conj_lam : conj (1 + 2 * ω) = -(1 + 2 * ω) := by
  rw [map_add, map_one, map_mul, map_ofNat, hconj]
  linear_combination 2 * hω

omit hconj in
lemma omega_sub_square : ω - ω ^ 2 = 1 + 2 * ω := by
  linear_combination -hω

theorem trace_div_lam (a b : ℤ) :
    ((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω) +
      conj (((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)) = (b : ℂ) := by
  have hl := lam_ne_zero ω hω
  simp only [map_div₀, map_add, map_intCast, map_mul, hconj,
    conj_lam ω hω hconj]
  rw [div_neg, ← sub_eq_add_neg, ← sub_div]
  calc
    ((a : ℂ) + (b : ℂ) * ω - ((a : ℂ) + (b : ℂ) * ω ^ 2)) /
        (1 + 2 * ω) = (b : ℂ) * (ω - ω ^ 2) / (1 + 2 * ω) := by ring
    _ = (b : ℂ) := by rw [omega_sub_square ω hω]; field_simp

theorem trace_character_period (a b : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)) +
       conj (((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)))) = 1 := by
  rw [trace_div_lam ω hω hconj a b]
  calc
    _ = Complex.exp ((b : ℂ) * (2 * Real.pi * Complex.I)) := by congr 1; ring
    _ = Complex.exp (2 * Real.pi * Complex.I) ^ b := Complex.exp_int_mul _ _
    _ = 1 := by rw [Complex.exp_two_pi_mul_I, one_zpow]

end Generic

noncomputable def ω₃ : ℂ := ((-1 : ℂ) + (Real.sqrt 3 : ℝ) * Complex.I) / 2

theorem omega_sq : ω₃ ^ 2 = -ω₃ - 1 := by
  have hs : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs' : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    norm_cast
  have hquad : ω₃ ^ 2 + ω₃ + 1 =
      (3 + ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * Complex.I ^ 2) / 4 := by
    unfold ω₃
    ring
  rw [hs', Complex.I_sq] at hquad
  norm_num at hquad
  linear_combination hquad

theorem omega_conj : conj ω₃ = ω₃ ^ 2 := by
  rw [omega_sq]
  unfold ω₃
  simp only [map_div₀, map_add, map_neg, map_one, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem eisenstein_trace_period (a b : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)) +
       conj (((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)))) = 1 := by
  apply trace_character_period ω₃
  · rw [omega_sq]; ring
  · exact omega_conj

noncomputable def breveE : AddChar ℂ ℂ where
  toFun z := Complex.exp (2 * Real.pi * Complex.I * (z + conj z))
  map_zero_eq_one' := by simp
  map_add_eq_mul' z w := by
    have harg : 2 * Real.pi * Complex.I * (z + w + conj (z + w)) =
        2 * Real.pi * Complex.I * (z + conj z) +
          2 * Real.pi * Complex.I * (w + conj w) := by
      rw [map_add]
      ring
    rw [harg, Complex.exp_add]

theorem breveE_period_lam (a b : ℤ) :
    breveE (((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)) = 1 := by
  exact eisenstein_trace_period a b

theorem lam_eq_sqrt3_mul_I :
    1 + 2 * ω₃ = (Real.sqrt 3 : ℝ) * Complex.I := by
  unfold ω₃
  ring

theorem sub_conj_eq (z : ℂ) :
    z - conj z = 2 * (z.im : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [Complex.mul_im]
    ring

theorem breveE_div_lam_eq_e (z : ℂ) :
    breveE (z / (1 + 2 * ω₃)) =
      Complex.exp (4 * Real.pi * Complex.I * (z.im / Real.sqrt 3)) := by
  have hs : (Real.sqrt 3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hl : ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hs) Complex.I_ne_zero
  change Complex.exp (2 * Real.pi * Complex.I *
    (z / (1 + 2 * ω₃) + conj (z / (1 + 2 * ω₃)))) = _
  rw [lam_eq_sqrt3_mul_I]
  have hc : conj (((Real.sqrt 3 : ℝ) : ℂ) * Complex.I) =
      -(((Real.sqrt 3 : ℝ) : ℂ) * Complex.I) := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [map_div₀, hc, div_neg, ← sub_eq_add_neg, ← sub_div, sub_conj_eq]
  congr 1
  field_simp
  ring

end ShortDraftTrace

end OAI
end

section

namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open Finset Complex

open scoped Classical

open scoped Classical

namespace IdealGaussCRT

variable {T R S : Type*} [CommRing T] [CommRing R] [CommRing S]

def leftAddChar (e : T ≃+* R × S) (ψ : AddChar T ℂ) : AddChar R ℂ where
  toFun z := ψ (e.symm (z, 0))
  map_zero_eq_one' := by
    change ψ (e.symm (0 : R × S)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ (e.symm (z + w, 0)) = ψ (e.symm (z, 0)) * ψ (e.symm (w, 0))
    rw [show (z + w, (0 : S)) = (z, 0) + (w, 0) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

def rightAddChar (e : T ≃+* R × S) (ψ : AddChar T ℂ) : AddChar S ℂ where
  toFun z := ψ (e.symm (0, z))
  map_zero_eq_one' := by
    change ψ (e.symm (0 : R × S)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ (e.symm (0, z + w)) = ψ (e.symm (0, z)) * ψ (e.symm (0, w))
    rw [show ((0 : R), z + w) = (0, z) + (0, w) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

noncomputable def quotientAddChar {A : Type*} [CommRing A]
    (I : Ideal A) (ψ : AddChar A ℂ)
    (hper : ∀ a : A, a ∈ I → ψ a = 1) : AddChar (A ⧸ I) ℂ where
  toFun := fun x => Quotient.liftOn' x ψ (by
    intro a b hab
    have hsub : a - b ∈ I := I.quotientRel_def.mp hab
    have h := ψ.map_add_eq_mul (a - b) b
    rw [sub_add_cancel] at h
    rw [hper _ hsub, one_mul] at h
    exact h)
  map_zero_eq_one' := by
    change ψ 0 = 1
    exact AddChar.map_zero_eq_one ψ
  map_add_eq_mul' := by
    intro x y
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    exact AddChar.map_add_eq_mul ψ a b

@[simp] theorem quotientAddChar_mk {A : Type*} [CommRing A]
    (I : Ideal A) (ψ : AddChar A ℂ)
    (hper : ∀ a : A, a ∈ I → ψ a = 1) (a : A) :
    quotientAddChar I ψ hper (Ideal.Quotient.mk I a) = ψ a := rfl

theorem principal_coprime_of_bezout {A : Type*} [CommRing A]
    {a b u v : A} (h : u * a + v * b = 1) :
    IsCoprime (Ideal.span {a}) (Ideal.span {b}) := by
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨u * a, ?_, v * b, ?_, h⟩
  · exact Ideal.mem_span_singleton.mpr ⟨u, by ring⟩
  · exact Ideal.mem_span_singleton.mpr ⟨v, by ring⟩

theorem bezout_of_principal_coprime {A : Type*} [CommRing A]
    {a b : A} (h : IsCoprime (Ideal.span {a}) (Ideal.span {b})) :
    ∃ u v : A, u * a + v * b = 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hy
  refine ⟨u, v, ?_⟩
  rw [hu, hv] at hxy
  convert (preTransparency := .instances) hxy using 1; ring

noncomputable def rawTraceChar {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A) : AddChar A ℂ where
  toFun x := ψ (ι x / (ι c * lam))
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [map_add, add_div, AddChar.map_add_eq_mul]

theorem rawTraceChar_period {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A)
    (hc : ι c ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)
    (x : A) (hx : x ∈ Ideal.span {c}) :
    rawTraceChar ι ψ lam c x = 1 := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  rw [hy]
  change ψ (ι (c * y) / (ι c * lam)) = 1
  rw [map_mul]
  have hfrac : ι c * ι y / (ι c * lam) = ι y / lam := by
    field_simp
  rw [hfrac]
  exact hbase y

noncomputable def traceModChar {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A)
    (hc : ι c ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    AddChar (A ⧸ Ideal.span {c}) ℂ :=
  quotientAddChar (Ideal.span {c}) (rawTraceChar ι ψ lam c)
    (rawTraceChar_period ι ψ lam c hc hlam hbase)

@[simp] theorem traceModChar_mk {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A)
    (hc : ι c ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) (x : A) :
    traceModChar ι ψ lam c hc hlam hbase
      (Ideal.Quotient.mk (Ideal.span {c}) x) =
      ψ (ι x / (ι c * lam)) := rfl

noncomputable def traceProdChar {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (a b : A)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    AddChar (A ⧸ (Ideal.span {a}) * (Ideal.span {b})) ℂ :=
  quotientAddChar ((Ideal.span {a}) * (Ideal.span {b}))
    (rawTraceChar ι ψ lam (a * b)) (by
      intro x hx
      have hx' : x ∈ Ideal.span {a * b} := by
        simpa only [Ideal.span_singleton_mul_span_singleton] using hx
      exact rawTraceChar_period ι ψ lam (a * b)
        (by simpa only [map_mul] using mul_ne_zero ha hb)
        hlam hbase x hx')

@[simp] theorem traceProdChar_mk {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (a b : A)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) (x : A) :
    traceProdChar ι ψ lam a b ha hb hlam hbase
      (Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) x) =
      ψ (ι x / (ι (a * b) * lam)) := rfl

theorem bezout_inverse_left {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) :
    (Ideal.Quotient.mk (Ideal.span {a}) b) *
      (Ideal.Quotient.mk (Ideal.span {a}) v) = 1 := by
  rw [← map_mul]
  apply Ideal.Quotient.eq.mpr
  change b * v - 1 ∈ Ideal.span {a}
  rw [Ideal.mem_span_singleton]
  refine ⟨-u, ?_⟩
  calc
    b * v - 1 = b * v - (u * a + v * b) := by rw [hbez]
    _ = a * -u := by ring

theorem gauss_shift_bezout_left {A : Type*} [CommRing A]
    {a b u v : A} [Fintype (A ⧸ Ideal.span {a})]
    (hbez : u * a + v * b = 1)
    (χ : MulChar (A ⧸ Ideal.span {a}) ℂ)
    (ψ : AddChar (A ⧸ Ideal.span {a}) ℂ) :
    gaussSum χ (ψ.mulShift (Ideal.Quotient.mk (Ideal.span {a}) v)) =
      χ (Ideal.Quotient.mk (Ideal.span {a}) b) * gaussSum χ ψ := by
  let mb := Ideal.Quotient.mk (Ideal.span {a}) b
  let mv := Ideal.Quotient.mk (Ideal.span {a}) v
  have hprod : mb * mv = 1 := bezout_inverse_left hbez
  have hu : IsUnit mv := IsUnit.of_mul_eq_one_right mb hprod
  have hχ : χ mb * χ mv = 1 := by rw [← map_mul, hprod, map_one]
  have hshift := gaussSum_mulShift χ ψ hu.unit
  have hshift' : χ mv * gaussSum χ (ψ.mulShift mv) = gaussSum χ ψ := by
    simpa only [hu.unit_spec] using hshift
  calc
    gaussSum χ (ψ.mulShift mv) =
        (χ mb * χ mv) * gaussSum χ (ψ.mulShift mv) := by rw [hχ, one_mul]
    _ = χ mb * (χ mv * gaussSum χ (ψ.mulShift mv)) := by ring
    _ = χ mb * gaussSum χ ψ := by rw [hshift']

end IdealGaussCRT

end

end OAI
end

section

namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

noncomputable section

namespace ActualEisensteinSieve

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

def omega : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

def lambda : O := omega - 1

def lambdaIdeal : Ideal O := Ideal.span {lambda}

theorem lambda_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

theorem lambda_maximal : lambdaIdeal.IsMaximal := by
  have hp : lambdaIdeal.IsPrime :=
    Ideal.isPrime_span_singleton_of_prime lambda_prime
  have hne : lambdaIdeal ≠ ⊥ := by
    exact Ideal.span_singleton_eq_bot.not.mpr lambda_prime.ne_zero
  exact hp.isMaximal hne

theorem lambda_card : Nat.card (O ⧸ lambdaIdeal) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [lambdaIdeal, lambda, omega,
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).card_quotient_toInteger_sub_one,
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).norm_toInteger_sub_one_of_prime_ne_two'
      (by decide)]
  norm_num

instance : lambdaIdeal.IsMaximal := lambda_maximal

theorem lambda_residue_odd : ringChar (O ⧸ lambdaIdeal) ≠ 2 := by
  classical
  let : Field (O ⧸ lambdaIdeal) := Ideal.Quotient.field lambdaIdeal
  let : Fintype (O ⧸ lambdaIdeal) := Fintype.ofFinite (O ⧸ lambdaIdeal)
  intro hchar
  have hcard := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card, lambda_card] at hcard
  norm_num at hcard

end ActualEisensteinSieve

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

namespace ShortDraftFiniteGaussFourier
open scoped Classical
open AddChar MulChar
variable {F : Type*} [Field F] [Fintype F]

theorem gauss_transform (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (h : F) :
    (∑ x : F, χ x * ψ (h * x)) =
      if h = 0 then 0 else (χ h)⁻¹ * gaussSum χ ψ := by
  classical
  by_cases hh : h = 0
  · subst h
    simp only [zero_mul, map_zero_eq_one, mul_one, ite_true]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  · have hu : IsUnit h := isUnit_iff_ne_zero.mpr hh
    have hshift := gaussSum_mulShift_eq χ ψ hu.unit
    simp only [gaussSum, AddChar.mulShift_apply] at hshift
    simpa only [hu.unit_spec, if_neg hh, inv_apply_eq_inv' χ h, gaussSum] using hshift

theorem product_gauss_transform
    {ι : Type*} [Fintype ι]
    (E : ι → Type*) [∀ i, Field (E i)] [∀ i, Fintype (E i)]
    (χ : ∀ i, MulChar (E i) ℂ) (ψ : ∀ i, AddChar (E i) ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : ∀ i, E i) :
    (∑ x : ∀ i, E i, ∏ i, χ i (x i) * ψ i (h i * x i)) =
      ∏ i, if h i = 0 then 0 else (χ i (h i))⁻¹ * gaussSum (χ i) (ψ i) := by
  classical
  calc
    (∑ x : ∀ i, E i, ∏ i, χ i (x i) * ψ i (h i * x i)) =
        ∏ i, ∑ x : E i, χ i x * ψ i (h i * x) := by
      simpa using (Fintype.prod_sum
        (fun i (x : E i) => χ i x * ψ i (h i * x))).symm
    _ = ∏ i, if h i = 0 then 0 else (χ i (h i))⁻¹ * gaussSum (χ i) (ψ i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact gauss_transform (χ i) (ψ i) (hχ i) (h i)

end ShortDraftFiniteGaussFourier

open Finset Complex

namespace ActualCubicChar

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]

omit [IsDomain R] in
theorem cubic_roots_surjective (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3) :
    Function.Surjective (restrictRootsOfUnity ρ 3) := by
  intro η
  have hη : ((η : Fˣ) : F) ^ 3 = 1 := by
    exact (mem_rootsOfUnity' 3 (η : Fˣ)).mp η.property
  obtain ⟨j, _, hj⟩ := hζF.eq_pow_of_pow_eq_one hη
  let z : rootsOfUnity 3 R := rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one
  refine ⟨z ^ j, ?_⟩
  apply rootsOfUnity.coe_injective
  change ρ (ζ ^ j) = ((η : Fˣ) : F)
  rw [map_pow]
  exact hj

noncomputable def cubic_roots_equiv (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3) :
    rootsOfUnity 3 R ≃* rootsOfUnity 3 F := by
  classical
  letI : Fintype (rootsOfUnity 3 R) := Fintype.ofFinite _
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  apply MulEquiv.ofBijective (restrictRootsOfUnity ρ 3)
  apply (Fintype.bijective_iff_surjective_and_card _).2
  constructor
  · exact cubic_roots_surjective ρ ζ hζ hζF
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hζ.card_rootsOfUnity, hζF.card_rootsOfUnity]

variable [Fintype F]

theorem euler_jacobi_sum_zero (m : ℕ)
    (hm : 2 * m < Fintype.card F - 1) :
    (∑ x : F, x ^ m * (1 - x) ^ m) = 0 := by
  classical
  simp_rw [sub_eq_add_neg, add_pow]
  simp only [one_pow, one_mul, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have he : m + (m - j) < Fintype.card F - 1 := by
    have hle : m - j ≤ m := Nat.sub_le m j
    omega
  calc
    (∑ x : F, x ^ m * ((-x) ^ (m - j) * ↑(m.choose j))) =
        ((-1 : F) ^ (m - j) * ↑(m.choose j)) *
          ∑ x : F, x ^ (m + (m - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [neg_pow, pow_add]
      ring
    _ = 0 := by rw [FiniteField.sum_pow_lt_card_sub_one F _ he]; ring

def euler_to_roots (m : ℕ) (hq : Fintype.card F - 1 = m * 3) :
    Fˣ →* rootsOfUnity 3 F where
  toFun u := rootsOfUnity.mkOfPowEq ((u : F) ^ m) (by
    rw [← pow_mul, ← hq]
    exact FiniteField.pow_card_sub_one_eq_one (u : F) u.ne_zero)
  map_one' := by
    apply rootsOfUnity.coe_injective
    simp
  map_mul' u v := by
    apply rootsOfUnity.coe_injective
    simp [mul_pow]

noncomputable def cubicResidueChar (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) : MulChar F R :=
  MulChar.ofUnitHom <|
    (Subgroup.subtype _).comp <|
      (cubic_roots_equiv ρ ζ hζ hζF).symm.toMonoidHom.comp
        (euler_to_roots m hq)

theorem cubicResidueChar_reduce_unit (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) (u : Fˣ) :
    ρ (cubicResidueChar ρ ζ hζ hζF m hq (u : F)) = (u : F) ^ m := by
  let e := cubic_roots_equiv ρ ζ hζ hζF
  simp only [cubicResidueChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply]
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (u : F) ^ m
  have he := e.apply_symm_apply (euler_to_roots m hq u)
  have he' := congrArg (fun v : rootsOfUnity 3 F => ((v : Fˣ) : F)) he
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (((euler_to_roots m hq u : rootsOfUnity 3 F) : Fˣ) : F) at he'
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (u : F) ^ m at he'
  exact he'

theorem cubicResidueChar_pow_three (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) :
    cubicResidueChar ρ ζ hζ hζF m hq ^ 3 = 1 := by
  apply MulChar.ext
  intro u
  rw [(cubicResidueChar ρ ζ hζ hζF m hq).pow_apply_coe,
    MulChar.one_apply_coe]
  simp only [cubicResidueChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply]
  let v : rootsOfUnity 3 R :=
    (cubic_roots_equiv ρ ζ hζ hζF).symm (euler_to_roots m hq u)
  change (((v : Rˣ) : R) ^ 3) = 1
  exact (mem_rootsOfUnity' 3 (v : Rˣ)).mp v.property

end ActualCubicChar

namespace ActualEisensteinCubic

section

open NumberField

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

def omega : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

def lambda : O := omega - 1

noncomputable instance quotientFintype (P : Ideal O) [P.IsMaximal] :
    Fintype (O ⧸ P) := Fintype.ofFinite _

noncomputable instance quotientField (P : Ideal O) [P.IsMaximal] :
    Field (O ⧸ P) := Ideal.Quotient.field P

theorem omega_primitive : IsPrimitiveRoot omega 3 := by
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot

def traceLambda : O := 1 + 2 * omega

theorem omega_reduced_primitive (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let ρ : O →+* O ⧸ P := Ideal.Quotient.mk P
  have hpow : (ρ omega) ^ 3 = 1 := by
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hne : ρ omega ≠ 1 := by
    intro he
    apply hgood
    have hz : ρ (omega - 1) = 0 := by rw [map_sub, he, map_one, sub_self]
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hz
  apply IsPrimitiveRoot.mk_of_lt _ (by decide) hpow
  intro l hl0 hl3
  have hl : l = 1 ∨ l = 2 := by omega
  rcases hl with rfl | rfl
  · simpa using hne
  · intro h2
    apply hne
    calc
      ρ omega = (ρ omega) ^ 2 * ρ omega := by rw [h2, one_mul]
      _ = (ρ omega) ^ 3 := by ring
      _ = 1 := hpow

theorem card_sub_one_div_three (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    3 ∣ Nat.card (O ⧸ P) - 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let hζ := omega_reduced_primitive P hgood
  let u : (O ⧸ P)ˣ := (hζ.isUnit (by decide)).unit
  have hu : IsPrimitiveRoot u 3 := hζ.isUnit_unit (by decide)
  have h := orderOf_dvd_natCard u
  rw [← hu.eq_orderOf] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using h

noncomputable def cubicChar (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) O := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  exact ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
    omega_primitive (omega_reduced_primitive P hgood) m hq

theorem cubicChar_reduce (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O ⧸ P) :
    (Ideal.Quotient.mk P) (cubicChar P hgood x) =
      x ^ ((Nat.card (O ⧸ P) - 1) / 3) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 0 < m := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  rw [Nat.card_eq_fintype_card]
  change (Ideal.Quotient.mk P)
      (ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
        omega_primitive (omega_reduced_primitive P hgood) m hq x) = x ^ m
  by_cases hx : x = 0
  · subst x
    rw [(ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
      omega_primitive (omega_reduced_primitive P hgood) m hq).map_zero,
      map_zero, zero_pow hm.ne']
  · let u : (O ⧸ P)ˣ := (isUnit_iff_ne_zero.mpr hx).unit
    have hu : (u : O ⧸ P) = x := (isUnit_iff_ne_zero.mpr hx).unit_spec
    rw [← hu]
    exact ActualCubicChar.cubicResidueChar_reduce_unit
      (Ideal.Quotient.mk P) omega omega_primitive
      (omega_reduced_primitive P hgood) m hq u

theorem cubicChar_pow_three (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : cubicChar P hgood ^ 3 = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  change ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
    omega_primitive (omega_reduced_primitive P hgood) m hq ^ 3 = 1
  exact ActualCubicChar.cubicResidueChar_pow_three
    (Ideal.Quotient.mk P) omega omega_primitive
    (omega_reduced_primitive P hgood) m hq

theorem cubicChar_ne_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : cubicChar P hgood ≠ 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 0 < m := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  intro hχ
  have hall : ∀ u : (O ⧸ P)ˣ, u ^ m = 1 := by
    intro u
    apply Units.ext
    have hr := cubicChar_reduce P hgood (u : O ⧸ P)
    rw [hχ, MulChar.one_apply_coe, map_one] at hr
    simpa only [Units.val_pow_eq_pow_val, Units.val_one,
      Nat.card_eq_fintype_card] using hr.symm
  have hdvd := (FiniteField.forall_pow_eq_one_iff (O ⧸ P) m).mp hall
  rw [hq] at hdvd
  have hle := Nat.le_of_dvd hm hdvd
  omega

theorem cubicChar_order (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : orderOf (cubicChar P hgood) = 3 := by
  have hdvd : orderOf (cubicChar P hgood) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (cubicChar_pow_three P hgood)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact False.elim ((cubicChar_ne_one P hgood) (orderOf_eq_one_iff.mp h1))
  · exact h3

theorem cubicJacobi_primary (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    ∃ z ∈ Algebra.adjoin ℤ {omega},
      jacobiSum (cubicChar P hgood) (cubicChar P hgood) =
        -1 + z * lambda ^ 2 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  simpa only [lambda] using
    (exists_jacobiSum_eq_neg_one_add (n := 3) (by decide)
      (cubicChar_pow_three P hgood) (cubicChar_pow_three P hgood)
      (by simpa only [Nat.card_eq_fintype_card] using card_sub_one_div_three P hgood)
      omega_primitive)

theorem cubicJacobi_mem_prime (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) ∈ P := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 2 * m < Fintype.card (O ⧸ P) - 1 := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  rw [jacobiSum, map_sum]
  simp_rw [map_mul, cubicChar_reduce P hgood]
  simp only [Nat.card_eq_fintype_card]
  exact ActualCubicChar.euler_jacobi_sum_zero m hm

theorem cubicJacobi_product (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹ =
        (Nat.card (O ⧸ P) : O) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let ι : O →+* K := algebraMap O K
  let ψ := (cubicChar P hgood).ringHomComp ι
  have hchar : ringChar K ≠ ringChar (O ⧸ P) := by
    rw [ringChar.eq_zero]
    exact (CharP.char_is_prime (O ⧸ P) (ringChar (O ⧸ P))).ne_zero.symm
  have hψ : ψ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff RingOfIntegers.coe_injective).mpr
      (cubicChar_ne_one P hgood)
  have hχ2 : cubicChar P hgood * cubicChar P hgood ≠ 1 := by
    intro h
    have hd : orderOf (cubicChar P hgood) ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [cubicChar_order P hgood] at hd
    norm_num at hd
  have hψ2 : ψ * ψ ≠ 1 := by
    rw [show ψ * ψ =
      (cubicChar P hgood * cubicChar P hgood).ringHomComp ι by
        exact (MulChar.ringHomComp_mul _ _ _).symm]
    exact (MulChar.ringHomComp_ne_one_iff RingOfIntegers.coe_injective).mpr hχ2
  have hprod := jacobiSum_mul_jacobiSum_inv hchar hψ hψ hψ2
  apply RingOfIntegers.coe_injective
  change ι (jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹) =
    ι (Nat.card (O ⧸ P) : O)
  rw [map_mul, ← jacobiSum_ringHomComp, ← jacobiSum_ringHomComp,
    ← MulChar.ringHomComp_inv]
  simpa only [ψ, Nat.card_eq_fintype_card, map_natCast] using hprod

noncomputable def conjK : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).pow_of_coprime 2 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by decide))

noncomputable def conjO : O ≃+* O :=
  RingOfIntegers.mapRingEquiv conjK.toRingEquiv

theorem conjO_omega : conjO omega = omega ^ 2 := by
  apply RingOfIntegers.coe_injective
  change conjK (IsCyclotomicExtension.zeta 3 ℚ K) =
    (IsCyclotomicExtension.zeta 3 ℚ K) ^ 2
  exact IsCyclotomicExtension.fromZetaAut_spec
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).pow_of_coprime 2 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by decide))

theorem conjO_cubic_root (x : O) (hx : x ^ 3 = 1) :
    conjO x = x ^ 2 := by
  obtain ⟨j, _, hj⟩ := omega_primitive.eq_pow_of_pow_eq_one hx
  rw [← hj, map_pow, conjO_omega]
  simp only [← pow_mul]
  rw [Nat.mul_comm]

theorem cubicChar_conj_eq_inv (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O ⧸ P) :
    conjO (cubicChar P hgood x) = (cubicChar P hgood)⁻¹ x := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let χ := cubicChar P hgood
  have hinv : χ⁻¹ = χ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using cubicChar_pow_three P hgood
  rw [hinv, χ.pow_apply' (by decide)]
  by_cases hx : x = 0
  · subst x
    rw [χ.map_zero, map_zero, zero_pow (by decide)]
  · have hχ3 : χ x ^ 3 = 1 := by
      rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
    exact conjO_cubic_root (χ x) hχ3

theorem cubicJacobi_conj (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    conjO (jacobiSum (cubicChar P hgood) (cubicChar P hgood)) =
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹ := by
  classical
  rw [jacobiSum, map_sum]
  simp_rw [map_mul, cubicChar_conj_eq_inv P hgood]
  rfl

theorem cubicJacobi_mul_conj (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      conjO (jacobiSum (cubicChar P hgood) (cubicChar P hgood)) =
        (Nat.card (O ⧸ P) : O) := by
  rw [cubicJacobi_conj P hgood]
  exact cubicJacobi_product P hgood

end

noncomputable def quadraticCharO (P : Ideal O) [P.IsMaximal] :
    MulChar (O ⧸ P) O := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  exact (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O)

theorem quadraticCharO_sq (P : Ideal O) [P.IsMaximal] :
    quadraticCharO P ^ 2 = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  change ((quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O)) ^ 2 = 1
  exact ((quadraticChar_isQuadratic (O ⧸ P)).comp (Int.castRingHom O)).sq_eq_one

noncomputable def sexticChar (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) O :=
  cubicChar P hgood ^ 2 * quadraticCharO P

theorem sexticChar_powers (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    sexticChar P hgood ^ 2 = cubicChar P hgood ∧
    sexticChar P hgood ^ 3 = quadraticCharO P ∧
    sexticChar P hgood ^ 6 = 1 := by
  have hc := cubicChar_pow_three P hgood
  have hq := quadraticCharO_sq P
  let c := cubicChar P hgood
  let q := quadraticCharO P
  have htwo : (c ^ 2 * q) ^ 2 = c := by
    calc
      (c ^ 2 * q) ^ 2 = c ^ 4 * q ^ 2 := by rw [mul_pow, ← pow_mul]
      _ = c := by rw [hq]; calc
        c ^ 4 * 1 = c ^ 3 * c := by group
        _ = c := by rw [hc, one_mul]
  have hthree : (c ^ 2 * q) ^ 3 = q := by
    calc
      (c ^ 2 * q) ^ 3 = (c ^ 3) ^ 2 * (q ^ 2) * q := by simp [mul_pow]; group
      _ = q := by rw [hc, hq]; group
  refine ⟨htwo, hthree, ?_⟩
  calc
    (c ^ 2 * q) ^ 6 = ((c ^ 2 * q) ^ 3) ^ 2 := by group
    _ = 1 := by rw [hthree, hq]

theorem lambda_not_dvd_two : ¬ lambda ∣ (2 : O) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hprime : Prime lambda :=
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'
  let I : Ideal O := Ideal.span {lambda}
  have hI : I.IsMaximal := by
    have hp : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hprime
    have hne : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hprime.ne_zero
    exact hp.isMaximal hne
  let : I.IsMaximal := hI
  let : Field (O ⧸ I) := Ideal.Quotient.field I
  let : Fintype (O ⧸ I) := Fintype.ofFinite _
  have hcard : Nat.card (O ⧸ I) = 3 := by
    change Nat.card (O ⧸ Ideal.span {omega - 1}) = 3
    rw [omega,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).card_quotient_toInteger_sub_one,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).norm_toInteger_sub_one_of_prime_ne_two'
        (by decide)]
    norm_num
  intro hdiv
  have hmem : (2 : O) ∈ I := (Ideal.mem_span_singleton).mpr hdiv
  have hzero : (2 : O ⧸ I) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  have hchar : ringChar (O ⧸ I) = 2 := by
    have hdvd : ringChar (O ⧸ I) ∣ 2 := (ringChar.spec (O ⧸ I) 2).mp hzero
    exact (Nat.prime_dvd_prime_iff_eq
      (CharP.char_is_prime (O ⧸ I) (ringChar (O ⧸ I))) Nat.prime_two).mp hdvd
  have heven := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card, hcard] at heven
  norm_num at heven

theorem conjK_ne_refl : conjK ≠ AlgEquiv.refl := by
  intro he
  have hw : omega ^ 2 = omega := by
    have hc : conjO omega = omega := by
      apply NumberField.RingOfIntegers.coe_injective
      change conjK (omega : K) = (omega : K)
      rw [he]
      rfl
    exact conjO_omega.symm.trans hc
  have hw1 : omega = 1 := by
    have hunit : IsUnit omega := omega_primitive.isUnit (by decide)
    apply (mul_left_cancel₀ hunit.ne_zero)
    calc
      omega * omega = omega ^ 2 := by ring
      _ = omega := hw
      _ = omega * 1 := by ring
  exact (omega_primitive.ne_one (by decide)) hw1

theorem galois_card_two : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by
  classical
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank ℚ K,
    IsCyclotomicExtension.finrank (n := 3) K
      (Polynomial.cyclotomic.irreducible_rat (by decide))]
  decide

theorem galois_univ_pair [DecidableEq (K ≃ₐ[ℚ] K)] :
    (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {(AlgEquiv.refl : K ≃ₐ[ℚ] K), conjK} := by
  symm
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, galois_card_two, Finset.card_pair]
  exact conjK_ne_refl.symm

theorem norm_eq_mul_conjK (p : O) :
    ((Algebra.norm ℚ (p : K) : ℚ) : K) = (p : K) * conjK (p : K) := by
  classical
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  have h := Algebra.norm_eq_prod_automorphisms ℚ (p : K)
  rw [galois_univ_pair, Finset.prod_pair conjK_ne_refl.symm] at h
  simpa using h

theorem norm_int_eq_mul_conjO (p : O) :
    ((Algebra.norm ℤ p : ℤ) : O) = p * conjO p := by
  apply NumberField.RingOfIntegers.coe_injective
  change ((Algebra.norm ℤ p : ℤ) : K) = (p : K) * conjK (p : K)
  have h := norm_eq_mul_conjK p
  rw [← Algebra.coe_norm_int p] at h
  exact h

theorem generator_mul_conj_eq_sign_card (P : Ideal O) [P.IsMaximal]
    (p : O) (hP : P = Ideal.span {p}) :
    p * conjO p = (Nat.card (O ⧸ P) : O) ∨
      p * conjO p = -(Nat.card (O ⧸ P) : O) := by
  have habs : (Algebra.norm ℤ p).natAbs = Nat.card (O ⧸ P) := by
    calc
      (Algebra.norm ℤ p).natAbs = Ideal.absNorm (Ideal.span {p}) :=
        (Ideal.absNorm_span_singleton p).symm
      _ = Ideal.absNorm P := by rw [← hP]
      _ = Nat.card (O ⧸ P) := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsq : (Algebra.norm ℤ p) * (Algebra.norm ℤ p) =
      (Nat.card (O ⧸ P) : ℤ) * (Nat.card (O ⧸ P) : ℤ) := by
    apply (Int.natAbs_eq_iff_mul_self_eq).mp
    simpa using habs
  have hzero : (Algebra.norm ℤ p - (Nat.card (O ⧸ P) : ℤ)) *
      (Algebra.norm ℤ p + (Nat.card (O ⧸ P) : ℤ)) = 0 := by
    nlinarith [hsq]
  rcases mul_eq_zero.mp hzero with hpos | hneg
  · left
    have heq : Algebra.norm ℤ p = (Nat.card (O ⧸ P) : ℤ) := sub_eq_zero.mp hpos
    simp [← norm_int_eq_mul_conjO p, heq]
  · right
    have heq : Algebra.norm ℤ p = -(Nat.card (O ⧸ P) : ℤ) := add_eq_zero_iff_eq_neg.mp hneg
    simp [← norm_int_eq_mul_conjO p, heq]

theorem cubicJacobi_unit_multiple_of_principal (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p}) :
    ∃ u : Oˣ, jacobiSum (cubicChar P hgood) (cubicChar P hgood) = p * u := by
  classical
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  have hdiv : p ∣ J := (Ideal.mem_span_singleton).mp (hP ▸ cubicJacobi_mem_prime P hgood)
  obtain ⟨v, hv⟩ := hdiv
  have hqne : (Nat.card (O ⧸ P) : O) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hnorm := generator_mul_conj_eq_sign_card P p hP
  have hpne : p * conjO p ≠ 0 := by
    rcases hnorm with h | h
    · rw [h]; exact hqne
    · rw [h]; exact neg_ne_zero.mpr hqne
  have hprod : (p * conjO p) * (v * conjO v) = (Nat.card (O ⧸ P) : O) := by
    calc
      (p * conjO p) * (v * conjO v) = (p * v) * conjO (p * v) := by
        rw [map_mul]; ring
      _ = J * conjO J := by rw [hv]
      _ = (Nat.card (O ⧸ P) : O) := cubicJacobi_mul_conj P hgood
  have hvnorm : v * conjO v = 1 ∨ v * conjO v = -1 := by
    rcases hnorm with hpos | hneg
    · left
      apply mul_left_cancel₀ hpne
      calc
        (p * conjO p) * (v * conjO v) = (Nat.card (O ⧸ P) : O) := hprod
        _ = (p * conjO p) * 1 := by rw [hpos]; ring
    · right
      apply mul_left_cancel₀ hpne
      calc
        (p * conjO p) * (v * conjO v) = (Nat.card (O ⧸ P) : O) := hprod
        _ = (p * conjO p) * -1 := by rw [hneg]; ring
  have hvunit : IsUnit v := by
    rcases hvnorm with h | h
    · exact IsUnit.of_mul_eq_one (conjO v) h
    · apply IsUnit.of_mul_eq_one (-conjO v)
      rw [mul_neg, h]
      ring
  refine ⟨hvunit.unit, ?_⟩
  simpa only [hvunit.unit_spec] using hv

theorem cubicJacobi_eq_neg_primary_generator_of_principal (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) = -p := by
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  obtain ⟨u, hJu⟩ := cubicJacobi_unit_multiple_of_principal P hgood p hP
  change J = p * (u : O) at hJu
  obtain ⟨z, _, hJ⟩ := cubicJacobi_primary P hgood
  have hJmod : lambda ^ 2 ∣ J + 1 := by
    refine ⟨z, ?_⟩
    dsimp [J]
    rw [hJ]
    ring
  have hucong : lambda ^ 2 ∣ (u : O) + 1 := by
    have heq : (u : O) + 1 = (J + 1) - (p - 1) * (u : O) := by
      rw [hJu]
      ring
    rw [heq]
    exact dvd_sub hJmod (dvd_mul_of_dvd_left hprimary _)
  have hunit : u = 1 ∨ u = -1 := by
    apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) u
    refine ⟨(-1 : ℤ), ?_⟩
    simpa only [lambda, omega, Int.cast_neg, Int.cast_one, sub_neg_eq_add] using hucong
  rcases hunit with h1 | hneg
  · have htwo : lambda ^ 2 ∣ (2 : O) := by
      simpa [h1, one_add_one_eq_two] using hucong
    exact False.elim (lambda_not_dvd_two ((dvd_pow_self lambda (by decide)).trans htwo))
  · rw [hneg] at hJu
    simpa only [Units.val_neg, Units.val_one, mul_neg, mul_one] using hJu

theorem cubicJacobi_generates_prime (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    P = Ideal.span {jacobiSum (cubicChar P hgood) (cubicChar P hgood)} := by
  classical
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  have hnormJ : Algebra.norm ℤ J = (Nat.card (O ⧸ P) : ℤ) := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → O))
    change ((Algebra.norm ℤ J : ℤ) : O) = (Nat.card (O ⧸ P) : O)
    rw [norm_int_eq_mul_conjO]
    exact cubicJacobi_mul_conj P hgood
  have habsJ : Ideal.absNorm (Ideal.span {J}) = Nat.card (O ⧸ P) := by
    rw [Ideal.absNorm_span_singleton, hnormJ]
    simp
  have habsP : Ideal.absNorm P = Nat.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hle : Ideal.span {J} ≤ P :=
    (Ideal.span_singleton_le_iff_mem P).mpr (cubicJacobi_mem_prime P hgood)
  obtain ⟨Q, hQ⟩ := (Ideal.dvd_iff_le).mpr hle
  have hq : Nat.card (O ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hQnorm : Ideal.absNorm Q = 1 := by
    have heq : Nat.card (O ⧸ P) = Nat.card (O ⧸ P) * Ideal.absNorm Q := by
      calc
        Nat.card (O ⧸ P) = Ideal.absNorm (Ideal.span {J}) := habsJ.symm
        _ = Ideal.absNorm (P * Q) := by rw [hQ]
        _ = Ideal.absNorm P * Ideal.absNorm Q := map_mul Ideal.absNorm P Q
        _ = Nat.card (O ⧸ P) * Ideal.absNorm Q := by rw [habsP]
    exact (mul_left_cancel₀ hq (heq.symm.trans (by ring)))
  have hQtop : Q = ⊤ := Ideal.absNorm_eq_one_iff.mp hQnorm
  change P = Ideal.span {J}
  rw [hQ, hQtop, ← Ideal.one_eq_top, mul_one]

theorem cubicJacobi_exists_primary_generator (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    ∃ p : O, P = Ideal.span {p} ∧ lambda ^ 2 ∣ p - 1 ∧
      jacobiSum (cubicChar P hgood) (cubicChar P hgood) = -p := by
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  refine ⟨-J, ?_, ?_, by simp [J]⟩
  · have h := cubicJacobi_generates_prime P hgood
    simpa only [J, Ideal.span_singleton_neg] using h
  · obtain ⟨z, _, hJ⟩ := cubicJacobi_primary P hgood
    refine ⟨-z, ?_⟩
    dsimp [J]
    rw [hJ]
    ring

theorem quadraticCharO_ne_one (P : Ideal O) [P.IsMaximal]
    (hchar : ringChar (O ⧸ P) ≠ 2) : quadraticCharO P ≠ 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  change (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O) ≠ 1
  exact (MulChar.ringHomComp_ne_one_iff
    (Int.cast_injective (α := O))).2 (quadraticChar_ne_one hchar)

theorem sexticChar_order (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (sexticChar P hgood) = 6 := by
  have h2 := (sexticChar_powers P hgood).1
  have h3 := (sexticChar_powers P hgood).2.1
  have h6 := (sexticChar_powers P hgood).2.2
  have hdiv : orderOf (sexticChar P hgood) ∣ 6 :=
    orderOf_dvd_of_pow_eq_one h6
  have hne2 : orderOf (sexticChar P hgood) ≠ 2 := by
    intro he
    have hχ2 := pow_orderOf_eq_one (sexticChar P hgood)
    rw [he, h2] at hχ2
    exact cubicChar_ne_one P hgood hχ2
  have hne3 : orderOf (sexticChar P hgood) ≠ 3 := by
    intro he
    have hχ3 := pow_orderOf_eq_one (sexticChar P hgood)
    rw [he, h3] at hχ3
    exact quadraticCharO_ne_one P hchar hχ3
  have hne1 : orderOf (sexticChar P hgood) ≠ 1 := by
    intro he
    have hχ1 := orderOf_eq_one_iff.mp he
    rw [hχ1] at h2
    exact cubicChar_ne_one P hgood (by simpa using h2.symm)
  have hne0 : orderOf (sexticChar P hgood) ≠ 0 := by
    intro he
    norm_num [he] at hdiv
  have hpos : 0 < orderOf (sexticChar P hgood) := Nat.pos_of_ne_zero hne0
  have hle : orderOf (sexticChar P hgood) ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv
  have hne4 : orderOf (sexticChar P hgood) ≠ 4 := by
    intro he
    norm_num [he] at hdiv
  have hne5 : orderOf (sexticChar P hgood) ≠ 5 := by
    intro he
    norm_num [he] at hdiv
  omega

theorem sexticChar_reduce_unit (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (u : (O ⧸ P)ˣ) :
    (Ideal.Quotient.mk P) (sexticChar P hgood (u : O ⧸ P)) =
      (u : O ⧸ P) ^ ((Nat.card (O ⧸ P) - 1) / 6) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let N := Fintype.card (O ⧸ P)
  let m := (N - 1) / 6
  have hthree : 3 ∣ N - 1 := by
    simpa only [N, Nat.card_eq_fintype_card] using card_sub_one_div_three P hgood
  have hodd : N % 2 = 1 := FiniteField.odd_card_of_char_ne_two hchar
  have hN : 1 < N := Fintype.one_lt_card
  have hsix : 6 ∣ N - 1 := by omega
  have hsize : N - 1 = 6 * m := by
    dsimp [m]
    exact (Nat.mul_div_cancel_left' hsix).symm
  have hthird : (N - 1) / 3 = 2 * m := by omega
  have hhalf : N / 2 = 3 * m := by omega
  let ρ : O →+* O ⧸ P := Ideal.Quotient.mk P
  have hquad : ρ (quadraticCharO P (u : O ⧸ P)) =
      (u : O ⧸ P) ^ (N / 2) := by
    change (quadraticChar (O ⧸ P) (u : O ⧸ P) : O ⧸ P) = _
    exact quadraticChar_eq_pow_of_char_ne_two' hchar (u : O ⧸ P)
  have hcub : ρ (cubicChar P hgood (u : O ⧸ P)) =
      (u : O ⧸ P) ^ ((N - 1) / 3) := by
    simpa only [N, Nat.card_eq_fintype_card] using cubicChar_reduce P hgood (u : O ⧸ P)
  have hfermat : (u : O ⧸ P) ^ (N - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero u)
  change ρ ((cubicChar P hgood ^ 2 * quadraticCharO P) (u : O ⧸ P)) = _
  rw [MulChar.mul_apply, MulChar.pow_apply', map_mul, map_pow, hcub, hquad]
  rw [hthird, hhalf]
  simpa only [Nat.card_eq_fintype_card, N, m] using
    (show ((u : O ⧸ P) ^ (2 * m)) ^ 2 * (u : O ⧸ P) ^ (3 * m) =
      (u : O ⧸ P) ^ m by
      calc
        ((u : O ⧸ P) ^ (2 * m)) ^ 2 * (u : O ⧸ P) ^ (3 * m) =
            (u : O ⧸ P) ^ (7 * m) := by
              rw [← pow_mul, ← pow_add]
              congr 1
              omega
        _ = (u : O ⧸ P) ^ m * (u : O ⧸ P) ^ (N - 1) := by
          rw [hsize, ← pow_add]; congr 1; omega
        _ = (u : O ⧸ P) ^ m := by rw [hfermat, mul_one])
  all_goals norm_num

end ActualEisensteinCubic

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace EisensteinEmbedding

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

noncomputable def ζ : K := IsCyclotomicExtension.zeta 3 ℚ K
noncomputable def pb : PowerBasis ℤ O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis

noncomputable def omega3 : ℂ := ((-1 : ℂ) + (Real.sqrt 3 : ℝ) * Complex.I) / 2

theorem omega3_sq : omega3 ^ 2 + omega3 + 1 = 0 := by
  have hs : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs' : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by norm_cast
  have hquad : omega3 ^ 2 + omega3 + 1 =
      (3 + ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * Complex.I ^ 2) / 4 := by
    unfold omega3
    ring
  rw [hs', Complex.I_sq] at hquad
  norm_num at hquad
  exact hquad

theorem omega3_im : omega3.im = Real.sqrt 3 / 2 := by
  simp [omega3]

theorem omega3_im_ne_zero : omega3.im ≠ 0 := by
  rw [omega3_im]
  exact div_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num))) (by norm_num)

theorem lam_ne_zero (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    1 + 2 * w ≠ 0 := by
  intro h
  have hw' : w = -(1 : ℂ) / 2 := by linear_combination h / 2
  rw [hw'] at hw
  norm_num at hw

theorem pb_minpoly : minpoly ℤ pb.gen =
    (Polynomial.X : Polynomial ℤ) ^ 2 + Polynomial.X + 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hgen : pb.gen = hζ.toInteger := by
    simpa only [pb] using hζ.integralPowerBasis_gen
  rw [hgen]
  calc
    minpoly ℤ (hζ.toInteger : O) =
        minpoly ℤ (hζ.toInteger : K) :=
          (NumberField.RingOfIntegers.minpoly_coe hζ.toInteger).symm
    _ = minpoly ℤ (IsCyclotomicExtension.zeta 3 ℚ K) := by
          exact congrArg (minpoly ℤ) hζ.coe_toInteger
    _ = Polynomial.cyclotomic 3 ℤ :=
          (Polynomial.cyclotomic_eq_minpoly hζ (by decide)).symm
    _ = _ := Polynomial.cyclotomic_three ℤ

noncomputable def embedding (w : ℂ) (hw : w ^ 2 + w + 1 = 0) : O →+* ℂ :=
  (pb.lift w (by
    rw [pb_minpoly]
    simpa only [map_add, map_pow, map_one, Polynomial.aeval_X] using hw)).toRingHom

theorem embedding_gen (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    embedding w hw pb.gen = w := by
  exact pb.lift_gen w (by
    rw [pb_minpoly]
    simpa only [map_add, map_pow, map_one, Polynomial.aeval_X] using hw)

theorem pb_dim : pb.dim = 2 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hdim := hζ.integralPowerBasis_dim
  have htot : Nat.totient 3 = 2 := by decide
  simpa only [pb, htot] using hdim

theorem exists_ab (x : O) : ∃ a b : ℤ, x = a + b * pb.gen := by
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let c := pb.basis.repr x
  have h := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    have hi := i.isLt
    have hd := pb_dim
    simp only [i0, i1, Fin.ext_iff]
    omega
  rw [huniv, Finset.sum_insert (by simp [i0, i1]), Finset.sum_singleton] at h
  refine ⟨c i0, c i1, ?_⟩
  simpa only [pb.coe_basis, i0, i1, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, zsmul_eq_mul, mul_one] using h.symm

theorem embedding_apply_ab (w : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (a b : ℤ) :
    embedding w hw (a + b * pb.gen : O) =
      (a : ℂ) + (b : ℂ) * w := by
  simp only [map_add, map_mul, map_intCast, embedding_gen]

theorem embedding_injective (w : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (him : w.im ≠ 0) : Function.Injective (embedding w hw) := by
  intro x y hxy
  have hz : embedding w hw (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨a, b, hrepr⟩ := exists_ab (x - y)
  rw [hrepr, embedding_apply_ab] at hz
  have himz := congrArg Complex.im hz
  have hb : b = 0 := by
    simp only [Complex.add_im, Complex.intCast_im, zero_add,
      Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      zero_mul, add_zero, Complex.zero_im] at himz
    have hbc : (b : ℝ) = 0 := (mul_eq_zero.mp himz).resolve_right him
    exact_mod_cast hbc
  have ha : a = 0 := by
    rw [hb, Int.cast_zero, zero_mul, add_zero] at hz
    exact_mod_cast hz
  have hzero : x - y = 0 := by rw [hrepr, ha, hb]; simp
  exact sub_eq_zero.mp hzero

theorem trace_period_on_ringOfIntegers
    (w : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (ψ : AddChar ℂ ℂ) (lam : ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * w) / lam) = 1) :
    ∀ x : O, ψ (embedding w hw x / lam) = 1 := by
  intro x
  obtain ⟨a, b, hrepr⟩ := exists_ab x
  rw [hrepr, embedding_apply_ab]
  exact hperiod a b

end EisensteinEmbedding

namespace ConcreteTraceCRT

open EisensteinEmbedding IdealGaussCRT

noncomputable def eisEmbedding : O →+* ℂ := embedding omega3 omega3_sq

theorem eisEmbedding_injective : Function.Injective eisEmbedding :=
  embedding_injective omega3 omega3_sq omega3_im_ne_zero

theorem eisEmbedding_ne_zero {a : O} (ha : a ≠ 0) : eisEmbedding a ≠ 0 := by
  intro h
  exact ha (eisEmbedding_injective (by simpa using h))

noncomputable def eisLam : ℂ := 1 + 2 * omega3

theorem eisLam_ne_zero : eisLam ≠ 0 := lam_ne_zero omega3 omega3_sq

theorem eisPeriod (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = 1) :
    ∀ x : O, ψ (eisEmbedding x / eisLam) = 1 :=
  trace_period_on_ringOfIntegers omega3 omega3_sq ψ eisLam hperiod

def coordinateSubring : Subring ℂ where
  carrier := {z | ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * omega3}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a + c, b + d, ?_⟩
    push_cast
    ring
  neg_mem' := by
    rintro x ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    push_cast
    ring
  mul_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c - b * d, a * d + b * c - b * d, ?_⟩
    push_cast
    linear_combination (b : ℂ) * (d : ℂ) * omega3_sq

noncomputable def toCoordinateSubring : O →+* coordinateSubring :=
  eisEmbedding.codRestrict coordinateSubring (by
    intro x
    obtain ⟨a, b, hrepr⟩ := exists_ab x
    rw [hrepr]
    change embedding omega3 omega3_sq (a + b * pb.gen : O) ∈ coordinateSubring
    rw [embedding_apply_ab]
    exact ⟨a, b, rfl⟩)

theorem toCoordinateSubring_surjective : Function.Surjective toCoordinateSubring := by
  rintro ⟨z, a, b, hz⟩
  refine ⟨(a + b * pb.gen : O), ?_⟩
  apply Subtype.ext
  change eisEmbedding (a + b * pb.gen : O) = z
  change embedding omega3 omega3_sq (a + b * pb.gen : O) = z
  rw [embedding_apply_ab]
  exact hz.symm

noncomputable def eisTraceModChar
    (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = 1)
    (a : O) (ha : a ≠ 0) : AddChar (O ⧸ Ideal.span {a}) ℂ :=
  traceModChar eisEmbedding ψ eisLam a
    (eisEmbedding_ne_zero ha) eisLam_ne_zero (eisPeriod ψ hperiod)

noncomputable def eisTraceProdChar
    (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = 1)
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0) :
    AddChar (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) ℂ :=
  traceProdChar eisEmbedding ψ eisLam a b
    (eisEmbedding_ne_zero ha) (eisEmbedding_ne_zero hb)
    eisLam_ne_zero (eisPeriod ψ hperiod)

theorem finite_quotient_span {a : O} (ha : a ≠ 0) :
    Finite (O ⧸ Ideal.span {a}) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  intro h
  exact ha (Ideal.span_singleton_eq_bot.mp h)

theorem finite_quotient_product {a b : O} (ha : a ≠ 0) (hb : b ≠ 0) :
    Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  intro h
  have hab : a * b = 0 := Ideal.span_singleton_eq_bot.mp (by
    simpa only [Ideal.span_singleton_mul_span_singleton] using h)
  exact mul_ne_zero ha hb hab

end ConcreteTraceCRT

namespace ConcreteBreveE

open EisensteinEmbedding ConcreteTraceCRT

theorem breveE_period_coordinates :
    ∀ c d : ℤ,
      ShortDraftTrace.breveE
        (((c : ℂ) + (d : ℂ) * omega3) / eisLam) = 1 := by
  intro c d
  change ShortDraftTrace.breveE
    (((c : ℂ) + (d : ℂ) * ShortDraftTrace.ω₃) /
      (1 + 2 * ShortDraftTrace.ω₃)) = 1
  exact ShortDraftTrace.breveE_period_lam c d

end ConcreteBreveE

namespace ActualEisensteinCubic

open AddChar MulChar

open AddChar MulChar

noncomputable def canonicalSextic (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) ℂ :=
  (sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding

theorem canonicalSextic_pow_six (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : canonicalSextic P hgood ^ 6 = 1 := by
  change ((sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ^ 6 = 1
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).2.2,
    MulChar.ringHomComp_one]

theorem canonicalSextic_pow_ne_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {j : ℕ} (hj0 : j ≠ 0) (hj6 : j < 6) :
    canonicalSextic P hgood ^ j ≠ 1 := by
  change ((sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ^ j ≠ 1
  rw [MulChar.ringHomComp_pow]
  apply (MulChar.ringHomComp_ne_one_iff
    ConcreteTraceCRT.eisEmbedding_injective).2
  apply pow_ne_one_of_lt_orderOf hj0
  rwa [sexticChar_order P hgood hchar]

end ActualEisensteinCubic

end

end OAI
end

section

namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section

namespace ShortDraftCusp

variable {R : Type*} [CommRing R]

def U (t : R) : Matrix (Fin 2) (Fin 2) R := !![1,t;0,1]

end ShortDraftCusp

namespace ShortDraftGauss

open Complex
open scoped ComplexConjugate

variable {F : Type*} [Field F] [Fintype F]

theorem norm_gaussSum_eq_sqrt_card (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  let g := gaussSum χ ψ
  have hprod : g * conj g = (Fintype.card F : ℂ) := by
    have h := gaussSum_mul_gaussSum_eq_card hχ hψ
    rw [← star_gaussSum_eq] at h
    simpa only [g, Complex.star_def] using h
  have hnorm : ‖g‖ ^ 2 = (Fintype.card F : ℝ) := by
    apply Complex.ofReal_injective
    calc
      ((‖g‖ ^ 2 : ℝ) : ℂ) = (‖g‖ : ℂ) ^ 2 := by norm_cast
      _ = g * conj g := (Complex.mul_conj' g).symm
      _ = (Fintype.card F : ℂ) := hprod
      _ = ((Fintype.card F : ℝ) : ℂ) := by norm_cast
  have hcard : (0 : ℝ) ≤ Fintype.card F := by positivity
  have hsqrt := Real.sq_sqrt hcard
  nlinarith [norm_nonneg g, Real.sqrt_nonneg (Fintype.card F)]

end ShortDraftGauss

namespace ShortDraftSextic
open scoped Classical
variable {R : Type*} [CommRing R]

theorem sextic_power_is_unit_mask (χ : MulChar R ℂ)
    (hχ : χ ^ 6 = 1) (u : R) :
    χ (u ^ 6) = if IsUnit u then 1 else 0 := by
  classical
  rw [map_pow, ← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
  by_cases hu : IsUnit u
  · simp [hu, MulChar.one_apply]
  · simp [hu]

end ShortDraftSextic

namespace ShortDraftQuadraticGauss
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem quadratic_gauss_as_square_phase (ψ : AddChar F ℂ)
    (hchar : ringChar F ≠ 2) (hψ : ψ ≠ 1) :
    gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ =
      ∑ x : F, ψ (x ^ 2) := by
  have hfiber : (∑ x : F, ψ (x ^ 2)) =
      ∑ y : F, (#{x : F | x ^ 2 = y}.toFinset : ℂ) * ψ y := by
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun x : F => x ^ 2) (f := fun x : F => ψ (x ^ 2))]
    apply Finset.sum_congr rfl
    intro y _
    have hterm : (∑ x ∈ Finset.univ with x ^ 2 = y, ψ (x ^ 2)) =
        (#{x : F | x ^ 2 = y}.toFinset : ℂ) * ψ y := by
      rw [Finset.sum_congr rfl (fun x hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [hx])]
      simp
    exact hterm
  have hcount (y : F) :
      (#{x : F | x ^ 2 = y}.toFinset : ℂ) =
        (quadraticChar F y : ℂ) + 1 := by
    exact_mod_cast quadraticChar_card_sqrts hchar y
  rw [hfiber]
  simp_rw [hcount, add_mul]
  rw [Finset.sum_add_distrib]
  have hzero : (∑ y : F, ψ y) = 0 := AddChar.sum_eq_zero_of_ne_one hψ
  simp only [one_mul, hzero, add_zero]
  rfl

end ShortDraftQuadraticGauss

namespace EisensteinEPrimaryPhase

abbrev Coord := ZMod 4 × ZMod 4

def mul (x y : Coord) : Coord :=
  (x.1 * y.1 - x.2 * y.2,
   x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

def odd (x : Coord) : Prop := x.1.val % 2 = 1 ∨ x.2.val % 2 = 1

instance : DecidablePred odd := fun x =>
  inferInstanceAs (Decidable (x.1.val % 2 = 1 ∨ x.2.val % 2 = 1))

def norm (x : Coord) : ZMod 4 :=
  x.1 * x.1 - x.1 * x.2 + x.2 * x.2

theorem odd_mul (x y : Coord) (hx : odd x) (hy : odd y) : odd (mul x y) := by
  decide +revert

end EisensteinEPrimaryPhase

namespace ActualEisensteinCoordinates
abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K
instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
theorem hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K) 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ K
def omega : O := hζ.toInteger
def pb : PowerBasis ℤ O := hζ.integralPowerBasis

theorem pb_dim : pb.dim = 2 := by
  simp [pb, Nat.totient_prime Nat.prime_three]

theorem pb_gen : pb.gen = omega := by
  exact hζ.integralPowerBasis_gen

theorem exists_coordinates (x : O) :
    ∃ a b : ℤ, x = (a : O) + (b : O) * omega := by
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let a : ℤ := (pb.basis.repr x) i0
  let b : ℤ := (pb.basis.repr x) i1
  refine ⟨a, b, ?_⟩
  have hsum := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    ext i
    have hi : i.val < 2 := by simpa only [pb_dim] using i.isLt
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hv with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rw [huniv] at hsum
  have hne : i0 ≠ i1 := by decide
  have hnot : i0 ∉ ({i1} : Finset (Fin pb.dim)) := by
    simpa only [Finset.mem_singleton] using hne
  rw [Finset.sum_insert hnot, Finset.sum_singleton] at hsum
  simp only [pb.basis_eq_pow] at hsum
  have hi0 : (i0 : ℕ) = 0 := rfl
  have hi1 : (i1 : ℕ) = 1 := rfl
  simpa [a, b, hi0, hi1, pb_gen, smul_eq_mul, mul_comm] using hsum.symm

def i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
def i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩

def eval (a b : ℤ) : O := (a : O) + (b : O) * omega

theorem eval_basis (a b : ℤ) :
    eval a b = a • pb.basis i0 + b • pb.basis i1 := by
  simp [eval, PowerBasis.basis_eq_pow, i0, i1, pb_gen, mul_comm]

theorem unique_coordinates {a b c d : ℤ}
    (h : eval a b = eval c d) : a = c ∧ b = d := by
  have h0 := congrArg (fun x : O => (pb.basis.repr x) i0) h
  have h1 := congrArg (fun x : O => (pb.basis.repr x) i1) h
  have hne : i0 ≠ i1 := by decide
  rw [eval_basis, eval_basis] at h0 h1
  constructor
  · simpa only [map_add, map_smul, pb.basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, if_pos, if_neg hne.symm,
      smul_eq_mul, mul_one, mul_zero, add_zero] using h0
  · simpa only [map_add, map_smul, pb.basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, if_pos, if_neg hne,
      smul_eq_mul, mul_one, mul_zero, zero_add] using h1

theorem omega_sq : omega ^ 2 = -omega - 1 := by
  simpa [omega] using IsCyclotomicExtension.Rat.Three.eta_sq hζ

theorem eval_mul (a b c d : ℤ) :
    eval a b * eval c d = eval (a*c-b*d) (a*d+b*c-b*d) := by
  simp only [eval]
  calc
    ((a : O) + (b : O) * omega) * ((c : O) + (d : O) * omega)
      = (a : O) * c + ((a : O) * d + (b : O) * c) * omega +
          ((b : O) * d) * omega ^ 2 := by ring
    _ = ((a*c-b*d : ℤ) : O) + ((a*d+b*c-b*d : ℤ) : O) * omega := by
          rw [omega_sq]
          push_cast
          ring

theorem exists_pair (x : O) :
    ∃ p : ℤ × ℤ, eval p.1 p.2 = x := by
  obtain ⟨a, b, h⟩ := exists_coordinates x
  exact ⟨(a, b), h.symm⟩

def coords (x : O) : ℤ × ℤ := Classical.choose (exists_pair x)

theorem eval_coords (x : O) : eval (coords x).1 (coords x).2 = x :=
  Classical.choose_spec (exists_pair x)

def residue (x : O) : EisensteinEPrimaryPhase.Coord :=
  ((coords x).1, (coords x).2)

theorem residue_eval (a b : ℤ) :
    residue (eval a b) = ((a : ZMod 4), (b : ZMod 4)) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext (congrArg (fun n : ℤ => (n : ZMod 4)) h.1)
    (congrArg (fun n : ℤ => (n : ZMod 4)) h.2)

theorem residue_mul (x y : O) :
    residue (x*y) = EisensteinEPrimaryPhase.mul (residue x) (residue y) := by
  calc
    residue (x*y) = residue (eval (coords x).1 (coords x).2 *
        eval (coords y).1 (coords y).2) := by rw [eval_coords, eval_coords]
    _ = EisensteinEPrimaryPhase.mul (residue x) (residue y) := by
      rw [eval_mul, residue_eval]
      simp [residue, EisensteinEPrimaryPhase.mul]

def lift (v : EisensteinEPrimaryPhase.Coord) : O :=
  eval (v.1.val : ℤ) (v.2.val : ℤ)

theorem residue_two : residue (2 : O) = (2, 0) := by
  have h : eval 2 0 = (2 : O) := by simp [eval]
  rw [← h, residue_eval]
  norm_num

theorem not_odd_mul_two (v : EisensteinEPrimaryPhase.Coord) :
    ¬ EisensteinEPrimaryPhase.odd
      (EisensteinEPrimaryPhase.mul (2, 0) v) := by
  decide +revert

theorem not_odd_cast_zero (v : EisensteinEPrimaryPhase.Coord)
    (h : ¬ EisensteinEPrimaryPhase.odd v) :
    (ZMod.cast v.1 : ZMod 2) = 0 ∧
      (ZMod.cast v.2 : ZMod 2) = 0 := by
  decide +revert

theorem odd_residue_iff_not_two_dvd (x : O) :
    EisensteinEPrimaryPhase.odd (residue x) ↔ ¬ (2 : O) ∣ x := by
  constructor
  · intro hx hdiv
    obtain ⟨y, hy⟩ := hdiv
    rw [hy, residue_mul, residue_two] at hx
    exact not_odd_mul_two (residue y) hx
  · intro hdiv
    by_contra hodd
    obtain ⟨ha, hb⟩ := not_odd_cast_zero (residue x) hodd
    have ha' : ((coords x).1 : ZMod 2) = 0 := by
      simpa [residue, ZMod.cast_intCast (by decide : 2 ∣ 4)] using ha
    have hb' : ((coords x).2 : ZMod 2) = 0 := by
      simpa [residue, ZMod.cast_intCast (by decide : 2 ∣ 4)] using hb
    obtain ⟨a, ha2⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (coords x).1 2).mp ha'
    obtain ⟨b, hb2⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (coords x).2 2).mp hb'
    apply hdiv
    refine ⟨eval a b, ?_⟩
    rw [← eval_coords x]
    dsimp [eval]
    rw [ha2, hb2]
    push_cast
    ring
end ActualEisensteinCoordinates

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT

noncomputable def breveGamma2 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood ^ 2)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

theorem canonicalSextic_pow_two (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    canonicalSextic P hgood ^ 2 =
      (cubicChar P hgood).ringHomComp eisEmbedding := by
  change ((sexticChar P hgood).ringHomComp eisEmbedding) ^ 2 = _
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).1]

end ActualEisensteinCubic

namespace AnalyticBridge

theorem schwartz_fourier_one_plus_integrable
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ℝ =>
      (1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) volume := by
  let b := 𝓕 g
  have hI0 : Integrable (fun t : ℝ => ‖b t‖) volume := by
    simpa [b] using b.integrable_pow_mul volume 0
  have hIJ : Integrable
      (fun t : ℝ => ‖t‖ ^ J * ‖b t‖) volume :=
    b.integrable_pow_mul volume J
  have hR : Integrable
      (fun t : ℝ => (2 : ℝ) ^ J *
        (‖b t‖ + ‖t‖ ^ J * ‖b t‖)) volume :=
    (hI0.add hIJ).const_mul _
  have hpoint (t : ℝ) :
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
        (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
    have hp := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num)
      (norm_nonneg t) J
    have htwo : (2 : ℝ) ^ (J - 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)
    calc
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
          (2 : ℝ) ^ (J - 1) * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ J * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ := by
        gcongr
      _ = (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
        simp; ring
  have hcont : Continuous
      (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
    fun_prop
  exact hR.mono_nonneg hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (by intro t; positivity))
    (Filter.Eventually.of_forall hpoint)

end AnalyticBridge

namespace JacobiQuadratic

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def affineDouble (hchar : ringChar F ≠ 2) : F ≃ F where
  toFun x := 2 * x - 1
  invFun t := (t + 1) / 2
  left_inv := by
    intro x
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    field_simp
    ring
  right_inv := by
    intro t
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    field_simp
    ring

def oneSub : F ≃ F where
  toFun y := 1 - y
  invFun y := 1 - y
  left_inv := by intro y; ring
  right_inv := by intro y; ring

end JacobiQuadratic

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT

noncomputable def breveGamma1 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

noncomputable def breveGamma3 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood ^ 3)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

theorem canonicalSextic_pow_three_quadratic (P : Ideal O)
    [P.IsMaximal] (hgood : lambda ∉ P) :
    canonicalSextic P hgood ^ 3 =
      (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom ℂ) := by
  change ((sexticChar P hgood).ringHomComp eisEmbedding) ^ 3 = _
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).2.1]
  ext x
  change eisEmbedding ((quadraticChar (O ⧸ P) x : ℤ) : O) =
    ((quadraticChar (O ⧸ P) x : ℤ) : ℂ)
  simp

end

section

open EisensteinEmbedding ConcreteTraceCRT

noncomputable def breveLocalG (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  (canonicalSextic P hgood (Ideal.Quotient.mk P (4 : O)))⁻¹ *
    breveGamma3 P hgood p hP hp

end

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

end ActualEisensteinCubic

namespace ConcreteBreveE

open EisensteinEmbedding ConcreteTraceCRT

noncomputable def normalizedTraceGauss
    (a : O) (ha : a ≠ 0) (χ : MulChar (O ⧸ Ideal.span {a}) ℂ) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span ha
  letI : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  exact gaussSum χ (eisTraceModChar ShortDraftTrace.breveE
    breveE_period_coordinates a ha) / (‖eisEmbedding a‖ : ℂ)

end ConcreteBreveE

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT

noncomputable def breveGammaMinus1 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood)⁻¹
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

end ActualEisensteinCubic

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace FourierBridge
open scoped FourierTransform SchwartzMap

theorem logPhase_norm (t y : ℝ) : ‖logPhase t y‖ = 1 := by
  simpa [logPhase] using
    Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t * y)

theorem logPhase_continuous_left (y : ℝ) :
    Continuous (fun t : ℝ => logPhase t y) := by
  unfold logPhase
  fun_prop

end FourierBridge

namespace ActualEisensteinCubic

section

open AddChar MulChar

@[instance_reducible] noncomputable def crtIntersectionFintype
    {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hdistinct : Function.Injective (fun i => Ideal.span {p i})) :
    Fintype (O ⧸ ⨅ i, Ideal.span {p i}) := by
  classical
  letI (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  have hcop : Pairwise
      (fun i k => IsCoprime (Ideal.span {p i}) (Ideal.span {p k})) := by
    intro i k hik
    exact Ideal.isCoprime_of_isMaximal (hdistinct.ne hik)
  let e := Ideal.quotientInfRingEquivPiQuotient
    (fun i => Ideal.span {p i}) hcop
  exact Fintype.ofEquiv (∀ i, O ⧸ Ideal.span {p i}) e.symm.toEquiv

end

theorem canonicalSextic_sixth_power_mask (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (a : O) :
    canonicalSextic P hgood (Ideal.Quotient.mk P (a ^ 6)) =
      if a ∈ P then 0 else 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  rw [map_pow, ShortDraftSextic.sextic_power_is_unit_mask
    (canonicalSextic P hgood) (canonicalSextic_pow_six P hgood)]
  by_cases ha : a ∈ P
  · simp [ha, isUnit_iff_ne_zero, Ideal.Quotient.eq_zero_iff_mem]
  · simp [ha, isUnit_iff_ne_zero, Ideal.Quotient.eq_zero_iff_mem]

end ActualEisensteinCubic

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace TraceLambdaPhase

open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped ComplexConjugate

theorem eisLam_sq : eisLam ^ 2 = (-3 : ℂ) := by
  change (1 + 2 * omega3) ^ 2 = -3
  linear_combination 4 * omega3_sq

theorem exp_minus_four_pi_div_three :
    Complex.exp (-(4 : ℂ) * Real.pi * Complex.I / 3) = omega3 := by
  have hshift : Complex.exp (-(4 : ℂ) * Real.pi * Complex.I / 3) =
      Complex.exp ((2 : ℂ) * Real.pi * Complex.I / 3) := by
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨-1, ?_⟩
    push_cast
    ring
  rw [hshift]
  have harg : ((2 : ℂ) * Real.pi * Complex.I / 3) =
      (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I]
  have htwo : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [htwo, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  unfold omega3
  push_cast
  ring

end TraceLambdaPhase

namespace ActualEisensteinCubic

noncomputable def finiteSquarefreeRow
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (u : O) : ℂ :=
  ∏ i ∈ S, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) u)

end ActualEisensteinCubic

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem breveE_quarter_trace (a b : ℤ) :
    ShortDraftTrace.breveE
      ((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) =
      Complex.I ^ b := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj a b
  have hconj : ∀ z : ℂ, star (z / 4) = star z / 4 := by
    intro z
    simp
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) +
      star (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4)))) = _
  rw [hconj]
  have hL : ((a : ℂ) + (b : ℂ) * omega3) / eisLam +
      star (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = (b : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  have harg : 2 * Real.pi * Complex.I *
      (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) +
        (star (((a : ℂ) + (b : ℂ) * omega3) / eisLam)) / 4) =
      (b : ℂ) * (Real.pi / 2 * Complex.I) := by
    rw [← add_div, hL]
    ring
  rw [harg, Complex.exp_int_mul, Complex.exp_pi_div_two_mul_I]

noncomputable def breveGaussianFourTerms (a b : ℤ) : ℂ :=
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  (ShortDraftTrace.breveE (0 : ℂ) +
      ShortDraftTrace.breveE (((-c) / eisLam) / 4) +
      ShortDraftTrace.breveE (((-c * omega3 ^ 2) / eisLam) / 4) +
      ShortDraftTrace.breveE (((-c * (1 + omega3) ^ 2) / eisLam) / 4)) / 2

theorem breveGaussianFourTerms_formula (a b : ℤ) :
    breveGaussianFourTerms a b =
      (1 + Complex.I ^ (-b) + Complex.I ^ a + Complex.I ^ (b-a)) / 2 := by
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  have hfirst : ShortDraftTrace.breveE (((-c) / eisLam) / 4) =
      Complex.I ^ (-b) := by
    have hc : -c = ((-a : ℤ) : ℂ) + ((-b : ℤ) : ℂ) * omega3 := by
      dsimp [c]
      push_cast
      ring
    rw [hc]
    exact breveE_quarter_trace (-a) (-b)
  have hsecond : ShortDraftTrace.breveE
      (((-c * omega3 ^ 2) / eisLam) / 4) = Complex.I ^ a := by
    have hc : -c * omega3 ^ 2 = ((a-b : ℤ) : ℂ) + (a : ℂ) * omega3 := by
      dsimp [c]
      push_cast
      linear_combination -(a : ℂ) * omega3_sq -
        (b : ℂ) * (omega3 - 1) * omega3_sq
    rw [hc]
    exact breveE_quarter_trace (a-b) a
  have hthird : ShortDraftTrace.breveE
      (((-c * (1 + omega3) ^ 2) / eisLam) / 4) =
      Complex.I ^ (b-a) := by
    have hω : (1 + omega3) ^ 2 = omega3 := by
      linear_combination omega3_sq
    have hc : -c * (1 + omega3) ^ 2 =
        (b : ℂ) + ((b-a : ℤ) : ℂ) * omega3 := by
      rw [hω]
      dsimp [c]
      push_cast
      linear_combination -(b : ℂ) * omega3_sq
    rw [hc]
    exact breveE_quarter_trace b (b-a)
  dsimp [breveGaussianFourTerms]
  rw [hfirst, hsecond, hthird]
  simp only [map_zero_eq_one]

end ActualEisensteinCubic

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ShortDraftLatticeCount

def q (x : ℤ × ℤ) : ℤ := x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2

theorem coordinate_squares (a b D : ℤ) (hD : 0 ≤ D)
    (h : a ^ 2 - a * b + b ^ 2 ≤ D) :
    a ^ 2 ≤ 2 * D ∧ b ^ 2 ≤ 2 * D := by
  constructor <;> nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b)]

theorem finite_lattice_count (S : Finset (ℤ × ℤ)) (D R : ℕ)
    (hR : 2 * D < R ^ 2)
    (hS : ∀ x ∈ S, q x ≤ D) :
    S.card ≤ (2 * R + 1) ^ 2 := by
  let I : Finset ℤ := Finset.Icc (-(R : ℤ)) (R : ℤ)
  have hbox : S ⊆ I.product I := by
    intro x hx
    rcases x with ⟨a, b⟩
    have hD : (0 : ℤ) ≤ D := by positivity
    obtain ⟨ha, hb⟩ := coordinate_squares a b D hD (hS (a, b) hx)
    have hR' : 2 * (D : ℤ) < (R : ℤ) ^ 2 := by exact_mod_cast hR
    have hRnonneg : (0 : ℤ) ≤ R := by positivity
    apply Finset.mem_product.mpr
    constructor <;> simp only [I, Finset.mem_Icc] <;> constructor <;>
      nlinarith [sq_nonneg (a - R),
      sq_nonneg (a + R), sq_nonneg (b - R), sq_nonneg (b + R)]
  have hI : I.card = 2 * R + 1 := by
    dsimp [I]
    rw [Int.card_Icc]
    have hcast : (R : ℤ) + 1 + (R : ℤ) = ((R + 1 + R : ℕ) : ℤ) := by
      push_cast
      ring
    rw [sub_neg_eq_add, hcast, Int.toNat_natCast]
    ring
  calc
    S.card ≤ (I.product I).card := Finset.card_le_card hbox
    _ = I.card * I.card := Finset.card_product _ _
    _ = (2 * R + 1) ^ 2 := by rw [hI]; ring

theorem finite_lattice_count_linear (S : Finset (ℤ × ℤ)) (D : ℕ)
    (hS : ∀ x ∈ S, q x ≤ D) :
    S.card ≤ 64 * (D + 1) := by
  have hR : 2 * D < (Nat.sqrt (2 * D) + 1) ^ 2 := by
    exact Nat.lt_succ_sqrt' _
  have hcount := finite_lattice_count S D (Nat.sqrt (2 * D) + 1) hR hS
  have hsquare : (Nat.sqrt (2 * D)) ^ 2 ≤ 2 * D := Nat.sqrt_le' _
  have hroot : Nat.sqrt (2 * D) ≤ 2 * D := Nat.sqrt_le_self _
  nlinarith

theorem actual_eisenstein_count
    (S : Finset ActualEisensteinCoordinates.O) (D : ℕ)
    (hS : ∀ x ∈ S, q (ActualEisensteinCoordinates.coords x) ≤ D) :
    S.card ≤ 64 * (D + 1) := by
  have hinj : Function.Injective ActualEisensteinCoordinates.coords := by
    intro x y hxy
    calc
      x = ActualEisensteinCoordinates.eval
          (ActualEisensteinCoordinates.coords x).1
          (ActualEisensteinCoordinates.coords x).2 :=
        (ActualEisensteinCoordinates.eval_coords x).symm
      _ = ActualEisensteinCoordinates.eval
          (ActualEisensteinCoordinates.coords y).1
          (ActualEisensteinCoordinates.coords y).2 := by rw [hxy]
      _ = y := ActualEisensteinCoordinates.eval_coords y
  have himage : (S.image ActualEisensteinCoordinates.coords).card = S.card :=
    Finset.card_image_of_injective S hinj
  have hbound : ∀ v ∈ S.image ActualEisensteinCoordinates.coords,
      q v ≤ D := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact hS x hx
  calc
    S.card = (S.image ActualEisensteinCoordinates.coords).card := himage.symm
    _ ≤ 64 * (D + 1) := finite_lattice_count_linear _ D hbound

end ShortDraftLatticeCount

namespace ActualEisensteinCubic

open ShortDraftCusp

theorem A3_cubicChar_neg_one
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) :
    cubicChar P hgood (-1 : O ⧸ P) = 1 := by
  let χ := cubicChar P hgood
  have hcube : χ (-1 : O ⧸ P) ^ 3 = 1 := by
    rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
    exact MulChar.one_apply isUnit_neg_one
  have hminus : (-1 : O ⧸ P) ^ 3 = -1 := by ring
  calc
    χ (-1 : O ⧸ P) = χ ((-1 : O ⧸ P) ^ 3) := by rw [hminus]
    _ = χ (-1 : O ⧸ P) ^ 3 := by rw [map_pow]
    _ = 1 := hcube

end ActualEisensteinCubic

namespace ShortDraftLatticeCount

open ActualEisensteinCoordinates

theorem coords_eval (a b : ℤ) :
    coords (eval a b) = (a, b) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext h.1 h.2

theorem qO_mul (x y : O) :
    q (coords (x * y)) = q (coords x) * q (coords y) := by
  have hxy : x * y = eval
      ((coords x).1 * (coords y).1 - (coords x).2 * (coords y).2)
      ((coords x).1 * (coords y).2 + (coords x).2 * (coords y).1 -
        (coords x).2 * (coords y).2) := by
    calc
      x * y = eval (coords x).1 (coords x).2 *
          eval (coords y).1 (coords y).2 := by rw [eval_coords, eval_coords]
      _ = _ := eval_mul _ _ _ _
  rw [hxy, coords_eval]
  exact ShortDraft.eisenstein_norm_mul (coords x) (coords y)

theorem qO_nonneg (x : O) : 0 ≤ q (coords x) := by
  exact ShortDraft.eisenstein_norm_nonneg (coords x)

def qNat (x : O) : ℕ := (q (coords x)).toNat

theorem qNat_mul (x y : O) : qNat (x * y) = qNat x * qNat y := by
  unfold qNat
  rw [qO_mul]
  exact Int.toNat_mul (qO_nonneg x) (qO_nonneg y)

end ShortDraftLatticeCount

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ActualEisensteinCubic

section

open ActualEisensteinCoordinates ShortDraftLatticeCount

theorem omega_sq_for_norm : omega ^ 2 = -omega - 1 := by
  simpa [omega] using
    IsCyclotomicExtension.Rat.Three.eta_sq
      (IsCyclotomicExtension.zeta_spec 3 ℚ K)

theorem conjO_eval_coordinates (a b : ℤ) :
    conjO (eval a b) = eval (a - b) (-b) := by
  have hω : ActualEisensteinCoordinates.omega = omega := rfl
  simp only [eval, map_add, map_mul, map_intCast, hω, conjO_omega]
  rw [omega_sq_for_norm]
  push_cast
  ring

theorem coordinate_norm_eq_mul_conjO (p : O) :
    ((q (coords p) : ℤ) : O) = p * conjO p := by
  let a := (coords p).1
  let b := (coords p).2
  have hp : p = eval a b := (eval_coords p).symm
  symm
  calc
    p * conjO p = eval a b * eval (a - b) (-b) := by
      rw [hp, conjO_eval_coordinates]
    _ = ((q (coords p) : ℤ) : O) := by
      rw [eval_mul]
      simp only [eval, q]
      dsimp [a, b]
      push_cast
      ring

theorem algebraNorm_eq_coordinate_norm (p : O) :
    Algebra.norm ℤ p = q (coords p) := by
  have h := (norm_int_eq_mul_conjO p).trans
    (coordinate_norm_eq_mul_conjO p).symm
  exact_mod_cast h

theorem qNat_eq_absNorm_span (p : O) :
    qNat p = Ideal.absNorm (Ideal.span {p}) := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_eq_coordinate_norm]
  unfold qNat
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg (qO_nonneg p),
    Int.natAbs_of_nonneg (qO_nonneg p)]

end

section

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

theorem rational_modulus_card (m : ℕ) (_hm : m ≠ 0) :
    Nat.card (O ⧸ Ideal.span {(m : O)}) = m ^ 2 := by
  have hnorm : Algebra.norm ℤ (m : O) = (m : ℤ) ^ 2 := by
    have h := Algebra.norm_algebraMap_of_basis
      EisensteinEmbedding.pb.basis (m : ℤ)
    simpa [EisensteinEmbedding.pb_dim] using h
  calc
    Nat.card (O ⧸ Ideal.span {(m : O)}) =
        Ideal.absNorm (Ideal.span {(m : O)}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = (Algebra.norm ℤ (m : O)).natAbs :=
      Ideal.absNorm_span_singleton (m : O)
    _ = m ^ 2 := by rw [hnorm]; simp

theorem mk_eval_congr_mod (m : ℕ) (a b c d : ℤ)
    (ha : (a : ZMod m) = c) (hb : (b : ZMod m) = d) :
    Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval a b) =
      Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval c d) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  have hda : (m : ℤ) ∣ a - c :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub c a m).mp ha.symm
  have hdb : (m : ℤ) ∣ b - d :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub d b m).mp hb.symm
  obtain ⟨r, hr⟩ := hda
  obtain ⟨s, hs⟩ := hdb
  apply (Ideal.mem_span_singleton).mpr
  refine ⟨ActualEisensteinCoordinates.eval r s, ?_⟩
  dsimp [ActualEisensteinCoordinates.eval]
  rw [show a = c + m*r by omega, show b = d + m*s by omega]
  push_cast
  ring

noncomputable def rationalCoordMap (m : ℕ) :
    ZMod m × ZMod m → (O ⧸ Ideal.span {(m : O)}) :=
  fun ab => Ideal.Quotient.mk (Ideal.span {(m : O)})
    (ActualEisensteinCoordinates.eval (ZMod.cast ab.1) (ZMod.cast ab.2))

theorem rationalCoordMap_surjective (m : ℕ) :
    Function.Surjective (rationalCoordMap m) := by
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, b, hab⟩ := ActualEisensteinCoordinates.exists_coordinates z
  refine ⟨((a : ZMod m), (b : ZMod m)), ?_⟩
  change Ideal.Quotient.mk (Ideal.span {(m : O)})
      (ActualEisensteinCoordinates.eval (ZMod.cast (a : ZMod m))
        (ZMod.cast (b : ZMod m))) = _
  rw [hab]
  apply mk_eval_congr_mod
  · exact ZMod.intCast_zmod_cast _
  · exact ZMod.intCast_zmod_cast _

noncomputable def rationalCoordEquiv (m : ℕ) (hm : m ≠ 0) :
    ZMod m × ZMod m ≃ (O ⧸ Ideal.span {(m : O)}) := by
  letI : NeZero m := ⟨hm⟩
  letI : Finite (O ⧸ Ideal.span {(m : O)}) :=
    finite_quotient_span (by exact_mod_cast hm)
  letI : Fintype (O ⧸ Ideal.span {(m : O)}) := Fintype.ofFinite _
  refine Equiv.ofBijective (rationalCoordMap m) ?_
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · exact rationalCoordMap_surjective m
  · have hq : Fintype.card (O ⧸ Ideal.span {(m : O)}) = m ^ 2 := by
      simpa only [Nat.card_eq_fintype_card] using rational_modulus_card m hm
    simp [hq, Fintype.card_prod, sq]

theorem eisEmbedding_eval (a b : ℤ) :
    eisEmbedding (ActualEisensteinCoordinates.eval a b) =
      (a : ℂ) + (b : ℂ) * omega3 := by
  have hgen : ActualEisensteinCoordinates.omega =
      EisensteinEmbedding.pb.gen := by
    rw [← ActualEisensteinCoordinates.pb_gen]
    rfl
  rw [ActualEisensteinCoordinates.eval, hgen]
  change EisensteinEmbedding.embedding omega3 omega3_sq
    (a + b * EisensteinEmbedding.pb.gen : O) = _
  exact EisensteinEmbedding.embedding_apply_ab omega3 omega3_sq a b

theorem rationalCoordEquiv_apply (m : ℕ) (hm : m ≠ 0)
    (a b : ZMod m) :
    rationalCoordEquiv m hm (a,b) =
      Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval (ZMod.cast a) (ZMod.cast b)) := rfl

end

section

theorem cubic_roots_reduce_injective (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) {x y : O}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y) : x = y := by
  obtain ⟨i, hi, rfl⟩ := omega_primitive.eq_pow_of_pow_eq_one hx
  obtain ⟨j, hj, rfl⟩ := omega_primitive.eq_pow_of_pow_eq_one hy
  have hij : i = j := by
    apply (omega_reduced_primitive P hgood).pow_inj hi hj
    simpa only [map_pow] using hxy
  rw [hij]

theorem cubicChar_omega (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) =
      omega ^ ((Nat.card (O ⧸ P) - 1) / 3) := by
  let χ := cubicChar P hgood
  have hx : (χ (Ideal.Quotient.mk P omega)) ^ 3 = 1 := by
    rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
    exact MulChar.one_apply ((omega_reduced_primitive P hgood).isUnit (by decide))
  have hy : (omega ^ ((Nat.card (O ⧸ P) - 1) / 3)) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, omega_primitive.pow_eq_one, one_pow]
  apply cubic_roots_reduce_injective P hgood hx hy
  rw [map_pow]
  exact cubicChar_reduce P hgood (Ideal.Quotient.mk P omega)

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem breveE_int_trace_div (q u v : ℤ) (_hq : q ≠ 0) :
    ShortDraftTrace.breveE
      ((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q) =
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / q) := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj u v
  have hL : ((u : ℂ) + (v : ℂ) * omega3) / eisLam +
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) = (v : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q) +
      star (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q)))) = _
  rw [show star (((u : ℂ) + (v : ℂ) * omega3) / eisLam / q) =
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q by simp]
  rw [← add_div, hL]
  congr 1
  ring

theorem breveE_quadratic_coordinate (a b x y : ℤ)
    (hq : a*a - a*b + b*b ≠ 0) :
    let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
    let z : ℂ := (x : ℂ) + (y : ℂ) * omega3
    ShortDraftTrace.breveE (z ^ 2 / (c * eisLam)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((-b*x*x + 2*a*x*y + (b-a)*y*y : ℤ) : ℂ) /
        ((a*a-a*b+b*b : ℤ) : ℂ)) := by
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  let z : ℂ := (x : ℂ) + (y : ℂ) * omega3
  let cb : ℂ := ((a-b : ℤ) : ℂ) - (b : ℂ) * omega3
  let q : ℤ := a*a-a*b+b*b
  let U : ℤ := (x*x-y*y)*(a-b)+b*(2*x*y-y*y)
  let V : ℤ := -b*x*x+2*a*x*y+(b-a)*y*y
  have hnorm : c * cb = (q : ℂ) := by
    dsimp [c, cb, q]
    push_cast
    linear_combination -(b : ℂ)^2 * omega3_sq
  have hnum : z ^ 2 * cb = (U : ℂ) + (V : ℂ) * omega3 := by
    dsimp [z, cb, U, V]
    push_cast
    linear_combination
      ((y : ℂ)^2 * ((a : ℂ)-(b : ℂ)-(b : ℂ)*omega3) -
        (b : ℂ) * (2*(x : ℂ)*(y : ℂ)-(y : ℂ)^2)) * omega3_sq
  have hqC : (q : ℂ) ≠ 0 := by
    dsimp [q]
    exact_mod_cast hq
  have hc : c ≠ 0 := by
    intro hc
    apply hqC
    rw [← hnorm, hc, zero_mul]
  have hcb : cb ≠ 0 := by
    intro hcb
    apply hqC
    rw [← hnorm, hcb, mul_zero]
  have hdiv : z ^ 2 / (c * eisLam) =
      ((z ^ 2 * cb) / eisLam) / q := by
    rw [← hnorm]
    field_simp [hc, hcb, eisLam_ne_zero]
  change ShortDraftTrace.breveE (z ^ 2 / (c * eisLam)) = _
  rw [hdiv, hnum, breveE_int_trace_div q U V (by simpa [q] using hq)]

end

end ActualEisensteinCubic

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

noncomputable def quadraticGammaO (c : O) (hc : c ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  exact (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) /
    (‖eisEmbedding c‖ : ℂ)

end ActualEisensteinCubic

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex
theorem eisenstein_coord_norm_zero (a b : ℤ)
    (h : a*a-a*b+b*b = 0) : a = 0 ∧ b = 0 := by
  have hs : (a-b)^2 + a^2 + b^2 = 0 := by nlinarith [h]
  have ha : a^2 = 0 := by
    nlinarith [sq_nonneg (a-b), sq_nonneg b]
  have hb : b^2 = 0 := by
    nlinarith [sq_nonneg (a-b), sq_nonneg a]
  constructor <;> nlinarith

theorem quadraticTraceModChar_coordinate (a b x y : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval x y
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc)
      (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((-b*x*x + 2*a*x*y + (b-a)*y*y : ℤ) : ℂ) /
        ((a*a-a*b+b*b : ℤ) : ℂ)) := by
  have hq : a*a-a*b+b*b ≠ 0 := by
    intro h
    obtain ⟨ha,hb⟩ := eisenstein_coord_norm_zero a b h
    subst a
    subst b
    exact hc (by simp [ActualEisensteinCoordinates.eval])
  change ShortDraftTrace.breveE
    (eisEmbedding (ActualEisensteinCoordinates.eval x y ^ 2) /
      (eisEmbedding (ActualEisensteinCoordinates.eval a b) * eisLam)) = _
  rw [map_pow, eisEmbedding_eval, eisEmbedding_eval]
  exact breveE_quadratic_coordinate a b x y hq

end ActualEisensteinCubic

namespace GaussianAbelPartition

theorem tsum_by_finite_fibers {A B : Type*} [Fintype B]
    (q : A → B) (f : A → ℂ) (hf : Summable f) :
    (∑' a : A, f a) =
      ∑ b : B, ∑' a : (q ⁻¹' {b}), f a.1 := by
  have h := (hf.hasSum.tsum_fiberwise q).tsum_eq
  simpa only [tsum_fintype] using h.symm

theorem tsum_periodic_weighted_partition {A B : Type*} [Fintype B]
    (q : A → B) (P : B → ℂ) (W : A → ℂ)
    (hf : Summable (fun a => P (q a) * W a)) :
    (∑' a : A, P (q a) * W a) =
      ∑ b : B, P b * ∑' a : (q ⁻¹' {b}), W a.1 := by
  rw [tsum_by_finite_fibers q _ hf]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    (∑' a : (q ⁻¹' {b}), P (q a.1) * W a.1) =
        ∑' a : (q ⁻¹' {b}), P b * W a.1 := by
      apply tsum_congr
      intro a
      have ha : q a.1 = b := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using a.property
      rw [ha]
    _ = P b * ∑' a : (q ⁻¹' {b}), W a.1 := tsum_mul_left

open ConcreteTraceCRT ConcreteBreveE ActualEisensteinCubic

theorem actual_quadratic_gaussian_partition (c : O) (hc : c ≠ 0)
    (W : O → ℂ)
    (hsum : Summable (fun z : O =>
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z)) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z) =
      ∑ r : O ⧸ Ideal.span {c},
        (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
          (r ^ 2) *
          ∑' z : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}), W z.1 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c}))
    (fun r => (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
      (r ^ 2)) W hsum

end GaussianAbelPartition

namespace GaussianFiberEquiv

open ActualEisensteinCubic

def fiberMap (c : O) (r : O ⧸ Ideal.span {c})
    (r0 : O) (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r)
    (w : O) : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}) := by
  refine ⟨r0 + c*w, ?_⟩
  change Ideal.Quotient.mk (Ideal.span {c}) (r0 + c*w) = r
  rw [map_add, map_mul]
  have hc0 : Ideal.Quotient.mk (Ideal.span {c}) c = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton c))
  rw [hc0, zero_mul, add_zero, hr]

theorem fiberMap_injective (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    Function.Injective (fiberMap c r r0 hr) := by
  intro u v h
  have hval := congrArg Subtype.val h
  change r0 + c*u = r0 + c*v at hval
  exact mul_left_cancel₀ hc (add_left_cancel hval)

theorem fiberMap_surjective (c : O)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    Function.Surjective (fiberMap c r r0 hr) := by
  rintro ⟨z, hz⟩
  have hz' : Ideal.Quotient.mk (Ideal.span {c}) z = r := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
  have hdiff : z-r0 ∈ Ideal.span {c} :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem z r0).mp (hz'.trans hr.symm)
  obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton).mp hdiff
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change r0 + c*w = z
  rw [← hw]
  ring

noncomputable def fiberEquiv (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    O ≃ ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}) :=
  Equiv.ofBijective (fiberMap c r r0 hr)
    ⟨fiberMap_injective c hc r r0 hr, fiberMap_surjective c r r0 hr⟩

theorem fiber_tsum (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r)
    (W : O → ℂ) :
    (∑' z : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}), W z.1) =
      ∑' w : O, W (r0 + c*w) := by
  have h := (fiberEquiv c hc r r0 hr).tsum_eq (fun z => W z.1)
  have happ (w : O) : ((fiberEquiv c hc r r0 hr) w).1 = r0 + c*w := rfl
  simpa only [happ] using h.symm

end GaussianFiberEquiv

namespace RankTwoPoisson

open Real

theorem gauss_int_summable {a : ℂ} (ha : 0 < a.re) :
    Summable (fun n : ℤ => Complex.exp (-((Real.pi : ℂ) * a) * (n : ℂ) ^ 2)) := by
  have hpa : 0 < ((Real.pi : ℂ) * a).re := by
    simpa using mul_pos Real.pi_pos ha
  exact summable_of_isBigO (Real.summable_abs_int_rpow (show (1 : ℝ) < 2 by norm_num))
    ((isLittleO_exp_neg_mul_sq_cocompact hpa (-2)).isBigO.comp_tendsto
      Int.tendsto_coe_cofinite)

noncomputable def cg (a : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (-((Real.pi : ℂ) * a) * (n : ℂ) ^ 2)

theorem cg_summable {a : ℂ} (ha : 0 < a.re) : Summable (cg a) :=
  gauss_int_summable ha

theorem real_gauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * (n : ℝ) ^ 2)) := by
  have htc : 0 < (t : ℂ).re := by simpa using ht
  have h := (cg_summable htc).norm
  simpa [cg, Complex.norm_exp, ← Complex.ofReal_intCast, ← Complex.ofReal_pow, mul_assoc] using h

noncomputable def eisQ (z : ℤ × ℤ) : ℝ :=
  (z.1 : ℝ) ^ 2 - (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2

noncomputable def eisGauss (t : ℝ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp ((-Real.pi * t * eisQ z : ℝ) : ℂ)

theorem eisQ_lower (z : ℤ × ℤ) :
    ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / 2 ≤ eisQ z := by
  dsimp [eisQ]
  nlinarith [sq_nonneg ((z.1 : ℝ) - (z.2 : ℝ))]

theorem eis_gauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (eisGauss t) := by
  have ht2 : 0 < t / 2 := by positivity
  have h1 := real_gauss_summable ht2
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * (t / 2) * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (t / 2) * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine hmaj.of_norm_bounded ?_
  intro z
  have hq := eisQ_lower z
  have hpi : 0 ≤ Real.pi * t := (mul_pos Real.pi_pos ht).le
  have hmul := mul_le_mul_of_nonneg_left hq hpi
  have hexp : -Real.pi * t * eisQ z ≤
      -Real.pi * (t / 2) * (z.1 : ℝ) ^ 2 +
      -Real.pi * (t / 2) * (z.2 : ℝ) ^ 2 := by
    nlinarith [hmul]
  simpa [eisGauss, Complex.norm_exp, Real.exp_add] using
    (Real.exp_le_exp.mpr hexp)

end RankTwoPoisson

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar

open Filter Asymptotics

open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter

namespace ShortDraftHeckeBridge

abbrev O := ActualEisensteinSieve.O

noncomputable def normFiberCoeff (weight : Ideal O → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset, weight I

noncomputable def pairInverseCoeff
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ℕ → ℂ :=
  (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) ⍟
    (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ))

end ShortDraftHeckeBridge

open MulChar AddChar

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar

open MulChar AddChar

namespace ShortDraftHeckeBridge

noncomputable def chiMinusThree : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

noncomputable def baseChangeWeight {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ) * χ (Ideal.absNorm I)

noncomputable def invCharAF {q : ℕ} (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  (toArithmeticFunction (χ ·)).pmul (ArithmeticFunction.moebius : ArithmeticFunction ℂ)

noncomputable def pairAF {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  invCharAF χ * invCharAF ψ

end ShortDraftHeckeBridge
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic
open ActualEisensteinCubic
open Filter
open scoped Topology
open ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ActualEisensteinCubic

theorem A3_primary_unit_eq_one (x : O) (hx : IsUnit x)
    (hprimary : lambda ^ 2 ∣ x - 1) : x = 1 := by
  let v : Oˣ := hx.unit
  have hv : (v : O) = x := hx.unit_spec
  have hvprimary : lambda ^ 2 ∣ (v : O) - 1 := by
    simpa only [hv] using hprimary
  have hunit : v = 1 ∨ v = -1 := by
    apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) v
    refine ⟨(1 : ℤ), ?_⟩
    simpa only [lambda, omega, Int.cast_one] using hvprimary
  rcases hunit with h1 | hneg
  · calc
      x = (v : O) := hv.symm
      _ = 1 := by rw [h1]; rfl
  · have heq : (v : O) - 1 = -(2 : O) := by
      rw [hneg]
      norm_num
    rw [heq] at hvprimary
    have htwo : lambda ^ 2 ∣ (2 : O) := (dvd_neg).mp hvprimary
    exact False.elim (lambda_not_dvd_two
      ((dvd_pow_self lambda (by decide)).trans htwo))

end ActualEisensteinCubic

open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap

namespace LocalLogFourier

noncomputable def eulerDeriv (F : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  iteratedDeriv j (fun t : ℝ => F (x * Real.exp t)) 0

theorem iteratedDeriv_log_eq_euler (F : ℝ → ℂ) (R s : ℝ) (j : ℕ) :
    iteratedDeriv j (fun z : ℝ => F (R * Real.exp z)) s =
      eulerDeriv F j (R * Real.exp s) := by
  let G : ℝ → ℂ := fun z => F (R * Real.exp z)
  have hshift : (fun t : ℝ => F ((R * Real.exp s) * Real.exp t)) =
      (fun t : ℝ => G (s + t)) := by
    funext t
    simp only [G, Real.exp_add, mul_assoc]
  unfold eulerDeriv
  rw [hshift]
  simpa [G] using (congrArg (fun h : ℝ → ℂ => h 0)
    (iteratedDeriv_comp_const_add j G s)).symm

noncomputable def positiveLogProfile
    (V F : ℝ → ℂ) (R : ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) : 𝓢(ℝ, ℂ) := by
  let arg : ℝ → ℝ := fun s => R * Real.exp s
  have harg : ContDiff ℝ ∞ arg := by
    dsimp [arg]
    fun_prop
  have hargpos : ∀ s, arg s ∈ Set.Ioi (0 : ℝ) := by
    intro s
    exact mul_pos hR (Real.exp_pos _)
  have hG : ContDiff ℝ ∞ (fun s => F (arg s)) := by
    simpa only [Function.comp_def] using hFpos.comp_contDiff harg hargpos
  have hH : ContDiff ℝ ∞ (fun s => V s * F (arg s)) := hVs.mul hG
  have hc : HasCompactSupport (fun s => V s * F (arg s)) := hVc.mul_right
  exact hc.toSchwartzMap hH

@[simp] theorem positiveLogProfile_apply
    (V F : ℝ → ℂ) (R s : ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) :
    positiveLogProfile V F R hVc hVs hFpos hR s =
      V s * F (R * Real.exp s) := rfl

theorem positive_log_separation
    (V F : ℝ → ℂ) (R s : ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) :
    V s * F (R * Real.exp s) =
      ∫ t : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ t s) * Complex.I) *
        (𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t := by
  rw [← positiveLogProfile_apply V F R s hVc hVs hFpos hR]
  exact FourierBridge.schwartz_log_inversion _ _

theorem euler_derivative_scale
    (F : ℝ → ℂ) (R s m CF : ℝ) (A i : ℕ)
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hms : m ≤ Real.exp s)
    (hF : (1 + R * Real.exp s) ^ A *
      ‖eulerDeriv F i (R * Real.exp s)‖ ≤ CF) :
    m ^ A * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ i (fun z : ℝ => F (R * Real.exp z)) s‖ ≤ CF := by
  have hscale : m * (1 + R) ≤ 1 + R * Real.exp s := by
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hms)]
  have hpow : (m * (1 + R)) ^ A ≤
      (1 + R * Real.exp s) ^ A := by gcongr
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_log_eq_euler]
  calc
    m ^ A * (1 + R) ^ A * ‖eulerDeriv F i (R * Real.exp s)‖ =
      (m * (1 + R)) ^ A * ‖eulerDeriv F i (R * Real.exp s)‖ := by rw [mul_pow]
    _ ≤ (1 + R * Real.exp s) ^ A *
      ‖eulerDeriv F i (R * Real.exp s)‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ CF := hF

theorem positive_log_product_derivative_bound
    (V F : ℝ → ℂ) (R m CW CF : ℝ) (A n : ℕ)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ n, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s)
    (hEuler : ∀ i ≤ n, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF)
    (s : ℝ) :
    m ^ A * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ n
        (fun z : ℝ => V z * F (R * Real.exp z)) s‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF := by
  let G : ℝ → ℂ := fun z => F (R * Real.exp z)
  have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp z) := by fun_prop
  have hG : ContDiff ℝ ∞ G := by
    dsimp [G]
    simpa only [Function.comp_def] using
      hFpos.comp_contDiff harg (by intro z; exact mul_pos hR (Real.exp_pos _))
  have hprod := norm_iteratedFDeriv_mul_le hVs hG s (n := n) (by simp)
  have hS : 0 ≤ m ^ A * (1 + R) ^ A := by positivity
  calc
    m ^ A * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ n (fun z : ℝ => V z * F (R * Real.exp z)) s‖ ≤
      (m ^ A * (1 + R) ^ A) *
        (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i V s‖ *
            ‖iteratedFDeriv ℝ (n - i) G s‖) :=
      mul_le_mul_of_nonneg_left (by simpa [G] using hprod) hS
    _ = ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i V s‖ *
        ((m ^ A * (1 + R) ^ A) * ‖iteratedFDeriv ℝ (n - i) G s‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hVi : ‖iteratedFDeriv ℝ i V s‖ = 0
      · simp [hVi]
        positivity
      have hms := hwindow s ⟨i, hi', hVi⟩
      have hx : 0 < R * Real.exp s := mul_pos hR (Real.exp_pos _)
      have hGi := euler_derivative_scale F R s m CF A (n - i)
        hR hm hm1 hms (hEuler (n - i) (Nat.sub_le n i) _ hx)
      have hVi' := hVderiv i hi' s
      gcongr

theorem positive_log_uniform_seminorm
    (V F : ℝ → ℂ) (R m Lwin CW CF : ℝ) (A n k : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ n, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ n, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    m ^ A * (1 + R) ^ A *
      (SchwartzMap.seminorm ℝ k n)
        (positiveLogProfile V F R hVc hVs hFpos hR) ≤
      Lwin ^ k *
        (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF) := by
  let g := positiveLogProfile V F R hVc hVs hFpos hR
  let S := m ^ A * (1 + R) ^ A
  let C := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF
  have hS : 0 < S := by dsimp [S]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hLC : 0 ≤ Lwin ^ k * C := by positivity
  have hgeq : (g : ℝ → ℂ) =
      fun z => V z * F (R * Real.exp z) := by
    funext z
    exact positiveLogProfile_apply V F R z hVc hVs hFpos hR
  have hpoint (s : ℝ) :
      S * (|s| ^ k * ‖iteratedDeriv n g s‖) ≤ Lwin ^ k * C := by
    by_cases hactive : ∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0
    · obtain ⟨hms, habs⟩ := hwindow s hactive
      have hraw := positive_log_product_derivative_bound
        V F R m CW CF A n hVs hFpos hR hm hm1
        hCW hCF hVderiv
        (by intro z hz; exact (hwindow z hz).1)
        hEuler s
      have hnorm : S * ‖iteratedDeriv n g s‖ ≤ C := by
        rw [hgeq]
        simpa [S, C, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hraw
      calc
        S * (|s| ^ k * ‖iteratedDeriv n g s‖) =
          |s| ^ k * (S * ‖iteratedDeriv n g s‖) := by ring
        _ ≤ |s| ^ k * C :=
          mul_le_mul_of_nonneg_left hnorm (pow_nonneg (abs_nonneg _) _)
        _ ≤ Lwin ^ k * C :=
          mul_le_mul_of_nonneg_right (by gcongr) hC
    · have hzero (i : ℕ) (hi : i ≤ n) :
          ‖iteratedFDeriv ℝ i V s‖ = 0 := by
        by_contra hne
        exact hactive ⟨i, hi, hne⟩
      have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp z) := by fun_prop
      have hG : ContDiff ℝ ∞ (fun z : ℝ => F (R * Real.exp z)) := by
        simpa only [Function.comp_def] using
          hFpos.comp_contDiff harg (by intro z; exact mul_pos hR (Real.exp_pos _))
      have hprod := norm_iteratedFDeriv_mul_le hVs hG s (n := n) (by simp)
      have hsumzero :
          (∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i V s‖ *
              ‖iteratedFDeriv ℝ (n - i)
                (fun z : ℝ => F (R * Real.exp z)) s‖) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hzero i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
        ring
      have hnormzero : ‖iteratedDeriv n g s‖ = 0 := by
        have hzero' :
            ‖iteratedFDeriv ℝ n
              (fun z : ℝ => V z * F (R * Real.exp z)) s‖ = 0 :=
          le_antisymm (hprod.trans_eq hsumzero) (norm_nonneg _)
        rw [hgeq]
        simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hzero'
      simp [hnormzero, hLC]
  have hsemi : (SchwartzMap.seminorm ℝ k n) g ≤ Lwin ^ k * C / S := by
    apply SchwartzMap.seminorm_le_bound' ℝ k n g (div_nonneg hLC hS.le)
    intro s
    exact (le_div_iff₀ hS).mpr
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hpoint s)
  calc
    S * (SchwartzMap.seminorm ℝ k n) g ≤ S * (Lwin ^ k * C / S) :=
      mul_le_mul_of_nonneg_left hsemi hS.le
    _ = Lwin ^ k * C := by field_simp

noncomputable def derivativeConstant (n : ℕ) (CW CF : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF

noncomputable def momentConstant (K : ℕ) (Lwin CW CF : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1),
    (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
      derivativeConstant n CW CF

theorem derivativeConstant_nonneg (n : ℕ) (CW CF : ℝ)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) :
    0 ≤ derivativeConstant n CW CF := by
  unfold derivativeConstant
  positivity

theorem momentConstant_nonneg (K : ℕ) (Lwin CW CF : ℝ)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) :
    0 ≤ momentConstant K Lwin CW CF := by
  unfold momentConstant
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (by positivity)
    (derivativeConstant_nonneg n CW CF hCW hCF)

theorem momentConstant_dominates (K n : ℕ) (Lwin CW CF : ℝ)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hn : n ≤ K) :
    (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
      derivativeConstant n CW CF ≤ momentConstant K Lwin CW CF := by
  unfold momentConstant
  apply Finset.single_le_sum
    (f := fun i : ℕ =>
      (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
        derivativeConstant i CW CF)
    (a := n)
  · intro i hi
    exact mul_nonneg (by positivity)
      (derivativeConstant_nonneg i CW CF hCW hCF)
  · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn)

theorem positive_log_source_pair
    (V F : ℝ → ℂ) (R m Lwin CW CF C : ℝ) (A K n : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hn : n ≤ K)
    (hVderiv : ∀ i ≤ K, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ K, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF)
    (hCbound : ∀ j ≤ K,
      (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
        derivativeConstant j CW CF ≤ C) :
    (m ^ A * (1 + R) ^ A) *
      ((SchwartzMap.seminorm ℝ 0 n)
          (positiveLogProfile V F R hVc hVs hFpos hR) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n)
          (positiveLogProfile V F R hVc hVs hFpos hR)) ≤ C := by
  let p := (volume : Measure ℝ).integrablePower
  let D : ℝ := derivativeConstant n CW CF
  let g := positiveLogProfile V F R hVc hVs hFpos hR
  have hVderiv_n : ∀ i ≤ n, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW := by
    intro i hi s
    exact hVderiv i (hi.trans hn) s
  have hwindow_n : ∀ s,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin := by
    intro s hs
    obtain ⟨i, hi, hnonzero⟩ := hs
    exact hwindow s ⟨i, hi.trans hn, hnonzero⟩
  have hEuler_n : ∀ i ≤ n, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF := by
    intro i hi x hx
    exact hEuler i (hi.trans hn) x hx
  have hzero := positive_log_uniform_seminorm
    V F R m Lwin CW CF A n 0 hVc hVs hFpos hR hm hm1
    hL hCW hCF hVderiv_n hwindow_n hEuler_n
  have hp := positive_log_uniform_seminorm
    V F R m Lwin CW CF A n p hVc hVs hFpos hR hm hm1
    hL hCW hCF hVderiv_n hwindow_n hEuler_n
  calc
    (m ^ A * (1 + R) ^ A) *
        ((SchwartzMap.seminorm ℝ 0 n) g +
          (SchwartzMap.seminorm ℝ p n) g) =
        (m ^ A * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ 0 n) g +
        (m ^ A * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ p n) g := by ring
    _ ≤ D + Lwin ^ p * D := by
      apply add_le_add
      · simpa [D, derivativeConstant, g] using hzero
      · simpa [D, derivativeConstant, g, p] using hp
    _ = (1 + Lwin ^ p) * D := by ring
    _ ≤ C := by simpa [D, p] using hCbound n hn

theorem positive_log_fourier_moment
    (V F : ℝ → ℂ) (R m Lwin CW CF : ℝ) (A J : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    (m ^ A * (1 + R) ^ A) *
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t‖) ≤
      (2 : ℝ) ^ J *
        (FourierBridge.coefficientMomentBound 0
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF) +
         FourierBridge.coefficientMomentBound J
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF)) := by
  let K := J + (volume : Measure ℝ).integrablePower
  let C := momentConstant K Lwin CW CF
  have hC : 0 ≤ C := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  apply FourierBridge.uniform_fourier_one_plus_moment _ J _ C (by positivity) hC
  intro n hn
  exact positive_log_source_pair V F R m Lwin CW CF C A K n
    hVc hVs hFpos hR hm hm1 hL hCW hCF
    (by simpa [K] using hn)
    (by simpa [K] using hVderiv)
    (by simpa [K] using hwindow)
    (by simpa [K] using hEuler)
    (by
      intro j hj
      simpa [C] using momentConstant_dominates K j Lwin CW CF hL hCW hCF hj)

theorem positive_log_fourier_bound
    (V F : ℝ → ℂ) (R m Lwin CW CF : ℝ) (A J : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    (1 + R) ^ A *
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t‖) ≤
      ((2 : ℝ) ^ J *
        (FourierBridge.coefficientMomentBound 0
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF) +
         FourierBridge.coefficientMomentBound J
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF))) / m ^ A := by
  have hpow : 0 < m ^ A := pow_pos hm _
  apply (le_div_iff₀ hpow).mpr
  have hbase := positive_log_fourier_moment V F R m Lwin CW CF A J
    hVc hVs hFpos hR hm hm1 hL hCW hCF hVderiv hwindow hEuler
  simpa [mul_assoc, mul_left_comm, mul_comm] using hbase

theorem coupled_positive_log_separation
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F V : ℝ → ℂ) (R : ℝ)
    (a y : ι → ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R)
    (hactive : (∏ j : ι, W j (y j)) ≠ 0 →
      V (∑ j : ι, a j * y j) = 1) :
    (∏ j : ι, W j (y j)) *
      F (R * Real.exp (∑ j : ι, a j * y j)) =
      ∫ t : ℝ,
        (∏ j : ι, W j (y j) *
          FourierBridge.logPhase t (a j * y j)) *
          (𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t := by
  classical
  let s : ℝ := ∑ j : ι, a j * y j
  let P : ℂ := ∏ j : ι, W j (y j)
  let b := 𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)
  have hsep : V s * F (R * Real.exp s) =
      ∫ t : ℝ, FourierBridge.logPhase t s * b t := by
    calc
      V s * F (R * Real.exp s) =
          ∫ t : ℝ, Complex.exp
            (↑(2 * Real.pi * inner ℝ t s) * Complex.I) * b t := by
        simpa [b] using
          (positive_log_separation V F R s hVc hVs hFpos hR)
      _ = ∫ t : ℝ, FourierBridge.logPhase t s * b t := by
        apply integral_congr_ae
        filter_upwards [] with t
        congr 1
        simp only [FourierBridge.logPhase, Real.inner_apply]
        congr 1
        push_cast
        ring
  have hcut : P * F (R * Real.exp s) =
      P * (V s * F (R * Real.exp s)) := by
    by_cases hP : P = 0
    · simp [hP]
    · rw [hactive (by simpa [P, s] using hP)]
      ring
  calc
    P * F (R * Real.exp s) = P * (V s * F (R * Real.exp s)) := hcut
    _ = P * (∫ t : ℝ, FourierBridge.logPhase t s * b t) := by rw [hsep]
    _ = ∫ t : ℝ, P * (FourierBridge.logPhase t s * b t) := by
      rw [integral_const_mul]
    _ = ∫ t : ℝ,
          (∏ j : ι, W j (y j) * FourierBridge.logPhase t (a j * y j)) * b t := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [show FourierBridge.logPhase t s =
          ∏ j : ι, FourierBridge.logPhase t (a j * y j) by
        simpa [s] using FourierBridge.logPhase_sum
          (Finset.univ : Finset ι) t (fun j => a j * y j)]
      rw [Finset.prod_mul_distrib]
      simp only [P]
      ring

end LocalLogFourier

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ShortDraftHeckeBridge

instance : IsCyclotomicExtension {3} ℚ ActualEisensteinSieve.K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

end ShortDraftHeckeBridge

namespace NormFiberCRT

abbrev O := ActualEisensteinSieve.O
abbrev K := ActualEisensteinSieve.K

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

end NormFiberCRT

namespace NormFiberMult

abbrev O := ActualEisensteinSieve.O

end NormFiberMult

open Filter Asymptotics

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

namespace FiniteSFactor

abbrev O := NumberField.RingOfIntegers (CyclotomicField 3 ℚ)

noncomputable def outsideWeight (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (I : Ideal O) : ℂ := by
  classical
  exact if ∀ P ∈ S, ¬ P ∣ I then w I else 0

noncomputable def fiber (n : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset

open scoped Classical

open scoped Classical

noncomputable def outsideCoeff (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (n : ℕ) : ℂ :=
  ∑ I ∈ fiber n, outsideWeight S w I

end FiniteSFactor

namespace DyadicTransfer

noncomputable def annularCutoff (φ : ℝ → ℂ) (y : ℝ) : ℂ :=
  φ y - φ (2 * y)

theorem annularCutoff_eq_zero_of_two_le (φ : ℝ → ℂ)
    (hlarge : ∀ y : ℝ, 2 ≤ y → φ y = 0)
    {y : ℝ} (hy : 2 ≤ y) : annularCutoff φ y = 0 := by
  have h2y : 2 ≤ 2 * y := by linarith
  simp [annularCutoff, hlarge y hy, hlarge (2 * y) h2y]

end DyadicTransfer

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

def normLogBin (u : ℝ) : ℕ := ⌊Real.log u⌋₊
def normLogScale (j : ℕ) : ℝ := Real.exp (j : ℝ)

variable {ι : Type*}
  [DecidableEq ι]

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*}
  [DecidableEq ι]

end SecondPassArithmetic

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace InitialMeanSquare

section
open ActualEisensteinCubic
abbrev O := ActualEisensteinCubic.O

end

end InitialMeanSquare

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical

open scoped BigOperators
namespace CompletedDyadic

def ramifiedScale (ρ q : ℝ) (m : ℕ) : ℝ := ρ*q^m

end CompletedDyadic

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

namespace CanonicalCubeSeparation
open FourierBridge

def columnWindowRadius (a b : ℝ) : ℝ := |Real.log a| + |Real.log b| + 3

def sourceLogProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) := by
  have hc : HasCompactSupport (fun u : ℝ => W (Real.exp u)) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (Real.log a) (Real.log b)) isCompact_Icc
    intro u hu
    have hm := hs hu
    constructor
    · simpa only [Real.log_exp] using Real.log_le_log ha hm.1
    · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hm.2
  exact hc.toSchwartzMap (hW.comp Real.contDiff_exp)

@[simp] lemma sourceLogProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (u : ℝ) :
    sourceLogProfile W a b ha hs hW u = W (Real.exp u) := rfl

def reopeningCoefficient (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) :=
  𝓕 (sourceLogProfile W a b ha hs hW)

def cubeFrequencyFactor (t ξ : ℝ) : ℂ :=
  (Real.exp (t/2) : ℂ) * logPhase ξ (3*t)

@[simp] lemma cubeFrequencyFactor_norm (t ξ : ℝ) :
    ‖cubeFrequencyFactor t ξ‖ = Real.exp (t/2) := by
  simp only [cubeFrequencyFactor, norm_mul, logPhase_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

end CanonicalCubeSeparation

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

namespace CompletedHeight

open MeasureTheory Filter Set
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
open FourierBridge

def positiveCutoff (a b : ℝ) (ha : 0 < a) : ContDiffBump ((a+max a b)/2) where
  rIn := (max a b-a)/2+a/4
  rOut := (max a b-a)/2+a/2
  rIn_pos := by linarith [le_max_left a b]
  rIn_lt_rOut := by linarith

lemma positiveCutoff_one (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x∈Icc a b) :
    positiveCutoff a b ha x=1 := by
  apply (positiveCutoff a b ha).one_of_mem_closedBall
  change dist x ((a+max a b)/2) ≤ (max a b-a)/2+a/4
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith [hx.1,hx.2,le_max_right a b]

lemma positiveCutoff_zero (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < a/2) :
    positiveCutoff a b ha x=0 := by
  by_contra hn
  have hm : x∈Function.support (positiveCutoff a b ha) := hn
  rw [(positiveCutoff a b ha).support_eq] at hm
  change dist x ((a+max a b)/2) < (max a b-a)/2+a/2 at hm
  rw [Real.dist_eq,abs_lt] at hm
  linarith [hm.1]

def logCorrection (a b : ℝ) (ha : 0 < a) (x : ℝ) : ℝ :=
  positiveCutoff a b ha x*(Real.log x-x)

def patchedLog (a b : ℝ) (ha : 0 < a) (x : ℝ) : ℝ := x+logCorrection a b ha x

lemma logCorrection_compact (a b : ℝ) (ha : 0 < a) :
    HasCompactSupport (logCorrection a b ha) := (positiveCutoff a b ha).hasCompactSupport.mul_right

lemma logCorrection_smooth (a b : ℝ) (ha : 0 < a) :
    ContDiff ℝ ∞ (logCorrection a b ha) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x=0
  · subst x
    have he : logCorrection a b ha =ᶠ[𝓝 (0:ℝ)] (fun _=>0) := by
      filter_upwards [isOpen_Iio.mem_nhds (by linarith : (0:ℝ)<a/2)] with y hy
      simp only [logCorrection,positiveCutoff_zero a b ha y hy,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (positiveCutoff a b ha).contDiff.contDiffAt.mul
      ((Real.contDiffAt_log.mpr hx).sub contDiffAt_id)

lemma patchedLog_temperate (a b : ℝ) (ha : 0 < a) :
    Function.HasTemperateGrowth (patchedLog a b ha) :=
  Function.HasTemperateGrowth.id'.add
    ((logCorrection_compact a b ha).hasTemperateGrowth (logCorrection_smooth a b ha))

lemma patchedLog_proper (a b : ℝ) (ha : 0 < a) :
    ∃k : ℕ, ∃C : ℝ, ∀x : ℝ, ‖x‖ ≤ C*(1+‖patchedLog a b ha x‖)^k := by
  obtain ⟨x₀,hx₀⟩ := (logCorrection_smooth a b ha).continuous.norm.exists_forall_ge_of_hasCompactSupport
    (logCorrection_compact a b ha).norm
  refine ⟨1,‖logCorrection a b ha x₀‖+1,?_⟩
  intro x
  have ht : ‖x‖ ≤ ‖patchedLog a b ha x‖+‖logCorrection a b ha x‖ := by
    simpa only [patchedLog,add_sub_cancel_right] using
      norm_sub_le (patchedLog a b ha x) (logCorrection a b ha x)
  have hb := hx₀ x
  simp only [pow_one]
  nlinarith [norm_nonneg (patchedLog a b ha x),norm_nonneg (logCorrection a b ha x₀)]

lemma patchedLog_eq_log (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x∈Icc a b) :
    patchedLog a b ha x=Real.log x := by
  simp only [patchedLog,logCorrection,positiveCutoff_one a b ha x hx,one_mul]
  ring

def sourceTwistCLM (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a) :
    𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
  ((SchwartzMap.smulLeftCLM ℂ (W : ℝ→ℂ)).restrictScalars ℝ).comp
    (SchwartzMap.compCLM ℝ (patchedLog_temperate a b ha) (patchedLog_proper a b ha))

def normTwistedSource (W : ℝ→ℂ) (t x : ℝ) : ℂ := logPhase t (Real.log x)*W x

lemma normTwistedSource_support (W : ℝ→ℂ) (t : ℝ) :
    Function.support (normTwistedSource W t) ⊆ Function.support W := by
  intro x hx hz
  exact hx (by simp only [normTwistedSource,hz,mul_zero])

end CompletedHeight

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section

namespace OAI

noncomputable section

namespace SixthPowerAverage

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open scoped BigOperators Classical
open ActualEisensteinCubic
open ShortDraftHeckeBridge

lemma prime_coprime_span_iff (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (b : ActualEisensteinCubic.O) : IsCoprime P (Ideal.span {b}) ↔ b∉P := by
  rw [Ideal.isCoprime_iff_codisjoint,
    ←(Ideal.isMaximal_def.mp (inferInstance : P.IsMaximal)).not_le_iff_codisjoint,
    Ideal.span_singleton_le_iff_mem]

end

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter Asymptotics MeasureTheory
open ActualEisensteinCubic
open ShortDraftHeckeBridge
open SecondPassArithmetic
open InitialMeanSquare

end SixthPowerAverage

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical ContDiff

open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

noncomputable local instance inactiveField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P
noncomputable local instance inactiveFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

end CubicEisenstein

open scoped BigOperators Classical

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredExceptionalCount
open UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

def valuation (I P : Ideal O) : ℕ := (normalizedFactors I).count P

def factorMultiset (I : Ideal O) (e : ℕ → ℕ) : Multiset (Ideal O) :=
  ∑ P ∈ (normalizedFactors I).toFinset, Multiset.replicate (e (valuation I P)) P

theorem factorMultiset_subset (I : Ideal O) (e : ℕ → ℕ) :
    factorMultiset I e ⊆ normalizedFactors I := by
  intro P hP
  obtain ⟨Q, hQ, hPQ⟩ := Multiset.mem_sum.mp hP
  have he : P = Q := (Multiset.mem_replicate.mp hPQ).2
  exact he ▸ Multiset.mem_toFinset.mp hQ

theorem factorMultiset_count (I P : Ideal O) (e : ℕ → ℕ) (he : e 0 = 0) :
    (factorMultiset I e).count P = e (valuation I P) := by
  unfold factorMultiset
  simp only [Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq']
  split_ifs with hP
  · rfl
  · have hz : valuation I P = 0 := Multiset.count_eq_zero.mpr
      (fun h => hP (Multiset.mem_toFinset.mpr h))
    rw [hz, he]

def factorPart (I : Ideal O) (e : ℕ → ℕ) : Ideal O := (factorMultiset I e).prod

theorem factorPart_ne_zero (I : Ideal O) (e : ℕ → ℕ) : factorPart I e ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (factorMultiset_subset I e)

theorem factorPart_valuation (I P : Ideal O) (e : ℕ → ℕ) (he : e 0 = 0) :
    valuation (factorPart I e) P = e (valuation I P) := by
  unfold valuation factorPart
  rw [normalizedFactors_prod_eq_self_of_subset (factorMultiset_subset I e)]
  exact factorMultiset_count I P e he

def sixthRemainder (I : Ideal O) : Ideal O := factorPart I (fun n => n % 6)

def sixthQuotient (I : Ideal O) : Ideal O := factorPart I (fun n => n / 6)

theorem sixthRemainder_ne_zero (I : Ideal O) : sixthRemainder I ≠ 0 := factorPart_ne_zero I _
theorem sixthQuotient_ne_zero (I : Ideal O) : sixthQuotient I ≠ 0 := factorPart_ne_zero I _

@[simp] theorem sixthRemainder_valuation (I P : Ideal O) :
    valuation (sixthRemainder I) P = valuation I P % 6 :=
  factorPart_valuation I P _ (by norm_num)

@[simp] theorem sixthQuotient_valuation (I P : Ideal O) :
    valuation (sixthQuotient I) P = valuation I P / 6 :=
  factorPart_valuation I P _ (by norm_num)

theorem valuation_mul (I J P : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    valuation (I * J) P = valuation I P + valuation J P := by
  simp only [valuation, normalizedFactors_mul hI hJ, Multiset.count_add]

theorem valuation_pow (I P : Ideal O) (n : ℕ) :
    valuation (I ^ n) P = n * valuation I P := by
  simp only [valuation, normalizedFactors_pow, Multiset.count_nsmul]

theorem ideal_eq_of_valuation_eq {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ P, valuation I P = valuation J P) : I = J := by
  rw [← Ideal.prod_normalizedFactors_eq_self hI, ← Ideal.prod_normalizedFactors_eq_self hJ]
  exact congrArg Multiset.prod (Multiset.ext.mpr h)

theorem sixth_normal_form (I : Ideal O) (hI : I ≠ 0) :
    sixthRemainder I * sixthQuotient I ^ 6 = I := by
  apply ideal_eq_of_valuation_eq
    (mul_ne_zero (sixthRemainder_ne_zero I) (pow_ne_zero _ (sixthQuotient_ne_zero I))) hI
  intro P
  rw [valuation_mul _ _ _ (sixthRemainder_ne_zero I)
    (pow_ne_zero _ (sixthQuotient_ne_zero I)), valuation_pow,
    sixthRemainder_valuation, sixthQuotient_valuation]
  omega

theorem sixthRemainder_valuation_lt (I P : Ideal O) : valuation (sixthRemainder I) P < 6 := by
  rw [sixthRemainder_valuation]
  omega

end SevenEighths.CenteredExceptionalCount
end

end OAI
end

section

namespace OAI

open scoped BigOperators

namespace SevenEighths.FiniteFourier

noncomputable section

variable {R : Type*} [CommRing R] [Fintype R]

def IsPrimitiveOnIdeals (χ : MulChar R ℂ) : Prop :=
  ∀ I : Ideal R, I ≠ ⊥ → ∃ u : Rˣ, (u : R) - 1 ∈ I ∧ χ (u : R) ≠ 1

theorem IsPrimitiveOnIdeals.inv {χ : MulChar R ℂ} (hχ : IsPrimitiveOnIdeals χ) :
    IsPrimitiveOnIdeals χ⁻¹ := by
  intro I hI
  obtain ⟨u, hu, hχu⟩ := hχ I hI
  refine ⟨u, hu, ?_⟩
  intro hinv
  apply hχu
  simpa only [← MulChar.star_apply', star_star, star_one] using congrArg star hinv

def transform (ψ : AddChar R ℂ) (f : R → ℂ) (a : R) : ℂ :=
  ∑ x : R, f x * ψ (a * x)

theorem transform_inversion (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f : R → ℂ) (x : R) :
    (∑ a : R, transform ψ f a * ψ (-(a * x))) =
      (Fintype.card R : ℂ) * f x := by
  classical
  simp only [transform, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ y : R, ∑ a : R, f y * ψ (a * y) * ψ (-(a * x))) =
        ∑ y : R, f y * ∑ a : R, ψ (a * (y - x)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (Fintype.card R : ℂ) * f x := by
      simp only [AddChar.sum_mulShift _ hψ, sub_eq_zero]
      simp [mul_ite, mul_comm]

theorem exists_nonzero_annihilator {a : R} (ha : ¬ IsUnit a) :
    ∃ b : R, b ≠ 0 ∧ a * b = 0 := by
  by_contra! h
  apply ha
  apply IsLeftRegular.isUnit_of_finite
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro b hb
  by_contra hb0
  exact h b hb0 hb

theorem exists_unit_stabilizer (χ : MulChar R ℂ) (hχ : IsPrimitiveOnIdeals χ)
    {a : R} (ha : ¬ IsUnit a) :
    ∃ u : Rˣ, a * (u : R) = a ∧ χ (u : R) ≠ 1 := by
  obtain ⟨b, hb, hab⟩ := exists_nonzero_annihilator ha
  have hI : Ideal.span ({b} : Set R) ≠ ⊥ := by
    intro hI
    have hbI := Ideal.mem_span_singleton_self b
    rw [hI] at hbI
    exact hb hbI
  obtain ⟨u, hu, hχu⟩ := hχ _ hI
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hu
  refine ⟨u, ?_, hχu⟩
  have hzero : a * ((u : R) - 1) = 0 := by
    rw [hc, ← mul_assoc, hab, zero_mul]
  linear_combination hzero

theorem gaussSum_mulShift_nonunit_eq_zero (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ)
    {a : R} (ha : ¬ IsUnit a) :
    gaussSum χ (ψ.mulShift a) = 0 := by
  obtain ⟨u, hu, hχu⟩ := exists_unit_stabilizer χ hχ ha
  have hshift : (ψ.mulShift a).mulShift (u : R) = ψ.mulShift a := by
    ext x
    simp only [AddChar.mulShift_apply, ← mul_assoc, hu]
  have heq := gaussSum_mulShift χ (ψ.mulShift a) u
  rw [hshift] at heq
  exact eq_zero_of_mul_eq_self_left hχu heq

theorem primitive_gaussSum_mulShift (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (a : R) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : IsUnit a
  · simpa only [ha.unit_spec] using gaussSum_mulShift_eq χ ψ ha.unit
  · rw [gaussSum_mulShift_nonunit_eq_zero χ hχ ψ ha,
      MulChar.map_nonunit _ ha, zero_mul]

theorem transform_primitive_character (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (a : R) :
    transform ψ χ a = χ⁻¹ a * gaussSum χ ψ := by
  exact primitive_gaussSum_mulShift χ hχ ψ a

theorem primitive_gaussSum_mul_conjugate (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * star (gaussSum χ ψ) = (Fintype.card R : ℂ) := by
  have hinv := transform_inversion ψ hψ (fun x => χ x) 1
  simp only [transform_primitive_character χ hχ, mul_one, map_one, mul_one] at hinv
  rw [star_gaussSum_eq]
  calc
    gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ =
        ∑ a : R, (χ⁻¹ a * gaussSum χ ψ) * ψ (-a) := by
      change gaussSum χ ψ * (∑ a : R, χ⁻¹ a * ψ⁻¹ a) = _
      rw [Finset.mul_sum]
      simp only [AddChar.inv_apply]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (Fintype.card R : ℂ) := hinv

theorem primitive_gaussSum_norm_sq (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card R : ℝ) := by
  apply Complex.ofReal_inj.mp
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simpa only [starRingEnd_apply, mul_comm, Complex.ofReal_natCast] using
    primitive_gaussSum_mul_conjugate χ hχ ψ hψ

end

end SevenEighths.FiniteFourier

end OAI
end

section

namespace OAI

namespace SevenEighths.FiniteConductor

open SevenEighths.FiniteFourier
open scoped Classical

noncomputable section

theorem exists_character_factor_iff {G H : Type*} [Group G] [CommGroup H]
    [Finite H] (q : G →* H) (χ : G →* ℂˣ) :
    (∃ φ : H →* ℂˣ, φ.comp q = χ) ↔ q.ker ≤ χ.ker := by
  constructor
  · rintro ⟨φ, rfl⟩ g hg
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply,
      MonoidHom.mem_ker.mp hg, map_one]
  · intro hker
    have hker' : q.rangeRestrict.ker ≤ χ.ker := by
      simpa only [MonoidHom.ker_rangeRestrict] using hker
    let θ : q.range →* ℂˣ :=
      MonoidHom.liftOfSurjective q.rangeRestrict q.rangeRestrict_surjective ⟨χ, hker'⟩
    have hθ : θ.comp q.rangeRestrict = χ := MonoidHom.liftOfRightInverse_comp ..
    obtain ⟨φ, hφ⟩ := MonoidHom.domRestrict_surjective ℂ q.range θ
    refine ⟨φ, ?_⟩
    calc
      φ.comp q = (φ.domRestrict q.range).comp q.rangeRestrict := rfl
      _ = θ.comp q.rangeRestrict := by rw [← hφ]; rfl
      _ = χ := hθ

variable {R : Type*} [CommRing R] [Finite R]

def quotientUnits (I : Ideal R) : Rˣ →* (R ⧸ I)ˣ :=
  Units.map (Ideal.Quotient.mk I).toMonoidHom

def FactorsThroughIdeal (χ : MulChar R ℂ) (I : Ideal R) : Prop :=
  ∃ φ : MulChar (R ⧸ I) ℂ,
    φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom

omit [Finite R] in
theorem quotientUnits_eq_one_iff (I : Ideal R) (u : Rˣ) :
    quotientUnits I u = 1 ↔ (u : R) - 1 ∈ I := by
  rw [← Units.val_inj]
  exact Ideal.Quotient.mk_eq_one_iff_sub_mem _

theorem factorsThroughIdeal_iff (χ : MulChar R ℂ) (I : Ideal R) :
    FactorsThroughIdeal χ I ↔
      ∀ u : Rˣ, (u : R) - 1 ∈ I → χ (u : R) = 1 := by
  let : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  have hfactor : FactorsThroughIdeal χ I ↔
      ∃ φ : (R ⧸ I)ˣ →* ℂˣ, φ.comp (quotientUnits I) = χ.toUnitHom := by
    constructor
    · rintro ⟨φ, hφ⟩
      exact ⟨φ.toUnitHom, hφ⟩
    · rintro ⟨φ, hφ⟩
      refine ⟨MulChar.ofUnitHom φ, ?_⟩
      simpa only [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq,
        Equiv.apply_symm_apply] using hφ
  rw [hfactor, exists_character_factor_iff]
  constructor
  · intro h u hu
    have hunit := h ((quotientUnits_eq_one_iff I u).mpr hu)
    exact congrArg Units.val hunit
  · intro h u hu
    apply Units.ext
    exact h u ((quotientUnits_eq_one_iff I u).mp hu)

theorem primitiveOnIdeals_iff_no_descent (χ : MulChar R ℂ) :
    IsPrimitiveOnIdeals χ ↔ ∀ I : Ideal R, I ≠ ⊥ → ¬ FactorsThroughIdeal χ I := by
  simp only [IsPrimitiveOnIdeals, factorsThroughIdeal_iff]
  push Not
  rfl

theorem FactorsThroughIdeal.inv {χ : MulChar R ℂ} {I : Ideal R}
    (h : FactorsThroughIdeal χ I) : FactorsThroughIdeal χ⁻¹ I := by
  rw [factorsThroughIdeal_iff] at h ⊢
  intro u hu
  rw [← MulChar.star_apply', h u hu, star_one]

omit [Finite R] in

theorem factorization_with_source_mask (χ : MulChar R ℂ) (I : Ideal R)
    (φ : MulChar (R ⧸ I) ℂ)
    (hφ : φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom) (a : R) :
    χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  classical
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    simp only [u.isUnit, ite_true]
    exact (congrArg (fun f : Rˣ →* ℂˣ => ((f u : ℂˣ) : ℂ)) hφ).symm
  · simp only [ha, ite_false, MulChar.map_nonunit _ ha]

end

end SevenEighths.FiniteConductor

end OAI
end

section

namespace OAI

namespace SevenEighths.CharacterTransport

open SevenEighths.FiniteFourier

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

def pullback (e : R ≃+* S) (χ : MulChar S ℂ) : MulChar R ℂ where
  toFun := fun x => χ (e x)
  map_one' := by simp
  map_mul' := by intro x y; simp
  map_nonunit' := by
    intro x hx
    apply χ.map_nonunit
    intro h
    apply hx
    simpa using h.map e.symm.toMonoidHom

@[simp] theorem pullback_apply (e : R ≃+* S) (χ : MulChar S ℂ) (x : R) :
    pullback e χ x = χ (e x) := rfl

@[simp] theorem pullback_symm (e : R ≃+* S) (χ : MulChar S ℂ) :
    pullback e.symm (pullback e χ) = χ := by
  apply MulChar.ext'
  intro x
  simp

@[simp] theorem pullback_mul (e : R ≃+* S) (χ ψ : MulChar S ℂ) :
    pullback e (χ * ψ) = pullback e χ * pullback e ψ := by
  apply MulChar.ext'
  intro x
  rfl

theorem primitive_pullback (e : R ≃+* S) (χ : MulChar S ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : IsPrimitiveOnIdeals (pullback e χ) := by
  intro I hI
  let J : Ideal S := I.comap e.symm.toRingHom
  have hJ : J ≠ ⊥ := by
    intro hJ
    apply hI
    apply le_antisymm _ bot_le
    intro x hx
    have he : e x ∈ J := by
      change e.symm (e x) ∈ I
      simpa using hx
    rw [hJ] at he
    have hx0 : x = 0 := e.injective (by simpa using he)
    exact hx0
  obtain ⟨u, hu, hχu⟩ := hχ J hJ
  let v : Rˣ := Units.map e.symm.toMonoidHom u
  refine ⟨v, ?_, ?_⟩
  · change e.symm (u : S) - 1 ∈ I
    change e.symm ((u : S) - 1) ∈ I at hu
    simpa only [map_sub, map_one] using hu
  · simpa [v, pullback] using hχu

end

end SevenEighths.CharacterTransport

end OAI
end

section

namespace OAI

namespace SevenEighths.FiniteConductor

open SevenEighths.FiniteFourier
open scoped Classical

noncomputable section

section QuotientBounds

variable {R : Type*} [CommRing R]

theorem quotient_card_le_of_le {I J : Ideal R} [Finite (R ⧸ J)] (hJI : J ≤ I) :
    Nat.card (R ⧸ I) ≤ Nat.card (R ⧸ J) :=
  Nat.card_le_card_of_surjective _ (Ideal.Quotient.factor_surjective hJI)

noncomputable def quotientComapEquiv (M : Ideal R) (I : Ideal (R ⧸ M)) :
    R ⧸ I.comap (Ideal.Quotient.mk M) ≃+* (R ⧸ M) ⧸ I :=
  RingEquiv.ofBijective (Ideal.quotientMap I (Ideal.Quotient.mk M) le_rfl)
    ⟨Ideal.quotientMap_injective,
      Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective⟩

theorem quotient_comap_card (M : Ideal R) (I : Ideal (R ⧸ M)) :
    Nat.card (R ⧸ I.comap (Ideal.Quotient.mk M)) = Nat.card ((R ⧸ M) ⧸ I) :=
  Nat.card_congr (quotientComapEquiv M I).toEquiv

end QuotientBounds

section FiniteRing

variable {R : Type*} [CommRing R] [Finite R]

theorem primitive_of_maximal_descent (χ : MulChar R ℂ) (I : Ideal R)
    (φ : MulChar (R ⧸ I) ℂ)
    (hφ : φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom)
    (hI : Maximal (FactorsThroughIdeal χ) I) : IsPrimitiveOnIdeals φ := by
  let : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  apply (primitiveOnIdeals_iff_no_descent φ).mpr
  intro J hJ hdesc
  let K : Ideal R := J.comap (Ideal.Quotient.mk I)
  have hK : FactorsThroughIdeal χ K := by
    apply (factorsThroughIdeal_iff χ K).mpr
    intro u hu
    have huJ : ((quotientUnits I u : (R ⧸ I)ˣ) : R ⧸ I) - 1 ∈ J := by
      change Ideal.Quotient.mk I ((u : R) - 1) ∈ J at hu
      change Ideal.Quotient.mk I (u : R) - 1 ∈ J
      simpa only [map_sub, map_one] using hu
    have heq := congrArg (fun f : Rˣ →* ℂˣ => ((f u : ℂˣ) : ℂ)) hφ
    exact heq.symm.trans ((factorsThroughIdeal_iff φ J).mp hdesc _ huJ)
  have hIK : I ≤ K := by
    intro x hx
    change Ideal.Quotient.mk I x ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact J.zero_mem
  have hKI : K ≤ I := hI.2 hK hIK
  apply hJ
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hKI hx)

theorem exists_primitive_quotient_above (χ : MulChar R ℂ) (J : Ideal R)
    (hJ : FactorsThroughIdeal χ J) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      J ≤ I ∧ φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I := by
  let : Finite (Ideal R) := Finite.of_injective
    (fun I : Ideal R => (I : Set R)) SetLike.coe_injective
  obtain ⟨I, hJI, hI⟩ := Finite.exists_le_maximal hJ
  obtain ⟨φ, hφ⟩ := hI.1
  exact ⟨I, φ, hJI, hφ, primitive_of_maximal_descent χ I φ hφ hI, hI⟩

theorem exists_primitive_quotient_above_with_bound_and_mask
    (χ : MulChar R ℂ) (J : Ideal R) (hJ : FactorsThroughIdeal χ J) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      J ≤ I ∧ φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I ∧
      Nat.card (R ⧸ I) ≤ Nat.card (R ⧸ J) ∧
      ∀ a : R, χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  let : Finite (R ⧸ J) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := J))
  obtain ⟨I, φ, hJI, hφ, hprimitive, hmaximal⟩ := exists_primitive_quotient_above χ J hJ
  exact ⟨I, φ, hJI, hφ, hprimitive, hmaximal, quotient_card_le_of_le hJI,
    factorization_with_source_mask χ I φ hφ⟩

end FiniteRing

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]
  [Module.Free ℤ A] [Module.Finite ℤ A]

theorem absNorm_le_of_le {I J : Ideal A} [Finite (A ⧸ J)] (hJI : J ≤ I) :
    I.absNorm ≤ J.absNorm := by
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using
    quotient_card_le_of_le hJI

theorem absNorm_comap_eq_quotient_card (M : Ideal A) (I : Ideal (A ⧸ M)) :
    (I.comap (Ideal.Quotient.mk M)).absNorm = Nat.card ((A ⧸ M) ⧸ I) := by
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using quotient_comap_card M I

theorem exists_primitive_residue_quotient_above_with_norm_and_mask
    (M : Ideal A) [Finite (A ⧸ M)] (χ : MulChar (A ⧸ M) ℂ)
    (J : Ideal (A ⧸ M)) (hJ : FactorsThroughIdeal χ J) :
    ∃ (I : Ideal (A ⧸ M)) (φ : MulChar ((A ⧸ M) ⧸ I) ℂ),
      J ≤ I ∧ φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I ∧
      (I.comap (Ideal.Quotient.mk M)).absNorm ≤
        (J.comap (Ideal.Quotient.mk M)).absNorm ∧
      ∀ a : A ⧸ M, χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  obtain ⟨I, φ, hJI, hφ, hprimitive, hmaximal, hcard, hmask⟩ :=
    exists_primitive_quotient_above_with_bound_and_mask χ J hJ
  refine ⟨I, φ, hJI, hφ, hprimitive, hmaximal, ?_, hmask⟩
  simpa only [absNorm_comap_eq_quotient_card] using hcard

end

end SevenEighths.FiniteConductor

end OAI
end

section

namespace OAI

namespace SevenEighths

namespace ConductorPresentation

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open scoped Classical

noncomputable section

section Transport

variable {A : Type*} [CommRing A]

def quotientCharacter (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) : MulChar (A ⧸ I.comap (Ideal.Quotient.mk M)) ℂ :=
  CharacterTransport.pullback (quotientComapEquiv M I) φ

@[simp] theorem quotientCharacter_mk (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) (a : A) :
    quotientCharacter M I φ (Ideal.Quotient.mk _ a) =
      φ (Ideal.Quotient.mk I (Ideal.Quotient.mk M a)) := rfl

theorem primitive_quotientCharacter (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) (hφ : IsPrimitiveOnIdeals φ) :
    IsPrimitiveOnIdeals (quotientCharacter M I φ) :=
  CharacterTransport.primitive_pullback _ _ hφ

theorem source_le_comap (M : Ideal A) (I : Ideal (A ⧸ M)) :
    M ≤ I.comap (Ideal.Quotient.mk M) := by
  intro a ha
  change Ideal.Quotient.mk M a ∈ I
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact I.zero_mem

end Transport

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]
  [Module.Free ℤ A] [Module.Finite ℤ A]

theorem comap_ne_bot (M : Ideal A) [Finite (A ⧸ M)] (I : Ideal (A ⧸ M)) :
    I.comap (Ideal.Quotient.mk M) ≠ ⊥ := by
  let : Finite ((A ⧸ M) ⧸ I) :=
    Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  have hpos : 0 < (I.comap (Ideal.Quotient.mk M)).absNorm := by
    rw [absNorm_comap_eq_quotient_card]
    exact Nat.card_pos
  intro hzero
  rw [hzero, Ideal.absNorm_bot] at hpos
  exact (lt_irrefl 0) hpos

theorem exists_primitive_presentation_above_quotient
    (M : Ideal A) [Finite (A ⧸ M)] (χ : MulChar (A ⧸ M) ℂ)
    (J : Ideal (A ⧸ M)) (hJ : FactorsThroughIdeal χ J) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ J.comap (Ideal.Quotient.mk M) ≤ K ∧ K ≠ ⊥ ∧
      IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ (J.comap (Ideal.Quotient.mk M)).absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨I, ψ, hJI, hψ, hprimitive, hmaximal, hnorm, hmask⟩ :=
    exists_primitive_residue_quotient_above_with_norm_and_mask M χ J hJ
  refine ⟨I.comap (Ideal.Quotient.mk M), quotientCharacter M I ψ,
    source_le_comap M I, Ideal.comap_mono hJI, comap_ne_bot M I,
    primitive_quotientCharacter M I ψ hprimitive, hnorm, ?_⟩
  intro a
  simpa only [quotientCharacter_mk] using hmask (Ideal.Quotient.mk M a)

end

end ConductorPresentation

end SevenEighths

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicExponent (negative : Bool) : ℕ := if negative then 4 else 2

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section

def firstKappa (M r ell V δ A B R : ℝ) : ℝ := M-2*r-2*ell-V-δ+A+B-R/2
def firstPhysicalHeight (M r ell V δ B j : ℝ) : ℝ := 2*r-2*B-M+4*ell+2*V+δ-j
def secondLambda (M r ell V δ A B j t g θ : ℝ) : ℝ :=
  firstPhysicalHeight M r ell V δ B j - θ - (r-A-B-t-g)
def secondCount (ell R j t g θ : ℝ) : ℝ := ell+R/2-j+t+g-θ
def secondFormalColumn (r A B t g v : ℝ) : ℝ := r-A-B-t-g-v
def secondFormalLabel (B θ v j : ℝ) : ℝ := B+θ+v+j

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators

noncomputable section

variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def primeSlot (L : Finset ι) (a : ι → ℂ) (A : Finset ι) : ℂ :=
  ∑ p ∈ L, if p ∈ A then a p else 0

def primeMark (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) : ℂ := ∏ i ∈ I, primeSlot (L i) (a i) A

omit [DecidableEq σ] in
@[simp] theorem primeMark_empty (L : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) : primeMark ∅ L a A = 1 := by
  simp [primeMark]

end

end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open SecondPassArithmetic

noncomputable local instance markedQuotientField (P : Ideal ActualEisensteinCubic.O)
    [P.IsMaximal] : Field (ActualEisensteinCubic.O ⧸ P) := Ideal.Quotient.field P

noncomputable local instance markedQuotientFintype (P : Ideal ActualEisensteinCubic.O)
    [P.IsMaximal] : Fintype (ActualEisensteinCubic.O ⧸ P) := Fintype.ofFinite _

variable {ι σ : Type*}
  [DecidableEq ι]
  [DecidableEq σ]
  (p : ι → ActualEisensteinCubic.O)
  (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))

include hcop

end

end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def sourceGridCoefficient (beta : Ideal Eis → Ideal Eis → ℂ)
    (t c m h : Ideal Eis) : ℂ := beta (c * m) ((c * h) * t ^ 2)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open FourierBridge ActualEisensteinCubic SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondOuterPhase (h y : Fin 6 → ℝ) : ℂ :=
  logPhase (h 0) (y 0) * logPhase (h 1) (y 1) *
    logPhase (h 2) (y 2) * logPhase (h 3) (y 3)

def childLogTest (ω : ℝ → ℂ) (h : ℝ) (y : ℝ) : ℂ :=
  ω y * logPhase h (Real.log y)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondUnitFrequency (u v : Eisˣ) (k : Eis) : Eis := ((u^4*v:Eisˣ):Eis)*k

variable {ι σ : Type*}
  [DecidableEq ι]
  (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FourierBridge
open MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def firstCoordinates (a : Fin 7 → ℝ) (x y : ℝ) : Fin 9 → ℝ :=
  ![a 0,a 1,a 2,a 3,a 4,a 5,a 6,x,y]

def firstOuterPhase (h : Fin 9 → ℝ) (a : Fin 7 → ℝ) : ℂ :=
  ∏ i : Fin 7, logPhase (h ⟨i.val, by omega⟩) (a i)

variable {ι : Type*}
  [DecidableEq ι]
  (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseMomentFirstChildWindows
open InverseMoment

def outerIndex (i : Fin 7) : Fin 9 := i.castLE (by decide)

end SevenEighths.InverseMomentFirstChildWindows
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment
open ActualEisensteinCubic SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def physicalPrincipalFactor (Z M r ell V delta A B R j t eta tau eps window : ℝ) : ℝ :=
  (Z^(firstKappa M r ell V delta A B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
    Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)*
    (Z^(r-A-B-t)*Real.exp window)^(1+eps)

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic SecondPassArithmetic
open InverseMomentFirstChildWindows
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))

def liveNormCap (L B Y : ℝ) : ℝ := max Y (max L (max (L*B^2) (B^2)))

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic
open SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

def indexedIdealMark {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (primes : ι→Ideal O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (I : Ideal O) : ℂ :=
  ∏j∈slots,∑i∈lists j,if primes i∣I then a j i else 0

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic
open CanonicalCubeSeparation SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O

def actualCubeLength (Z:ℝ)(j:ℕ):ℝ:=Real.logb Z (normLogScale j)

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def slotTupleProduct (p : ι → Ideal Eis) : Ideal Eis := ∏ i, p i

def slotProductCoefficient (tuples : Finset (ι → Ideal Eis))
    (a : (ι → Ideal Eis) → ℂ) (P : Ideal Eis) : ℂ :=
  ∑ p ∈ tuples, if slotTupleProduct p = P then a p else 0

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def separateSector (M r P : Eis) :
    (Eis ⧸ Ideal.span {M^2}) × (Eis ⧸ Ideal.span {M^2}) :=
  (Ideal.Quotient.mk _ r, Ideal.Quotient.mk _ P)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def reflectedExponent {φ ρ σ : Type*} (jF : φ → ℕ) : φ ⊕ (ρ ⊕ σ) → ℕ :=
  Sum.elim jF (Sum.elim (fun _ => 1) (fun _ => 0))

def frozenIndices (φ ρ σ : Type*) [Fintype φ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image φ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) Sum.inl Finset.univ

def residualIndices (φ ρ σ : Type*) [Fintype ρ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image ρ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) (Sum.inr ∘ Sum.inl) Finset.univ

def slotIndices (φ ρ σ : Type*) [Fintype σ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image σ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) (Sum.inr ∘ Sum.inr) Finset.univ

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ ι : Type*} [Fintype φ] [Fintype ι] {N a c : Eis} {mode : Bool}

def extractedDualScale (D : Ideal Eis) (Y : ℝ) : ℝ := max 1 (Y/(Ideal.absNorm D:ℝ))

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def shapeArgument (z : Eis) : ℂ := ((Ideal.absNorm (Ideal.span {z}):ℝ):ℂ)/(eisEmbedding z)^2

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def kernelSlope : Fin 4 → ℝ := ![-2,-2,1,3]
def kernelLogCoordinates (QK QP Qn Qb k p n b : ℝ) : Fin 4 → ℝ :=
  ![Real.log (k/QK),Real.log (p/QP),Real.log (n/Qn),Real.log (b/Qb)]
def kernelCenter (C QK QP Qn Qb : ℝ) : ℝ := C*Qn*Qb^3/(QK^2*QP^2)

def fixedKernelCoefficient (X tau r : ℝ) (C D1 D2 : Ideal Eis) : ℝ :=
  X/(27*tau^2*(Ideal.absNorm C:ℝ)^2)*r^3*
    (Ideal.absNorm D1:ℝ)*(Ideal.absNorm D2:ℝ)^3

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open MeasureTheory FourierBridge
noncomputable section

def kernelCoordinateWeight (w : ℝ→ℂ) (slope Q t q : ℝ) : ℂ :=
  w (Real.log (q/Q))*logPhase t (slope*Real.log (q/Q))

def kernelDualWeight (windows : Fin 4→ℝ→ℂ) (Qn Qb t n b : ℝ) : ℂ :=
  kernelCoordinateWeight (windows 2) 1 Qn t n * kernelCoordinateWeight (windows 3) 3 Qb t b

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι]
def activeMarks (A S : Finset ι) : Finset A := Finset.univ.filter (fun i => i.val∈S)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def slotChoiceSplit (L : σ→Finset (Ideal Eis)) (T : Finset σ) :
    (∀ i, L i)≃(∀ i : T, L i.val)×(∀ i : {i // i∉T}, L i.val) :=
  Equiv.piEquivPiSubtypeProd (fun i => i∈T) (fun i => L i)

omit [Fintype σ] in
lemma slotChoiceSplit_active (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T, L i.val) (b : ∀ i : {i // i∉T}, L i.val) (i : T) :
    (slotChoiceSplit L T).symm (a,b) i.val=a i := by
  simp only [slotChoiceSplit,Equiv.piEquivPiSubtypeProd,Equiv.coe_fn_symm_mk,dif_pos i.property]

omit [Fintype σ] in
lemma slotChoiceSplit_inactive (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T, L i.val) (b : ∀ i : {i // i∉T}, L i.val) (i : {i // i∉T}) :
    (slotChoiceSplit L T).symm (a,b) i.val=b i := by
  simp only [slotChoiceSplit,Equiv.piEquivPiSubtypeProd,Equiv.coe_fn_symm_mk,dif_neg i.property]

lemma slot_choice_coprime_split (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T, L i.val) (b : ∀ i : {i // i∉T}, L i.val) (K : Ideal Eis) :
    IsCoprime K (∏ i, ((slotChoiceSplit L T).symm (a,b) i).val) ↔
      IsCoprime K (∏ i : T, (a i).val) ∧ IsCoprime K (∏ i : {i // i∉T}, (b i).val) := by
  simp only [IsCoprime.prod_right_iff,Finset.mem_univ,forall_const]
  constructor
  · intro h
    constructor
    · intro i
      simpa only [slotChoiceSplit_active] using h i.val
    · intro i
      simpa only [slotChoiceSplit_inactive] using h i.val
  · rintro ⟨ha,hb⟩ i
    by_cases hi : i∈T
    · rw [slotChoiceSplit_active L T a b ⟨i,hi⟩]
      exact ha ⟨i,hi⟩
    · rw [slotChoiceSplit_inactive L T a b ⟨i,hi⟩]
      exact hb ⟨i,hi⟩
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] in
lemma slot_choice_fixed_split (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val) (F : φ→Ideal Eis) :
    (∀ j i,((slotChoiceSplit L T).symm (a,b) i).val≠F j) ↔
      (∀ j,∀ i : T,(a i).val≠F j) ∧ (∀ j,∀ i : {i // i∉T},(b i).val≠F j) := by
  constructor
  · intro h
    constructor
    · intro j i
      simpa only [slotChoiceSplit_active] using h j i.val
    · intro j i
      simpa only [slotChoiceSplit_inactive] using h j i.val
  · rintro ⟨ha,hb⟩ j i
    by_cases hi : i∈T
    · rw [slotChoiceSplit_active L T a b ⟨i,hi⟩]
      exact ha j ⟨i,hi⟩
    · rw [slotChoiceSplit_inactive L T a b ⟨i,hi⟩]
      exact hb j ⟨i,hi⟩

lemma slot_choice_mask_split (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val)
    (F : φ→Ideal Eis) (K : Ideal Eis) :
    (IsCoprime K (∏ i,((slotChoiceSplit L T).symm (a,b) i).val) ∧
      ∀ j i,((slotChoiceSplit L T).symm (a,b) i).val≠F j) ↔
    (IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j,∀ i : {i // i∉T},(b i).val≠F j) ∧
      (IsCoprime K (∏ i : T,(a i).val) ∧ ∀ j,∀ i : T,(a i).val≠F j) := by
  rw [slot_choice_coprime_split,slot_choice_fixed_split]
  tauto

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

def supportedSlotChoices (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (K : Ideal Eis) :=
  {p : ∀ i,L i // IsCoprime K (∏ i,(p i).val) ∧ ∀ j i,(p i).val≠F j}

instance supportedSlotChoices_fintype (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (K : Ideal Eis) :
    Fintype (supportedSlotChoices L F K) := inferInstanceAs (Fintype {_p : ∀ i,L i // _})

def supportedSlotSplit (L : σ→Finset (Ideal Eis)) (T : Finset σ) (F : φ→Ideal Eis) (K : Ideal Eis) :
    supportedSlotChoices L F K ≃
      supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K ×
        supportedSlotChoices (fun i : T => L i.val) F K where
  toFun p :=
    let q := slotChoiceSplit L T p.val
    have h := (slot_choice_mask_split L T q.1 q.2 F K).mp (by simpa only [q,Prod.mk.eta,Equiv.symm_apply_apply] using p.property)
    (⟨q.2,h.1⟩,⟨q.1,h.2⟩)
  invFun q := ⟨(slotChoiceSplit L T).symm (q.2.val,q.1.val),
    (slot_choice_mask_split L T q.2.val q.1.val F K).mpr ⟨q.1.property,q.2.property⟩⟩
  left_inv p := by
    apply Subtype.ext
    exact (slotChoiceSplit L T).symm_apply_apply p.val
  right_inv q := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.snd ((slotChoiceSplit L T).apply_symm_apply (q.2.val,q.1.val))
    · exact congrArg Prod.fst ((slotChoiceSplit L T).apply_symm_apply (q.2.val,q.1.val))

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

 def cubeDivList (H : Ideal Eis) (L : Finset (Ideal Eis)) : Finset (Ideal Eis) := L.filter (fun P => P∣H)
 def cubeAwayList (H : Ideal Eis) (L : Finset (Ideal Eis)) : Finset (Ideal Eis) := L.filter (fun P => ¬P∣H)
 def cubeChoiceActive (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) (p : ∀ i,L i) : Finset σ :=
  Finset.univ.filter (fun i => ¬(p i).val∣H)

abbrev CubeSlotChoices (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :=
  Σ T : Finset σ,(∀ i : {i // i∉T},cubeDivList H (L i.val))×(∀ i : T,cubeAwayList H (L i.val))

def cubeChoicesJoin (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) (x : CubeSlotChoices H L) : ∀ i,L i :=
  (slotChoiceSplit L x.1).symm
    (fun i => ⟨(x.2.2 i).val,(Finset.mem_filter.mp (x.2.2 i).property).1⟩,
     fun i => ⟨(x.2.1 i).val,(Finset.mem_filter.mp (x.2.1 i).property).1⟩)

lemma cubeChoicesJoin_label (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) (x : CubeSlotChoices H L) :
    cubeChoiceActive H L (cubeChoicesJoin H L x)=x.1 := by
  rcases x with ⟨T,b,a⟩
  ext i
  simp only [cubeChoiceActive,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hi : i∈T
  · have ha := (Finset.mem_filter.mp (a ⟨i,hi⟩).property).2
    have he := slotChoiceSplit_active L T
      (fun j => ⟨(a j).val,(Finset.mem_filter.mp (a j).property).1⟩)
      (fun j => ⟨(b j).val,(Finset.mem_filter.mp (b j).property).1⟩) ⟨i,hi⟩
    dsimp only [cubeChoicesJoin]
    rw [he]
    exact iff_of_true ha hi
  · have hb := (Finset.mem_filter.mp (b ⟨i,hi⟩).property).2
    have he := slotChoiceSplit_inactive L T
      (fun j => ⟨(a j).val,(Finset.mem_filter.mp (a j).property).1⟩)
      (fun j => ⟨(b j).val,(Finset.mem_filter.mp (b j).property).1⟩) ⟨i,hi⟩
    dsimp only [cubeChoicesJoin]
    rw [he]
    exact iff_of_false (not_not_intro hb) hi

lemma cubeChoicesJoin_injective (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :
    Function.Injective (cubeChoicesJoin H L) := by
  rintro ⟨T,b,a⟩ ⟨U,d,c⟩ he
  have ht := congrArg (cubeChoiceActive H L) he
  rw [cubeChoicesJoin_label,cubeChoicesJoin_label] at ht
  dsimp only at ht
  subst U
  apply congrArg (fun q => (⟨T,q⟩ : CubeSlotChoices H L))
  have hx := congrArg (slotChoiceSplit L T) he
  simp only [cubeChoicesJoin,Equiv.apply_symm_apply] at hx
  apply Prod.ext
  · funext i
    apply Subtype.ext
    exact congrArg (fun q => (q.2 i).val) hx
  · funext i
    apply Subtype.ext
    exact congrArg (fun q => (q.1 i).val) hx

lemma cubeChoicesJoin_surjective (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :
    Function.Surjective (cubeChoicesJoin H L) := by
  intro p
  let T := cubeChoiceActive H L p
  let a : ∀ i : T,cubeAwayList H (L i.val) := fun i =>
    ⟨(p i.val).val,Finset.mem_filter.mpr ⟨(p i.val).property,(Finset.mem_filter.mp i.property).2⟩⟩
  have hd (i : {i // i∉T}) : (p i.val).val∣H := by
    by_contra hi
    exact i.property (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  let b : ∀ i : {i // i∉T},cubeDivList H (L i.val) := fun i =>
    ⟨(p i.val).val,Finset.mem_filter.mpr ⟨(p i.val).property,hd i⟩⟩
  refine ⟨⟨T,b,a⟩,?_⟩
  apply (slotChoiceSplit L T).injective
  simp only [cubeChoicesJoin,Equiv.apply_symm_apply]
  apply Prod.ext <;> funext i <;> apply Subtype.ext <;> rfl

def cubeSlotChoiceEquiv (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :
    CubeSlotChoices H L ≃ (∀ i,L i) :=
  Equiv.ofBijective (cubeChoicesJoin H L) ⟨cubeChoicesJoin_injective H L,cubeChoicesJoin_surjective H L⟩

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (H : Ideal Eis)
  (L : σ→Finset (Ideal Eis))
  (hmax : ∀ i,∀ P∈L i,P.IsMaximal)

def cubeAbsorbedCoefficient (w : ∀ i,L i→ℂ) (T : Finset σ) : ℂ :=
  ∑ b : ∀ i : {i // i∉T},cubeDivList H (L i.val),
    ∏ i : {i // i∉T},w i.val ⟨(b i).val,(Finset.mem_filter.mp (b i).property).1⟩

include hmax

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

def fixedTupleCoefficient (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ) (p : σ→Ideal Eis) : ℂ :=
  if hp:∀ i,p i∈L i then ∏ i,w i ⟨p i,hp i⟩ else 0

variable {N a c : Eis} {mode : Bool}
variable (K : Ideal Eis)
  (L : σ→Finset (Ideal Eis))
  (F : φ→Ideal Eis)
  (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
  (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
  (hprime : ∀ i,∀ P∈L i,Prime P)
  (p : supportedSlotChoices L F K)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

@[simp] lemma shapeArgument_one : shapeArgument (1:Eis)=1 := by
  simp [shapeArgument,Ideal.span_singleton_one]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

def inactiveRowSet (rows : Finset (Ideal Eis)) (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (F : φ→Ideal Eis) (b : ∀ i : {i // i∉T},L i.val) : Finset (Ideal Eis) :=
  rows.filter fun K => IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j i,(b i).val≠F j

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def punctureLists (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis)) : σ→Finset (Ideal Eis) :=
  fun i => (lists i).filter (fun P => P∉S)

def punctureListLift (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis))
    (p : ∀ i,punctureLists lists S i) : ∀ i,lists i :=
  fun i => ⟨(p i).val,(Finset.mem_filter.mp (p i).property).1⟩

def punctureListEquiv (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis)) :
    (∀ i,punctureLists lists S i) ≃ {p : ∀ i,lists i // ∀ i,(p i).val∉S} where
  toFun p := ⟨punctureListLift lists S p,fun i => (Finset.mem_filter.mp (p i).property).2⟩
  invFun p i := ⟨(p.val i).val,Finset.mem_filter.mpr ⟨(p.val i).property,p.property i⟩⟩
  left_inv _p := rfl
  right_inv _p := rfl

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic
open InverseReflectedPhase CompletedHeight
local notation "Eis"=>ActualEisensteinCubic.O
universe v

def tupleDivisibilityMark {σ:Type v} [Fintype σ] [DecidableEq σ]
    (lists:σ→Finset (Ideal Eis)) (w:∀i,lists i→ℂ) (A:Ideal Eis):ℂ :=
  ∑p:∀i,lists i,(∏i,w i (p i))*∏i,if (p i).val∣A then (1:ℂ) else 0

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

def phasePolynomial {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, a i*FourierBridge.logPhase t (x i)

end
end SevenEighths.HeckeDetectorFourier

end OAI
end

section

namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology

namespace SevenEighths.ThetaProduct

theorem rectangularPair_hasSum (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ =>
      (Real.exp (-Real.pi * (u * (n.1 + a) ^ 2 + v * (n.2 + b) ^ 2) * t) : ℂ))
      ((rectangularPair a b u v hu hv).f t) := by
  have h₁ := HurwitzZeta.hasSum_int_evenKernel a (mul_pos hu ht)
  have h₂ := HurwitzZeta.hasSum_int_evenKernel b (mul_pos hv ht)
  have hprod := h₁.mul h₂ (h₁.summable.mul_of_nonneg h₂.summable
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le))
  have hid (n : ℤ × ℤ) :
      Real.exp (-Real.pi * (u * (n.1 + a) ^ 2 + v * (n.2 + b) ^ 2) * t) =
      Real.exp (-Real.pi * (n.1 + a) ^ 2 * (u * t)) *
        Real.exp (-Real.pi * (n.2 + b) ^ 2 * (v * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hid]
  simpa only [rectangularPair, product, scaledEvenPair, rescale,
    HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply, Complex.ofReal_mul] using
    (Complex.hasSum_ofReal.mpr hprod)

end SevenEighths.ThetaProduct

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace SevenEighths.EisensteinTheta
open ThetaProduct

def normForm (x y : ℝ) : ℝ := x ^ 2 - x * y + y ^ 2

def shearEquiv : (ℤ × (ℤ × Fin 2)) ≃ (Fin 2 × (ℤ × ℤ)) where
  toFun n := (n.2.2, (n.1 - n.2.1, n.2.1))
  invFun p := (p.2.1 + p.2.2, (p.2.2, p.1))
  left_inv n := by simp
  right_inv p := by simp

def parityEquiv : (ℤ × ℤ) ≃ (Fin 2 × (ℤ × ℤ)) :=
  (Equiv.prodCongr (Equiv.refl ℤ) (Int.divModEquiv 2)).trans shearEquiv

theorem normForm_parity (a b L : ℝ) (hL : L ≠ 0) (e : Fin 2) (i j : ℤ) :
    normForm (a + L * (i + j)) (b + L * (2 * j + e)) =
      L ^ 2 * (i + xShift a b L e) ^ 2 +
        (3 * L ^ 2) * (j + yShift b L e) ^ 2 := by
  unfold normForm xShift yShift
  field_simp
  ring

theorem cosetTheta_hasSum (a b L : ℝ) (hL : 0 < L) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ =>
      (Real.exp (-Real.pi * normForm (a + L * n.1) (b + L * n.2) * t) : ℂ))
      (∑ e : Fin 2, (parityPair a b L hL e).f t) := by
  let F : Fin 2 × (ℤ × ℤ) → ℝ := fun p =>
    Real.exp (-Real.pi * (L ^ 2 * (p.2.1 + xShift a b L p.1) ^ 2 +
      (3 * L ^ 2) * (p.2.2 + yShift b L p.1) ^ 2) * t)
  have hsum (e : Fin 2) : HasSum (fun n : ℤ × ℤ => (F (e, n) : ℂ))
      ((parityPair a b L hL e).f t) :=
    rectangularPair_hasSum (xShift a b L e) (yShift b L e) (L ^ 2) (3 * L ^ 2) (sq_pos_of_pos hL)
      (mul_pos (by norm_num) (sq_pos_of_pos hL)) ht
  have hreal (e : Fin 2) : Summable (fun n : ℤ × ℤ => F (e, n)) :=
    Complex.summable_ofReal.mp (hsum e).summable
  have hF : Summable F :=
    (summable_prod_of_nonneg (fun _ => (Real.exp_pos _).le)).2
      ⟨hreal, (hasSum_fintype _).summable⟩
  have hFC : Summable (fun p => (F p : ℂ)) := Complex.summable_ofReal.mpr hF
  have hid (p : Fin 2 × (ℤ × ℤ)) :
      Real.exp (-Real.pi * normForm
        (a + L * (parityEquiv.symm p).1) (b + L * (parityEquiv.symm p).2) * t) = F p := by
    change Real.exp (-Real.pi * normForm
      (a + L * ((p.2.1 + p.2.2 : ℤ) : ℝ))
      (b + L * ((p.2.2 * 2 + (p.1 : ℕ) : ℤ) : ℝ)) * t) = _
    push_cast
    rw [show (p.2.2 : ℝ) * 2 = 2 * p.2.2 from mul_comm _ _]
    rw [normForm_parity a b L hL.ne']
  apply parityEquiv.symm.hasSum_iff.mp
  change HasSum (fun p : Fin 2 × (ℤ × ℤ) =>
    (Real.exp (-Real.pi * normForm (a + L * (parityEquiv.symm p).1)
      (b + L * (parityEquiv.symm p).2) * t) : ℂ)) _
  simp_rw [hid]
  convert (preTransparency := .instances) hFC.hasSum using 1
  rw [hFC.tsum_prod, tsum_fintype]
  exact (Finset.sum_congr rfl (fun e _ => (hsum e).tsum_eq)).symm

@[simp] theorem parityPair_k (a b L : ℝ) (hL : 0 < L) (e : Fin 2) :
    (parityPair a b L hL e).k = 1 := rectangularPair_k _ _ _ _ _ _

def cosetConstant (a b L : ℝ) (hL : 0 < L) : ℂ :=
  ∑ e : Fin 2, (parityPair a b L hL e).f₀

theorem parityPair_f₀ (a b L : ℝ) (hL : 0 < L) (e : Fin 2) :
    (parityPair a b L hL e).f₀ =
      (if (xShift a b L e : UnitAddCircle) = 0 then 1 else 0) *
      (if (yShift b L e : UnitAddCircle) = 0 then 1 else 0) := rfl

theorem cosetConstant_eq (a b L : ℝ) (hL : 0 < L)
    (ha₀ : 0 ≤ a) (haL : a < L) (hb₀ : 0 ≤ b) (hbL : b < L) :
    cosetConstant a b L hL = if a = 0 ∧ b = 0 then 1 else 0 := by
  have htwo : 0 < 2 * L := by positivity
  have hy1 : yShift b L 1 ∈ Set.Ico (0 : ℝ) 1 := by
    simp only [yShift, Fin.val_one, Nat.cast_one, mul_one, Set.mem_Ico]
    constructor
    · positivity
    · apply (div_lt_one htwo).2
      linarith
  have hy1pos : 0 < yShift b L 1 := by
    simp only [yShift, Fin.val_one, Nat.cast_one, mul_one]
    exact div_pos (by linarith) htwo
  have hy1ne : (yShift b L 1 : UnitAddCircle) ≠ 0 := by
    intro h
    have := (AddCircle.coe_eq_zero_iff_of_mem_Ico hy1).mp h
    linarith
  have hy0 : yShift b L 0 ∈ Set.Ico (0 : ℝ) 1 := by
    simp only [yShift, Fin.val_zero, Nat.cast_zero, mul_zero, add_zero, Set.mem_Ico]
    constructor
    · positivity
    · apply (div_lt_one htwo).2
      linarith
  have hy0iff : (yShift b L 0 : UnitAddCircle) = 0 ↔ b = 0 := by
    rw [AddCircle.coe_eq_zero_iff_of_mem_Ico hy0]
    simp [yShift, div_eq_zero_iff, hL.ne']
  rw [cosetConstant, Fin.sum_univ_two, parityPair_f₀, parityPair_f₀,
    if_neg hy1ne, mul_zero, add_zero]
  by_cases hb : b = 0
  · subst b
    rw [if_pos (hy0iff.mpr rfl), mul_one]
    have hx : xShift a 0 L 0 = a / L := by
      simp only [xShift, sub_zero, Fin.val_zero, Nat.cast_zero, mul_zero]
      field_simp
    have hxmem : a / L ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨div_nonneg ha₀ hL.le, (div_lt_one hL).2 haL⟩
    have hxiff : (xShift a 0 L 0 : UnitAddCircle) = 0 ↔ a = 0 := by
      rw [hx, AddCircle.coe_eq_zero_iff_of_mem_Ico hxmem]
      simp [div_eq_zero_iff, hL.ne']
    simp only [hxiff, and_true]
  · rw [if_neg (fun h => hb (hy0iff.mp h)), mul_zero, if_neg (fun h => hb h.2)]

end SevenEighths.EisensteinTheta

end

end OAI
end

section

namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta

def regroup (N : ℕ) : ((ℤ × Fin N) × (ℤ × Fin N)) ≃ ((Fin N × Fin N) × (ℤ × ℤ)) where
  toFun p := ((p.1.2, p.2.2), (p.1.1, p.2.1))
  invFun p := ((p.2.1, p.1.1), (p.2.2, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def residueEquiv (N : ℕ) [NeZero N] : (ℤ × ℤ) ≃ ((Fin N × Fin N) × (ℤ × ℤ)) :=
  (Equiv.prodCongr (Int.divModEquiv N) (Int.divModEquiv N)).trans (regroup N)

def periodicCoeff {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (n : ℤ × ℤ) : ℂ :=
  w (residueEquiv N n).1

def theta {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℤ × ℤ, periodicCoeff w n *
    (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ)

@[simp] theorem pair_k {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).k = 1 := rfl

theorem theta_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ => periodicCoeff w n *
      (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ)) ((pair w).f t) := by
  let hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  let F : (Fin N × Fin N) × (ℤ × ℤ) → ℂ := fun p => w p.1 *
    (Real.exp (-Real.pi * normForm (p.1.1 + (N : ℝ) * p.2.1)
      (p.1.2 + (N : ℝ) * p.2.2) * t) : ℂ)
  have hinner (a : Fin N × Fin N) : HasSum (fun n : ℤ × ℤ => F (a,n))
      (w a * ∑ e : Fin 2, (parityPair a.1 a.2 N hN e).f t) :=
    (cosetTheta_hasSum a.1 a.2 N hN ht).mul_left (w a)
  have hFnorm : Summable (fun p => ‖F p‖) :=
    (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
      ⟨fun a => (hinner a).summable.norm, (hasSum_fintype _).summable⟩
  have hF : Summable F := hFnorm.of_norm
  have hid (p : (Fin N × Fin N) × (ℤ × ℤ)) :
      periodicCoeff w ((residueEquiv N).symm p) *
        (Real.exp (-Real.pi * normForm (((residueEquiv N).symm p).1)
          (((residueEquiv N).symm p).2) * t) : ℂ) = F p := by
    simp only [periodicCoeff, Equiv.apply_symm_apply]
    change w p.1 * (Real.exp (-Real.pi * normForm
      ((p.2.1 * (N : ℤ) + p.1.1 : ℤ) : ℝ)
      ((p.2.2 * (N : ℤ) + p.1.2 : ℤ) : ℝ) * t) : ℂ) = F p
    simp only [F, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    congr 4 ; ring_nf
  apply (residueEquiv N).symm.hasSum_iff.mp
  change HasSum (fun p => periodicCoeff w ((residueEquiv N).symm p) *
    (Real.exp (-Real.pi * normForm (((residueEquiv N).symm p).1)
      (((residueEquiv N).symm p).2) * t) : ℂ)) _
  simp_rw [hid]
  convert (preTransparency := .instances) hF.hasSum using 1
  rw [hF.tsum_prod, tsum_fintype]
  simp_rw [(hinner _).tsum_eq]
  simp only [pair, finitePair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, Finset.mul_sum]

theorem theta_eq_pair {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) : theta w t = (pair w).f t :=
  (theta_hasSum w ht).tsum_eq

theorem pair_f₀ {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).f₀ = w (0, 0) := by
  have hconst (a : Fin N × Fin N) :
      cosetConstant a.1 a.2 N (Nat.cast_pos.mpr (NeZero.pos N)) =
        if a = (0, 0) then 1 else 0 := by
    rw [cosetConstant_eq _ _ _ _ (by positivity) (by exact_mod_cast a.1.isLt)
      (by positivity) (by exact_mod_cast a.2.isLt)]
    have hz : (a.1 : ℝ) = 0 ∧ (a.2 : ℝ) = 0 ↔ a = (0, 0) := by
      simp only [Prod.ext_iff, Fin.ext_iff, Fin.val_zero, Nat.cast_eq_zero]
    simp only [hz]
  change (∑ p : (Fin N × Fin N) × Fin 2,
    w p.1 * (parityPair p.1.1 p.1.2 N _ p.2).f₀) = _
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  change (∑ a : Fin N × Fin N, w a * cosetConstant a.1 a.2 N _) = _
  simp_rw [hconst]
  simp

def dualScalar (N : ℕ) : ℂ :=
  ((((N : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    (((3 * (N : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

theorem pair_g₀ {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).g₀ = 2 * dualScalar N * ∑ a, w a := by
  simp only [pair, finitePair, parityPair, ThetaProduct.rectangularPair,
    ThetaProduct.product, ThetaProduct.scaledEvenPair, ThetaProduct.rescale,
    HurwitzZeta.hurwitzEvenFEPair, one_mul, mul_one]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  simp_rw [← two_mul]
  rw [← Finset.mul_sum]
  simp only [← Finset.sum_mul, dualScalar]
  ring

theorem pair_g₀_eq_zero {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (hw : ∑ a, w a = 0) : (pair w).g₀ = 0 := by rw [pair_g₀, hw, mul_zero]

theorem pair_hasMellin {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun t => (pair w).f t - (pair w).f₀) s (completed w s) :=
  (pair w).hasMellin (by simpa using hs)

def regularizedCompleted {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (s : ℂ) : ℂ :=
  (s - 1) * ((pair w).Λ₀ s - s⁻¹ * (pair w).f₀) + (pair w).g₀

def regularizedLatticeL {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * regularizedCompleted w s

end SevenEighths.HeckeTheta

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeFamily

def Character.ofResidue (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk M (u : O)) = 1) : Character := by
  letI : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  letI : Fintype (O ⧸ M) := Fintype.ofFinite _
  exact {
    modulus := M
    modulus_ne_bot := hM
    residue := χ
    unit_trivial := hu
    period := Fintype.card (O ⧸ M)
    period_pos := Fintype.card_pos
    period_mem := Ideal.Quotient.eq_zero_iff_mem.mp (by
      simpa only [map_natCast] using Nat.cast_card_eq_zero (O ⧸ M)) }

@[simp] theorem elementCoeff_one (χ : Character) : elementCoeff χ 1 = 1 := by
  simp [elementCoeff]

theorem elementCoeff_mul (χ : Character) (z w : O) :
    elementCoeff χ (z * w) = elementCoeff χ z * elementCoeff χ w := by
  simp [elementCoeff, map_mul]

theorem elementCoeff_unit_mul (χ : Character) (u : Oˣ) (z : O) :
    elementCoeff χ ((u : O) * z) = elementCoeff χ z := by
  rw [elementCoeff_mul]
  have hu : elementCoeff χ (u : O) = 1 := χ.unit_trivial u
  rw [hu, one_mul]

theorem quotient_period (χ : Character) :
    Ideal.Quotient.mk χ.modulus (χ.period : O) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr χ.period_mem

theorem elementCoeff_add_period_mul (χ : Character) (z w : O) :
    elementCoeff χ (z + (χ.period : O) * w) = elementCoeff χ z := by
  simp [elementCoeff, map_add, map_mul, quotient_period χ]

theorem periodicCoeff_eq_elementCoeff (χ : Character) (n : ℤ × ℤ) :
    HeckeTheta.periodicCoeff (coefficients χ) n =
      elementCoeff χ (coordinateElement n.1 n.2) := by
  obtain ⟨p, rfl⟩ := (HeckeTheta.residueEquiv χ.period).symm.surjective n
  simp only [HeckeTheta.periodicCoeff, Equiv.apply_symm_apply, coefficients]
  change elementCoeff χ (coordinateElement p.1.1 p.1.2) =
    elementCoeff χ (coordinateElement (p.2.1 * (χ.period : ℤ) + p.1.1)
      (p.2.2 * (χ.period : ℤ) + p.1.2))
  have heq : coordinateElement (p.2.1 * (χ.period : ℤ) + p.1.1)
      (p.2.2 * (χ.period : ℤ) + p.1.2) =
      coordinateElement p.1.1 p.1.2 + (χ.period : O) *
        ((p.2.1 : O) + (p.2.2 : O) * omega) := by
    unfold coordinateElement
    push_cast
    ring
  rw [heq, elementCoeff_add_period_mul]

end SevenEighths.HeckeFamily

end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeCoordinates
open HeckeFamily

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
theorem hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K) 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
def pb : PowerBasis ℤ O := hζ.integralPowerBasis

theorem pb_dim : pb.dim = 2 := by
  simp [pb, Nat.totient_prime Nat.prime_three]

theorem pb_gen : pb.gen = HeckeFamily.omega := hζ.integralPowerBasis_gen

theorem coordinateElement_surjective :
    Function.Surjective (fun n : ℤ × ℤ => coordinateElement n.1 n.2) := by
  intro x
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let a : ℤ := (pb.basis.repr x) i0
  let b : ℤ := (pb.basis.repr x) i1
  refine ⟨(a,b), ?_⟩
  have hsum := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    ext i
    have hi : i.val < 2 := by simpa only [pb_dim] using i.isLt
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hv with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rw [huniv] at hsum
  have hne : i0 ≠ i1 := by decide
  have hnot : i0 ∉ ({i1} : Finset (Fin pb.dim)) := by
    simpa only [Finset.mem_singleton] using hne
  rw [Finset.sum_insert hnot, Finset.sum_singleton] at hsum
  simp only [pb.basis_eq_pow] at hsum
  simpa [a, b, i0, i1, pb_gen, coordinateElement, smul_eq_mul, mul_comm] using hsum

def intQuotientHom (χ : Character) : ℤ →+ (O ⧸ χ.modulus) :=
  (Ideal.Quotient.mk χ.modulus).toAddMonoidHom.comp (Int.castAddHom O)

def zmodQuotientHom (χ : Character) : ZMod χ.period →+ (O ⧸ χ.modulus) :=
  ZMod.lift χ.period ⟨intQuotientHom χ, by
    change Ideal.Quotient.mk χ.modulus ((χ.period : ℤ) : O) = 0
    simpa only [Int.cast_natCast] using quotient_period χ⟩

@[simp] theorem zmodQuotientHom_intCast (χ : Character) (a : ℤ) :
    zmodQuotientHom χ (a : ZMod χ.period) = Ideal.Quotient.mk χ.modulus (a : O) :=
  ZMod.lift_coe _ _ _

@[simp] theorem zmodQuotientHom_natCast (χ : Character) (a : ℕ) :
    zmodQuotientHom χ (a : ZMod χ.period) = Ideal.Quotient.mk χ.modulus (a : O) := by
  simpa only [Int.cast_natCast] using zmodQuotientHom_intCast χ (a : ℤ)

def coordinateQuotientHom (χ : Character) :
    (ZMod χ.period × ZMod χ.period) →+ (O ⧸ χ.modulus) where
  toFun p := zmodQuotientHom χ p.1 +
    zmodQuotientHom χ p.2 * Ideal.Quotient.mk χ.modulus HeckeFamily.omega
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring

@[simp] theorem coordinateQuotientHom_intCast (χ : Character) (a b : ℤ) :
    coordinateQuotientHom χ (a, b) =
      Ideal.Quotient.mk χ.modulus (coordinateElement a b) := by
  simp only [coordinateQuotientHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    zmodQuotientHom_intCast, coordinateElement, map_add, map_mul]

theorem coordinateQuotientHom_surjective (χ : Character) :
    Function.Surjective (coordinateQuotientHom χ) := by
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a,b⟩, hab⟩ := coordinateElement_surjective z
  change coordinateElement a b = z at hab
  exact ⟨(a,b), by rw [coordinateQuotientHom_intCast, hab]⟩

theorem coefficients_eq_quotient_character (χ : Character)
    (a : Fin χ.period × Fin χ.period) :
    coefficients χ a = χ.residue (coordinateQuotientHom χ (a.1, a.2)) := by
  simp [HeckeFamily.coefficients, HeckeFamily.elementCoeff, coordinateQuotientHom,
    coordinateElement]

end SevenEighths.HeckeCoordinates

end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.LatticeSummability
open EisensteinTheta

theorem normForm_nonneg (x y : ℝ) : 0 ≤ normForm x y := by
  unfold normForm
  nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]

theorem normForm_eq_zero_iff (x y : ℝ) : normForm x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    unfold normForm at h
    have hx : x ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]
    have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]
    exact ⟨sq_eq_zero_iff.mp hx, sq_eq_zero_iff.mp hy⟩
  · rintro ⟨rfl, rfl⟩
    simp [normForm]

theorem normForm_ge_half_norm_sq (n : ℤ × ℤ) :
    (1 / 2 : ℝ) * ‖n‖ ^ 2 ≤ normForm n.1 n.2 := by
  rw [Prod.norm_def, ← Int.norm_cast_real, ← Int.norm_cast_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  unfold normForm
  rcases le_total |(n.1 : ℝ)| |(n.2 : ℝ)| with h | h
  · rw [max_eq_right h, sq_abs]
    nlinarith [sq_nonneg ((n.1 : ℝ) - n.2), sq_nonneg (n.1 : ℝ)]
  · rw [max_eq_left h, sq_abs]
    nlinarith [sq_nonneg ((n.1 : ℝ) - n.2), sq_nonneg (n.2 : ℝ)]

theorem summable_pair_norm_rpow {k : ℝ} (hk : 2 < k) :
    Summable (fun n : ℤ × ℤ => ‖n‖ ^ (-k)) := by
  have h := (finTwoArrowEquiv ℤ).symm.summable_iff.mpr
    (EisensteinSeries.summable_one_div_norm_rpow hk)
  have hn (n : ℤ) : (n.natAbs : ℝ) = ‖n‖ := by
    exact congrArg (fun x : NNReal => (x : ℝ)) (NNReal.natCast_natAbs n)
  simpa only [finTwoArrowEquiv_symm_apply, Function.comp_def,
    EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero,
    Matrix.cons_val_one, Prod.norm_def, Nat.cast_max, hn] using h

theorem summable_normForm_neg_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => normForm n.1 n.2 ^ (-σ)) := by
  have hmajor := (summable_pair_norm_rpow (k := 2 * σ) (by linarith)).mul_left
    ((1 / 2 : ℝ) ^ (-σ))
  apply Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg (normForm_nonneg _ _) _) _ hmajor
  intro n
  by_cases hn : n = 0
  · subst n
    simp [normForm, Real.zero_rpow (by linarith : -σ ≠ 0),
      Real.zero_rpow (by linarith : -(2 * σ) ≠ 0)]
  · have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn
    calc
      normForm n.1 n.2 ^ (-σ) ≤ ((1 / 2 : ℝ) * ‖n‖ ^ 2) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (normForm_ge_half_norm_sq n)
          (by linarith)
      _ = (1 / 2 : ℝ) ^ (-σ) * ‖n‖ ^ (-(2 * σ)) := by
        rw [Real.mul_rpow (by norm_num) (sq_nonneg _)]
        congr 1
        rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        ring

theorem summable_one_div_normForm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => 1 / normForm n.1 n.2 ^ σ) := by
  simpa only [Real.rpow_neg (normForm_nonneg _ _), one_div] using
    summable_normForm_neg_rpow hσ

theorem summable_weighted_normForm {w : ℤ × ℤ → ℂ} {C σ : ℝ}
    (hw : ∀ n, ‖w n‖ ≤ C) (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => ‖w n‖ / normForm n.1 n.2 ^ σ) := by
  apply Summable.of_nonneg_of_le (fun n => div_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (normForm_nonneg _ _) _)) _
    ((summable_one_div_normForm_rpow hσ).mul_left C)
  intro n
  simpa only [mul_one_div] using
    div_le_div_of_nonneg_right (hw n) (Real.rpow_nonneg (normForm_nonneg _ _) _)

end SevenEighths.LatticeSummability

end

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta LatticeSummability

@[simp] theorem periodicCoeff_zero {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    periodicCoeff w (0, 0) = w (0, 0) := by
  simp [periodicCoeff, residueEquiv, regroup, Int.divModEquiv, Int.natMod]

theorem norm_periodicCoeff_le {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (n : ℤ × ℤ) : ‖periodicCoeff w n‖ ≤ ∑ a, ‖w a‖ := by
  unfold periodicCoeff
  exact Finset.single_le_sum (fun a _ => norm_nonneg (w a)) (Finset.mem_univ _)

theorem normForm_coordinates_eq_zero (n : ℤ × ℤ) :
    normForm n.1 n.2 = 0 ↔ n = (0, 0) := by
  rw [normForm_eq_zero_iff]
  simp only [Int.cast_eq_zero, Prod.ext_iff]

theorem theta_sub_zero_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ => if normForm n.1 n.2 = 0 then 0 else
      periodicCoeff w n * (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ))
      ((pair w).f t - (pair w).f₀) := by
  have h := (theta_hasSum w ht).sub (hasSum_ite_eq (0, 0) (w (0, 0)))
  rw [pair_f₀]
  convert (preTransparency := .instances) h using 1
  funext n
  simp only [normForm_coordinates_eq_zero]
  by_cases hn : n = (0, 0)
  · subst n
    simp [normForm]
  · simp [hn]

theorem completed_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
      periodicCoeff w n / (normForm n.1 n.2 : ℂ) ^ s) (completed w s) := by
  have hsum : Summable (fun n : ℤ × ℤ => ‖periodicCoeff w n‖ /
      normForm n.1 n.2 ^ s.re) :=
    summable_weighted_normForm (norm_periodicCoeff_le w) hs
  have h := hasSum_mellin_pi_mul₀
    (a := periodicCoeff w) (p := fun n : ℤ × ℤ => normForm n.1 n.2)
    (F := fun t => (pair w).f t - (pair w).f₀)
    (fun _ => normForm_nonneg _ _) (by linarith : 0 < s.re)
    (fun _ ht => theta_sub_zero_hasSum w ht) hsum
  rwa [(pair_hasMellin w hs).2] at h

theorem latticeL_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => periodicCoeff w n / (normForm n.1 n.2 : ℂ) ^ s)
      (latticeL w s) := by
  have hΓ := Complex.Gamma_ne_zero_of_re_pos (by linarith : 0 < s.re)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : (Real.pi : ℂ) ^ s ≠ 0 := fun h => hπ ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have h := (completed_hasSum w hs).mul_left ((Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹)
  change HasSum _ ((Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * completed w s)
  convert (preTransparency := .instances) h using 1
  funext n
  rw [Complex.cpow_neg]
  field_simp

end SevenEighths.HeckeTheta

end

end OAI
end

section

namespace OAI

noncomputable section

namespace SevenEighths.HeckeFamily
open EisensteinTheta

theorem continuedLattice_hasSum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => elementCoeff χ (coordinateElement n.1 n.2) /
      (normForm n.1 n.2 : ℂ) ^ s) (continuedLattice χ s) := by
  simpa only [periodicCoeff_eq_elementCoeff, continuedLattice] using HeckeTheta.latticeL_hasSum (coefficients χ) hs

end SevenEighths.HeckeFamily

end

end OAI
end

section

namespace OAI

namespace SevenEighths.ResidueCharacter

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A]

def inflate {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) :
    MulChar (A ⧸ M) ℂ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp
    (Units.map (Ideal.Quotient.factor hML).toMonoidHom))

theorem inflate_apply_unit {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ)
    (u : (A ⧸ M)ˣ) :
    inflate hML χ u = χ (Ideal.Quotient.factor hML (u : A ⧸ M)) :=
  MulChar.ofUnitHom_coe _ u

theorem inflate_apply {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ)
    (x : A ⧸ M) :
    inflate hML χ x = if IsUnit x then χ (Ideal.Quotient.factor hML x) else 0 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    simpa only [u.isUnit, ite_true] using inflate_apply_unit hML χ u
  · simp only [hx, ite_false, MulChar.map_nonunit _ hx]

theorem inflate_mk {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ) (a : A) :
    inflate hML χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then χ (Ideal.Quotient.mk L a) else 0 := by
  simpa only [Ideal.Quotient.factor_mk] using inflate_apply hML χ (Ideal.Quotient.mk M a)

theorem inflate_global_units {M L : Ideal A} (hML : M ≤ L) (χ : MulChar (A ⧸ L) ℂ)
    (hχ : ∀ u : Aˣ, χ (Ideal.Quotient.mk L u) = 1) :
    ∀ u : Aˣ, inflate hML χ (Ideal.Quotient.mk M u) = 1 := by
  intro u
  rw [inflate_mk]
  simp only [u.isUnit.map (Ideal.Quotient.mk M), ite_true, hχ]

theorem isUnit_mk_inf_iff (I J : Ideal A) (a : A) :
    IsUnit (Ideal.Quotient.mk (I ⊓ J) a) ↔
      IsUnit (Ideal.Quotient.mk I a) ∧ IsUnit (Ideal.Quotient.mk J a) := by
  constructor
  · intro h
    constructor
    · simpa only [Ideal.Quotient.factor_mk] using
        (h.map (Ideal.Quotient.factor (show I ⊓ J ≤ I from inf_le_left)))
    · simpa only [Ideal.Quotient.factor_mk] using
        (h.map (Ideal.Quotient.factor (show I ⊓ J ≤ J from inf_le_right)))
  · rintro ⟨hI, hJ⟩
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hI
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hJ
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hbI : a * b - 1 ∈ I :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp (by simpa only [map_mul] using hb)
    have hcJ : a * c - 1 ∈ J :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp (by simpa only [map_mul] using hc)
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk (I ⊓ J) (b + c - a * b * c), ?_⟩
    rw [← map_mul]
    apply (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr
    have hid : a * (b + c - a * b * c) - 1 = -((a * b - 1) * (a * c - 1)) := by ring
    rw [hid]
    exact ⟨I.neg_mem (I.mul_mem_right _ hbI), J.neg_mem (J.mul_mem_left _ hcJ)⟩

def product (I J : Ideal A) (χ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ) :
    MulChar (A ⧸ I ⊓ J) ℂ :=
  inflate inf_le_left χ * inflate inf_le_right ψ

theorem product_mk (I J : Ideal A) (χ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ)
    (a : A) :
    product I J χ ψ (Ideal.Quotient.mk (I ⊓ J) a) =
      χ (Ideal.Quotient.mk I a) * ψ (Ideal.Quotient.mk J a) := by
  rw [product, MulChar.mul_apply, inflate_mk, inflate_mk]
  by_cases ha : IsUnit (Ideal.Quotient.mk (I ⊓ J) a)
  · simp only [ha, ite_true]
  · simp only [ha, ite_false, zero_mul]
    by_cases hI : IsUnit (Ideal.Quotient.mk I a)
    · have hJ : ¬ IsUnit (Ideal.Quotient.mk J a) := fun hJ =>
        ha ((isUnit_mk_inf_iff I J a).mpr ⟨hI, hJ⟩)
      rw [MulChar.map_nonunit _ hJ, mul_zero]
    · rw [MulChar.map_nonunit _ hI, zero_mul]

theorem product_global_units (I J : Ideal A) (χ : MulChar (A ⧸ I) ℂ)
    (ψ : MulChar (A ⧸ J) ℂ)
    (hχ : ∀ u : Aˣ, χ (Ideal.Quotient.mk I u) = 1)
    (hψ : ∀ u : Aˣ, ψ (Ideal.Quotient.mk J u) = 1) :
    ∀ u : Aˣ, product I J χ ψ (Ideal.Quotient.mk (I ⊓ J) u) = 1 := by
  intro u
  rw [product_mk, hχ, hψ, one_mul]

end

end SevenEighths.ResidueCharacter

end OAI
end

section

namespace OAI

namespace SevenEighths.IdealCharacter

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open Submodule.IsPrincipal
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A]

abbrev UnitInvariant (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) : Prop :=
  ∀ u : Aˣ, χ (Ideal.Quotient.mk M u) = 1

theorem residue_eq_of_associated (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) {a b : A} (hab : Associated a b) :
    χ (Ideal.Quotient.mk M a) = χ (Ideal.Quotient.mk M b) := by
  obtain ⟨u, rfl⟩ := hab
  rw [map_mul, map_mul, hχ u, mul_one]

theorem isUnit_mk_iff_isCoprime (M : Ideal A) (a : A) :
    IsUnit (Ideal.Quotient.mk M a) ↔ IsCoprime (Ideal.span ({a} : Set A)) M := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Ideal.mem_span_singleton_sup]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv'.mp h
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hba : b * a - 1 ∈ M :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp (by simpa only [map_mul] using hb)
    refine ⟨b, -(b * a - 1), M.neg_mem hba, ?_⟩
    ring
  · rintro ⟨b, c, hc, hbc⟩
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨Ideal.Quotient.mk M b, ?_⟩
    have h := congrArg (Ideal.Quotient.mk M) hbc
    simpa only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hc,
      add_zero, map_one] using h

section Principal

variable [IsDomain A] [IsPrincipalIdealRing A]

def value (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (I : Ideal A) : ℂ :=
  if I = ⊥ then 0 else χ (Ideal.Quotient.mk M (generator I))

omit [IsDomain A] in
theorem value_bot (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) : value M χ ⊥ = 0 := by
  simp only [value, ite_true]

theorem value_span (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ)
    {a : A} (ha : a ≠ 0) :
    value M χ (Ideal.span ({a} : Set A)) = χ (Ideal.Quotient.mk M a) := by
  have hI : Ideal.span ({a} : Set A) ≠ ⊥ := by
    exact fun h => ha (Ideal.span_singleton_eq_bot.mp h)
  simp only [value, hI, ite_false]
  exact residue_eq_of_associated M χ hχ (associated_generator_span_self a)

def ofResidue (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    Ideal A →*₀ ℂ where
  toFun := value M χ
  map_zero' := value_bot M χ
  map_one' := by
    simpa only [Ideal.span_singleton_one, Ideal.one_eq_top, map_one] using
      value_span M χ hχ (one_ne_zero : (1 : A) ≠ 0)
  map_mul' I J := by
    by_cases hI : I = ⊥
    · subst I
      simp only [Ideal.bot_mul, value_bot, zero_mul]
    by_cases hJ : J = ⊥
    · subst J
      simp only [Ideal.mul_bot, value_bot, mul_zero]
    let a := generator I
    let b := generator J
    have ha : a ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    have hb : b ≠ 0 := fun h => hJ ((eq_bot_iff_generator_eq_zero J).mpr h)
    have hIa : Ideal.span ({a} : Set A) = I := Ideal.span_singleton_generator I
    have hJb : Ideal.span ({b} : Set A) = J := Ideal.span_singleton_generator J
    calc
      value M χ (I * J) = value M χ (Ideal.span ({a * b} : Set A)) := by
        rw [← Ideal.span_singleton_mul_span_singleton, hIa, hJb]
      _ = χ (Ideal.Quotient.mk M (a * b)) := value_span M χ hχ (mul_ne_zero ha hb)
      _ = χ (Ideal.Quotient.mk M a) * χ (Ideal.Quotient.mk M b) := by
        rw [map_mul, map_mul]
      _ = value M χ I * value M χ J := by
        rw [← hIa, ← hJb, value_span M χ hχ ha, value_span M χ hχ hb]

@[simp] theorem ofResidue_bot (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) : ofResidue M χ hχ ⊥ = 0 := value_bot M χ

theorem ofResidue_span (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ)
    {a : A} (ha : a ≠ 0) :
    ofResidue M χ hχ (Ideal.span ({a} : Set A)) = χ (Ideal.Quotient.mk M a) :=
  value_span M χ hχ ha

theorem ofResidue_of_generator (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) {I : Ideal A} (hI : I ≠ ⊥) {a : A}
    (ha : Ideal.span ({a} : Set A) = I) :
    ofResidue M χ hχ I = χ (Ideal.Quotient.mk M a) := by
  have ha0 : a ≠ 0 := by
    intro h
    apply hI
    simpa only [h, Ideal.span_singleton_zero] using ha.symm
  rw [← ha, ofResidue_span M χ hχ ha0]

omit [IsDomain A] [IsPrincipalIdealRing A] in
theorem norm_residue_le_one (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (a : A ⧸ M) : ‖χ a‖ ≤ 1 := by
  let : Fintype (A ⧸ M)ˣ := Fintype.ofFinite _
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    have hn : ‖χ (u : A ⧸ M)‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using h
    exact hn.le
  · rw [MulChar.map_nonunit χ ha, norm_zero]
    exact zero_le_one

theorem norm_ofResidue_le_one (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) (I : Ideal A) :
    ‖ofResidue M χ hχ I‖ ≤ 1 := by
  by_cases hI : I = ⊥
  · rw [hI, ofResidue_bot, norm_zero]
    exact zero_le_one
  · change ‖value M χ I‖ ≤ 1
    simp only [value, hI, ite_false]
    exact norm_residue_le_one M χ _

omit [IsDomain A] [IsPrincipalIdealRing A] in

theorem one_unitInvariant (M : Ideal A) : UnitInvariant M (1 : MulChar (A ⧸ M) ℂ) := by
  intro u
  exact MulChar.one_apply (u.isUnit.map (Ideal.Quotient.mk M))

theorem ofResidue_one (M : Ideal A) (I : Ideal A) :
    ofResidue M 1 (one_unitInvariant M) I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 := by
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_true]
  · have hg : generator I ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    have heq := ofResidue_span M 1 (one_unitInvariant M) hg
    rw [Ideal.span_singleton_generator] at heq
    rw [heq]
    simp only [hI, ite_false]
    have hu : IsUnit (Ideal.Quotient.mk M (generator I)) ↔ IsCoprime I M := by
      simpa only [Ideal.span_singleton_generator] using isUnit_mk_iff_isCoprime M (generator I)
    by_cases hc : IsCoprime I M
    · simp only [hc, ite_true]
      exact MulChar.one_apply (hu.mpr hc)
    · simp only [hc, ite_false]
      exact MulChar.map_nonunit _ (fun h => hc (hu.mp h))

theorem ofResidue_source_mask (M K : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hχ : UnitInvariant M χ) (hφ : UnitInvariant K φ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0)
    (I : Ideal A) :
    ofResidue M χ hχ I = if IsCoprime I M then ofResidue K φ hφ I else 0 := by
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_self]
  · have hg : generator I ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    have h := hmask (generator I)
    have hcop : IsUnit (Ideal.Quotient.mk M (generator I)) ↔ IsCoprime I M := by
      simpa only [Ideal.span_singleton_generator] using isUnit_mk_iff_isCoprime M (generator I)
    rw [← ofResidue_span M χ hχ hg, ← ofResidue_span K φ hφ hg,
      Ideal.span_singleton_generator] at h
    simpa only [hcop] using h

theorem ofResidue_product (M N : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (ψ : MulChar (A ⧸ N) ℂ)
    (hχ : UnitInvariant M χ) (hψ : UnitInvariant N ψ) (I : Ideal A) :
    ofResidue (M ⊓ N) (ResidueCharacter.product M N χ ψ)
        (ResidueCharacter.product_global_units M N χ ψ hχ hψ) I =
      ofResidue M χ hχ I * ofResidue N ψ hψ I := by
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, mul_zero]
  · have hg : generator I ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    conv_lhs => rw [← Ideal.span_singleton_generator I]
    rw [ofResidue_span _ _ _ hg, ResidueCharacter.product_mk]
    rw [← ofResidue_span M χ hχ hg, ← ofResidue_span N ψ hψ hg,
      Ideal.span_singleton_generator]

end Principal

end

end SevenEighths.IdealCharacter

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

def Character.product (χ ψ : Character) : Character :=
  Character.ofResidue (χ.modulus ⊓ ψ.modulus)
    (Ideal.inf_ne_bot_of_ne_bot χ.modulus_ne_bot ψ.modulus_ne_bot)
    (ResidueCharacter.product χ.modulus ψ.modulus χ.residue ψ.residue)
    (ResidueCharacter.product_global_units _ _ _ _ χ.unit_trivial ψ.unit_trivial)

theorem elementCoeff_product (χ ψ : Character) (z : O) :
    elementCoeff (χ.product ψ) z = elementCoeff χ z * elementCoeff ψ z :=
  ResidueCharacter.product_mk _ _ _ _ z

def Character.inverse (χ : Character) : Character where
  modulus := χ.modulus
  modulus_ne_bot := χ.modulus_ne_bot
  residue := χ.residue⁻¹
  unit_trivial u := by simp [MulChar.inv_apply_eq_inv', χ.unit_trivial]
  period := χ.period
  period_pos := χ.period_pos
  period_mem := χ.period_mem

def Character.power (χ : Character) (n : ℕ) : Character where
  modulus := χ.modulus
  modulus_ne_bot := χ.modulus_ne_bot
  residue := χ.residue ^ n
  unit_trivial u := by
    let v := Units.map (Ideal.Quotient.mk χ.modulus).toMonoidHom u
    change (χ.residue ^ n) (v : O ⧸ χ.modulus) = 1
    rw [MulChar.pow_apply_coe]
    change χ.residue (Ideal.Quotient.mk χ.modulus u) ^ n = 1
    simp [χ.unit_trivial]
  period := χ.period
  period_pos := χ.period_pos
  period_mem := χ.period_mem

end SevenEighths.HeckeFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open Set Filter Asymptotics MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.PeriodicThetaRegularity
open ThetaProduct EisensteinTheta HeckeTheta

theorem rectangularPair_f_continuous (a b : UnitAddCircle) (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) :
    ContinuousOn (rectangularPair a b u v hu hv).f (Ioi 0) :=
  (scaledEvenPair_f_continuous a u hu).mul (scaledEvenPair_f_continuous b v hv)

theorem pair_f_continuous {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    ContinuousOn (pair w).f (Ioi 0) := by
  have h : ContinuousOn (fun t => ∑ p : (Fin N × Fin N) × Fin 2,
      w p.1 * (parityPair p.1.1 p.1.2 N (Nat.cast_pos.mpr (NeZero.pos N)) p.2).f t)
      (Ioi 0) := by
    apply continuousOn_finsetSum
    intro p _
    exact continuousOn_const.mul
      (rectangularPair_f_continuous (xShift p.1.1 p.1.2 N p.2)
        (yShift p.1.2 N p.2) _ _ _ _)
  apply h.congr
  intro t _
  simp only [pair, finitePair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem theta_continuous {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    ContinuousOn (theta w) (Ioi 0) :=
  (pair_f_continuous w).congr (fun _t ht => theta_eq_pair w ht)

theorem theta_rapid {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (r : ℝ) :
    (fun t => theta w t - w (0,0)) =O[atTop] (fun t : ℝ => t ^ r) := by
  apply ((pair w).hf_top r).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [theta_eq_pair w ht, pair_f₀]

theorem scaledTheta_continuous {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (A : ℝ) (hA : 0 < A) :
    ContinuousOn (fun t => theta w (A * t)) (Ioi 0) :=
  (theta_continuous w).comp (by fun_prop) (fun t ht => mul_pos hA ht)

theorem scaledTheta_rapid {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (A : ℝ) (hA : 0 < A) (r : ℝ) :
    (fun t => theta w (A * t) - w (0,0)) =O[atTop] (fun t : ℝ => t ^ r) :=
  rapid_rescale (theta w) (w (0,0)) (theta_rapid w) hA r

def primitivePair {N M : ℕ} [NeZero N] [NeZero M]
    (w : Fin N × Fin N → ℂ) (v : Fin M × Fin M → ℂ)
    (A : ℝ) (hA : 0 < A) (ε : ℂ) (hε : ε ≠ 0)
    (hfeq : ∀ t : ℝ, 0 < t →
      theta w (A / t) = ε * (t : ℂ) * theta v (A * t)) : WeakFEPair ℂ where
  f := fun t => theta w (A * t)
  g := fun t => theta v (A * t)
  k := 1
  ε := ε
  f₀ := w (0,0)
  g₀ := v (0,0)
  hf_int := (scaledTheta_continuous w A hA).locallyIntegrableOn measurableSet_Ioi
  hg_int := (scaledTheta_continuous v A hA).locallyIntegrableOn measurableSet_Ioi
  hk := zero_lt_one
  hε := hε
  h_feq t ht := by
    simpa only [mul_one_div, Real.rpow_one, smul_eq_mul] using hfeq t ht
  hf_top := scaledTheta_rapid w A hA
  hg_top := scaledTheta_rapid v A hA

end SevenEighths.PeriodicThetaRegularity

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical Topology
open Filter Asymptotics

namespace SevenEighths.ThetaRegularity

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic ConcreteTraceCRT

variable (c : O) [NeZero c]

end SevenEighths.ThetaRegularity

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Filter Asymptotics Set MeasureTheory

namespace SevenEighths.HeckeStrip

def gammaConstant : ℝ := Real.Gamma (11 / 10) / Real.Gamma (19 / 10)

def completionScale (Q : ℝ) : ℝ := Real.sqrt (3 * Q) / (2 * Real.pi)

def leftConstant : ℝ :=
  (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * gammaConstant

def strip : Set ℂ := Complex.re ⁻¹' Ioo (-(1 / 10)) (11 / 10)
def closedStrip : Set ℂ := Complex.re ⁻¹' Icc (-(1 / 10)) (11 / 10)

def normalized (Q : ℝ) (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  L z / (((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) * (z + 2) ^ 2)

end SevenEighths.HeckeStrip
end

end OAI
end

section

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where

  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

@[ext] protected theorem CS.ext {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {x y : CS n E}
    (h : x.toFun = y.toFun) : x = y := by
  cases x
  cases y
  cases h
  rfl

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where

  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

theorem contDiff_ofReal : ContDiff ℝ ∞ ofReal := Complex.ofRealCLM.contDiff

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := f.h2.neg

instance : Neg (CS n E) where neg := neg

@[simp] theorem neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] theorem smul_apply : (R • f) x = R • f x := rfl

theorem continuous (f : CS n E) : Continuous f := f.h1.continuous

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

end CS

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

end trunc

namespace W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

theorem continuous (f : W1 n E) : Continuous f := f.smooth.continuous

theorem iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  funext x
  exact _root_.iteratedDeriv_sub hf.contDiffAt hg.contDiffAt

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance : Sub (W1 n E) where sub := sub

theorem integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : (SchwartzMap.derivCLM ℝ ℂ f : ℝ → ℂ) = _root_.deriv f := by
      funext x
      exact SchwartzMap.derivCLM_apply ℝ f x
    rw [← hd]
    exact ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def ofSchwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun

noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.ofSchwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, ?_⟩
  intro k hk
  cases k with
  | zero => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | succ k =>
    cases k with
    | zero =>
      simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
    | succ k =>
      have hk0 : k = 0 :=
        Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk))
      subst k
      simpa [iteratedDeriv_succ] using
        (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

end W21
end

section

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

section lemmas

@[simp] theorem F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] theorem F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  exact congr_fun (fourierIntegral_add continuous_fourierChar continuous_inner hf hg) x

@[simp] theorem F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] theorem F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas

@[simp] theorem deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv
end

section

open MeasureTheory Set Real
open scoped ContDiff

theorem smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]
end

section

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]

noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'

attribute [fun_prop] Real.continuous_fourierChar

@[continuity]
theorem continuous_multiplicative_ofAdd : Continuous (⇑Multiplicative.ofAdd : ℝ → ℝ) := ⟨fun _ ↦ id⟩

attribute [fun_prop] measurable_coe_nnreal_ennreal

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i

def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n

def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)

def shift (u : α → E) (n : α) : E := u (n + 1)

@[simp] theorem cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]

@[simp] theorem nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]

omit [Sub α] in
@[simp] theorem nabla_mul [Ring E] {u : α → E} {c : E} :
    nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]

omit [Sub α] in
@[simp] theorem nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]

end nabla

@[local gcongr]
theorem norm_lt_norm_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖x‖ ≤ ‖y‖ := by
  simp_rw [Real.norm_eq_abs]
  apply abs_le_abs hxy
  linarith

theorem smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by
  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩

noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩

noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹

noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) :=
  h2.toSchwartzMap h1

@[simp] theorem toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl

@[norm_cast]
theorem set_integral_ofReal {f : ℝ → ℝ} {s : Set ℝ} : ∫ x in s, (f x : ℂ) = ∫ x in s, f x :=
  integral_ofReal

noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N
end

section

namespace OAI

namespace SevenEighths.IdealMangoldt

open ActualEisensteinCubic UniqueFactorizationMonoid ArithmeticFunction
open scoped BigOperators Classical

noncomputable section

def primeBase (I : Ideal O) : Ideal O := if h : IsPrimePow I then h.choose else 1

def value (I : Ideal O) : ℝ :=
  if IsPrimePow I then Real.log (Ideal.absNorm (primeBase I)) else 0

@[simp] theorem value_zero : value (0 : Ideal O) = 0 := by
  simp only [value, not_isPrimePow_zero, ite_false]

@[simp] theorem value_one : value (1 : Ideal O) = 0 := by
  simp only [value, not_isPrimePow_one, ite_false]

def normFiber (n : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset

@[simp] theorem mem_normFiber (n : ℕ) (I : Ideal O) : I ∈ normFiber n ↔ Ideal.absNorm I = n :=
  Set.Finite.mem_toFinset _

def coeff (w : Ideal O → ℝ) (n : ℕ) : ℝ := ∑ I ∈ normFiber n, w I * value I

def primesOver (p : ℕ) [Fact p.Prime] : Finset (Ideal O) :=
  (IsDedekindDomain.primesOver_finite (Ideal.span {(p : ℤ)}) O).toFinset

@[simp] theorem mem_primesOver (p : ℕ) [Fact p.Prime] (P : Ideal O) :
    P ∈ primesOver p ↔ P ∈ (Ideal.span {(p : ℤ)}).primesOver O :=
  Set.Finite.mem_toFinset _

def classCoeff (C : Set (Ideal O)) (n : ℕ) : ℝ :=
  coeff (fun I => if I ∈ C then 1 else 0) n

end

end SevenEighths.IdealMangoldt

end OAI
end

section

namespace OAI

namespace SevenEighths.PNT.IdealPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter
open SevenEighths.IdealMangoldt
open scoped BigOperators Classical Topology

noncomputable section

def primeClassCoeff (C : Set (Ideal O)) (n : ℕ) : ℝ :=
  classCoeff {I | I ∈ C ∧ Prime I} n

def higherClassCoeff (C : Set (Ideal O)) (n : ℕ) : ℝ :=
  classCoeff {I | I ∈ C ∧ ¬Prime I} n

def primeIdealsBelow (C : Set (Ideal O)) (N : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset.filter
    (fun P => P ∈ C ∧ Prime P ∧ Ideal.absNorm P < N)

@[simp] theorem mem_primeIdealsBelow (C : Set (Ideal O)) (N : ℕ) (P : Ideal O) :
    P ∈ primeIdealsBelow C N ↔ P ∈ C ∧ Prime P ∧ Ideal.absNorm P < N := by
  simp only [primeIdealsBelow, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.2.2.le, h⟩⟩

def primeLogMass (C : Set (Ideal O)) (N : ℕ) : ℝ :=
  ∑ P ∈ primeIdealsBelow C N, Real.log (Ideal.absNorm P)

end

end SevenEighths.PNT.IdealPrimeMass

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckePrimePowers
open HeckeFamily UniqueFactorizationMonoid

def logWeight (I : Ideal O) : ℝ := IdealMangoldt.value I / Real.log (Ideal.absNorm I)

end SevenEighths.HeckePrimePowers

end

end OAI
end

section

namespace OAI

namespace SevenEighths.RayOrthogonality

open scoped Classical
noncomputable section

section FiniteMonoid
variable {R : Type*} [CommMonoid R] [Finite R]

def characters (H : Subgroup Rˣ) : Subgroup (MulChar R ℂ) :=
  (MulChar.subgroupOrderIsoSubgroupMulChar R ℂ H).ofDual

instance (H : Subgroup Rˣ) : Fintype (characters H) := Fintype.ofFinite _

theorem mem_characters_iff (H : Subgroup Rˣ) (χ : MulChar R ℂ) :
    χ ∈ characters H ↔ ∀ u ∈ H, χ u = 1 :=
  MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff

def inUnitSubgroup (H : Subgroup Rˣ) (r : R) : Prop :=
  ∃ u : Rˣ, (u : R) = r ∧ u ∈ H

end FiniteMonoid

section Residues
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]

def globalUnits : Subgroup (A ⧸ M)ˣ :=
  (Units.map (Ideal.Quotient.mk M).toMonoidHom).range

abbrev rayCharacters := characters (globalUnits M)

theorem mem_rayCharacters_iff (χ : MulChar (A ⧸ M) ℂ) :
    χ ∈ rayCharacters M ↔ IdealCharacter.UnitInvariant M χ := by
  rw [mem_characters_iff]
  constructor
  · intro h u
    exact h _ ⟨u, rfl⟩
  · intro h u hu
    obtain ⟨v, rfl⟩ := hu
    exact h v

def principalResidue (r : A ⧸ M) : Prop :=
  ∃ u : Aˣ, Ideal.Quotient.mk M u = r

abbrev rayCard : ℕ := Nat.card ((A ⧸ M)ˣ ⧸ globalUnits M)

section PrincipalIdeals
variable [IsDomain A] [IsPrincipalIdealRing A]

def idealCharacter (χ : rayCharacters M) : Ideal A →*₀ ℂ :=
  IdealCharacter.ofResidue M χ ((mem_rayCharacters_iff M χ).mp χ.property)

def principalIdeals : Set (Ideal A) :=
  {I | I ≠ ⊥ ∧ ∃ a : A, Ideal.span ({a} : Set A) = I ∧
    principalResidue M (Ideal.Quotient.mk M a)}

theorem idealCharacter_one (I : Ideal A) :
    idealCharacter M 1 I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 :=
  IdealCharacter.ofResidue_one M I

end PrincipalIdeals
end Residues

end
end SevenEighths.RayOrthogonality

end OAI
end

section

namespace OAI

namespace SevenEighths.RayQuotient
open SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section

variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
    (H : Subgroup (A ⧸ M)ˣ) (hH : globalUnits M ≤ H)

abbrev Characters := characters H
abbrev classNumber := Nat.card ((A ⧸ M)ˣ ⧸ H)

include hH

theorem character_unitInvariant (χ : Characters M H) :
    IdealCharacter.UnitInvariant M χ := by
  intro u
  exact (mem_characters_iff H χ).mp χ.property _ (hH ⟨u, rfl⟩)

def toFullRay : Characters M H →* rayCharacters M where
  toFun χ := ⟨χ, (mem_rayCharacters_iff M χ).mpr (character_unitInvariant M H hH χ)⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

variable [IsDomain A] [IsPrincipalIdealRing A]

def idealCharacter (χ : Characters M H) : Ideal A →*₀ ℂ :=
  IdealCharacter.ofResidue M χ (character_unitInvariant M H hH χ)

def identityClass : Set (Ideal A) :=
  {I | I ≠ ⊥ ∧ ∃ a : A, Ideal.span ({a} : Set A) = I ∧
    inUnitSubgroup H (Ideal.Quotient.mk M a)}

end
end SevenEighths.RayQuotient

end OAI
end

section

namespace OAI

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]

def fourierSum (ψ : AddChar R ℂ) (place : X → R) (f : X → ℂ) (h : R) : ℂ :=
  ∑ x, f x * ψ (h * place x)

def fullCorrelation (left : X → R) (right : Y → R)
    (f : X → ℂ) (g : Y → ℂ) (j : R) : ℂ :=
  ∑ x, ∑ y, if left x - right y = j then f x * star (g y) else 0

section FiniteField
variable {F : Type*} [Field F] [Fintype F]

def shiftCorrelation (χ : MulChar F ℂ) (k : F) : ℂ :=
  ∑ x : F, χ x * star (χ (x - k))

def localCorrelation (χ : MulChar F ℂ) (n₁ n₂ k : F) : ℂ :=
  fullCorrelation (fun x : F => n₂ * x) (fun y : F => n₁ * y) χ χ k

end FiniteField

variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

def reductionMultiplicity (π : A →+* B) : ℕ :=
  (Finset.univ.filter fun x : A => π x = 0).card

end
end SevenEighths.CenteredMomentCorrelation

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckePrimeAmplitudeBins

def amplitude (P cap mesh : ℝ) (Q : ℂ) : ℝ :=
  if Q=0 then 0 else min cap (max 0 (mesh*(⌊Real.log ‖Q‖/(mesh*Real.log P)⌋ : ℤ)))

def labels (cap mesh : ℝ) : Finset ℝ :=
  insert 0 (insert cap ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ))))

theorem amplitude_mem_labels (P cap mesh : ℝ) (Q : ℂ) (hm : 0< mesh) :
    amplitude P cap mesh Q∈labels cap mesh := by
  by_cases hQ : Q=0
  · simp [amplitude,hQ,labels]
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  have he : amplitude P cap mesh Q=min cap (max 0 (mesh*(n : ℝ))) := by
    simp only [amplitude,if_neg hQ]
    rfl
  rw [he]
  by_cases hc : cap≤ max 0 (mesh*(n : ℝ))
  · rw [min_eq_left hc]
    simp [labels]
  rw [min_eq_right (le_of_not_ge hc)]
  by_cases hn : mesh*(n : ℝ)≤0
  · rw [max_eq_left hn]
    simp [labels]
  have hn' : 0< mesh*(n : ℝ) := lt_of_not_ge hn
  rw [max_eq_right hn'.le]
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  refine ⟨n,Finset.mem_Icc.mpr ⟨?_,?_⟩,rfl⟩
  · have hh : (0 : ℝ)≤(n : ℝ) := by nlinarith
    exact_mod_cast hh
  · have hh : (n : ℝ)≤ cap/mesh := by
      apply (le_div_iff₀ hm).mpr
      have hlt : max 0 (mesh*(n : ℝ))<cap := lt_of_not_ge hc
      have : mesh*(n : ℝ)≤ max 0 (mesh*(n : ℝ)) := le_max_right _ _
      nlinarith
    exact_mod_cast hh.trans (Int.le_ceil _)

end SevenEighths.HeckePrimeAmplitudeBins

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
variable {A : Type*} [CommRing A]

def scaledResidue (d a m : A) (hm : m = d * a) :
    (A ⧸ Ideal.span {d}) → (A ⧸ Ideal.span {m}) := fun x =>
  Quotient.liftOn' x (fun z => Ideal.Quotient.mk (Ideal.span {m}) (a * z)) (by
    intro x y hxy
    apply Ideal.Quotient.eq.mpr
    have hd : d ∣ x - y := Ideal.mem_span_singleton.mp
      ((Ideal.span {d}).quotientRel_def.mp hxy)
    apply Ideal.mem_span_singleton.mpr
    obtain ⟨z, hz⟩ := hd
    refine ⟨z, ?_⟩
    rw [hm, ← mul_sub, hz]
    ring)

@[simp] theorem scaledResidue_mk (d a m : A) (hm : m = d * a) (x : A) :
    scaledResidue d a m hm (Ideal.Quotient.mk (Ideal.span {d}) x) =
      Ideal.Quotient.mk (Ideal.span {m}) (a * x) := rfl

def fullModulusCorrelation (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ) (j : A) : ℂ :=
  fullCorrelation (scaledResidue u v (u * v) rfl)
    (scaledResidue v u (u * v) (mul_comm u v)) χu χv
    (Ideal.Quotient.mk (Ideal.span {u * v}) j)

theorem scaledResidue_congruence (u v x y j : A) :
    scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) x) -
      scaledResidue v u (u * v) (mul_comm u v)
        (Ideal.Quotient.mk (Ideal.span {v}) y) =
      Ideal.Quotient.mk (Ideal.span {u * v}) j ↔
      u * v ∣ v * x - u * y - j := by
  rw [scaledResidue_mk, scaledResidue_mk, ← map_sub, Ideal.Quotient.eq]
  exact Ideal.mem_span_singleton

variable [IsDomain A]

theorem scaledResidue_injective (d a m : A) (hm : m = d * a) (ha : a ≠ 0) :
    Function.Injective (scaledResidue d a m hm) := by
  intro x y
  refine Quotient.inductionOn₂' x y ?_
  intro r s hrs
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hrs)
  change m ∣ a * r - a * s at hd
  rw [hm, ← mul_sub, mul_comm d a] at hd
  exact (mul_dvd_mul_iff_left ha).mp hd

end SevenEighths.CenteredMomentCorrelation
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCommonSupport
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A]

abbrev Residue (d : A) := A ⧸ Ideal.span {d}

def principalCRT (d a : A) (h : IsCoprime d a) :
    Residue (d * a) ≃+* Residue d × Residue a :=
  (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton d a).symm).trans
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {d}) (Ideal.span {a})
      ((Ideal.isCoprime_span_singleton_iff d a).mpr h))

@[simp] theorem principalCRT_mk (d a : A) (h : IsCoprime d a) (x : A) :
    principalCRT d a h (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ x) := by
  ext <;> simp [principalCRT, Ideal.quotEquivOfEq_mk]

theorem isUnit_residue_of_coprime (d a : A) (h : IsCoprime d a) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {d}) a) := by
  obtain ⟨u, v, huv⟩ := h
  apply IsUnit.of_mul_eq_one (Ideal.Quotient.mk (Ideal.span {d}) v)
  have hd : Ideal.Quotient.mk (Ideal.span {d}) d = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton d))
  have hm := congrArg (Ideal.Quotient.mk (Ideal.span {d})) huv
  simpa only [map_add, map_mul, map_one, hd, mul_zero, zero_mul, zero_add, mul_comm] using hm

def residueUnit (d a : A) (h : IsCoprime d a) : (Residue d)ˣ :=
  (isUnit_residue_of_coprime d a h).unit

@[simp] theorem residueUnit_coe (d a : A) (h : IsCoprime d a) :
    (residueUnit d a h : Residue d) = Ideal.Quotient.mk _ a :=
  (isUnit_residue_of_coprime d a h).unit_spec

def scaledCommonCorrelation (D E a b : A)
    [Fintype (Residue D)] [Fintype (Residue E)]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ) (j : A) : ℂ :=
  fullCorrelation
    (fun x => scaledResidue D E (D * E) rfl (Ideal.Quotient.mk _ b * x))
    (fun y => scaledResidue E D (D * E) (mul_comm _ _) (Ideal.Quotient.mk _ a * y))
    χD χE (Ideal.Quotient.mk _ j)

end SevenEighths.CenteredMomentCommonSupport
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

def gaussValuationTable (Q G : ℂ) (r n j : ℕ) : ℂ :=
  if 6 ∣ r then (if n+1 ≤ j then Q^(n+1) else 0) - (if n ≤ j then Q^n else 0)
  else if j=n then Q^n*G else 0

end SevenEighths.ProbePrimePower
end

end OAI
end

section

namespace OAI

namespace SevenEighths.PNT.AnnularPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter MeasureTheory
open SevenEighths.IdealMangoldt SevenEighths.PNT.IdealPrimeMass
open scoped BigOperators Classical Topology ContDiff

noncomputable section

def cumulative (f : ℕ → ℝ) (t : ℝ) : ℝ := cumsum f (⌊t⌋₊ + 1)

def scaledCumulative (f : ℕ → ℝ) (x y : ℝ) : ℝ := cumulative f (x * y) / x

def annularSum (f : ℕ → ℝ) (φ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊x * a⌋₊ ⌊x * b⌋₊, f n * φ (n / x)

def annularPrimeIdeals (C : Set (Ideal O)) (a b x : ℝ) : Finset (Ideal O) :=
  (primeIdealsBelow C (⌊x * b⌋₊ + 1)).filter (fun P => ⌊x * a⌋₊ < Ideal.absNorm P)

@[simp] theorem mem_annularPrimeIdeals (C : Set (Ideal O)) (a b x : ℝ) (P : Ideal O) :
    P ∈ annularPrimeIdeals C a b x ↔
      P ∈ C ∧ Prime P ∧ ⌊x * a⌋₊ < Ideal.absNorm P ∧ Ideal.absNorm P ≤ ⌊x * b⌋₊ := by
  simp only [annularPrimeIdeals, Finset.mem_filter, mem_primeIdealsBelow, Nat.lt_succ_iff]
  tauto

def primeAnnularSum (C : Set (Ideal O)) (φ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ P ∈ annularPrimeIdeals C a b x, φ (Ideal.absNorm P / x)

def primeLogAnnularSum (C : Set (Ideal O)) (φ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P) * φ (Ideal.absNorm P / x)

def weightedPrimeAnnularSum (C : Set (Ideal O)) (W : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ P ∈ annularPrimeIdeals C a b x,
    W (Ideal.absNorm P / x) * (Ideal.absNorm P : ℝ) ^ (-5 / 6 : ℝ)

def primeWeightTerm (C : Set (Ideal O)) (W : ℝ → ℝ) (x : ℝ) (P : Ideal O) : ℝ :=
  if P ∈ C ∧ Prime P then W (Ideal.absNorm P / x) * (Ideal.absNorm P : ℝ) ^ (-5 / 6 : ℝ) else 0

def weightedPrimeSum (C : Set (Ideal O)) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ᶠ P : Ideal O, primeWeightTerm C W x P

def weightedPrimeSumDeleted (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ᶠ P : Ideal O, if P ∈ S then 0 else primeWeightTerm C W x P

end

end SevenEighths.PNT.AnnularPrimeMass

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev PrimeIdeal := {P : Id // Prime P}

def primeValuations (I : Id) : PrimeIdeal →₀ ℕ :=
  (factorization I).subtypeDomain Prime

def idealFromValuations (v : PrimeIdeal →₀ ℕ) : Id :=
  v.prod (fun P n=>P.val^n)

lemma idealFromValuations_ne_zero (v : PrimeIdeal →₀ ℕ) : idealFromValuations v≠0 := by
  unfold idealFromValuations Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr (fun P hP=>pow_ne_zero _ P.property.ne_zero)

@[simp] lemma primeValuations_apply (I : Id) (P : PrimeIdeal) :
    primeValuations I P=(normalizedFactors I).count P.val := by
  simp only [primeValuations,Finsupp.subtypeDomain_apply,factorization_eq_count]

@[simp] lemma primeValuations_one : primeValuations 1=0 := by
  simp only [primeValuations,factorization_one,Finsupp.subtypeDomain_zero]

lemma primeValuations_mul (I J : Id) (hI : I≠0) (hJ : J≠0) :
    primeValuations (I*J)=primeValuations I+primeValuations J := by
  simp only [primeValuations,factorization_mul hI hJ,Finsupp.subtypeDomain_add]

@[simp] lemma primeValuations_prime (P : PrimeIdeal) :
    primeValuations P.val=Finsupp.single P 1 := by
  ext Q
  simp only [primeValuations_apply,normalizedFactors_irreducible P.property.irreducible,
    normalize_eq,Multiset.count_singleton,Finsupp.single_apply]
  by_cases h : Q=P
  · subst Q
    simp
  · have hv : Q.val≠P.val := fun hh=>h (Subtype.ext hh)
    simp [Ne.symm h,hv]

lemma primeValuations_pow (I : Id) (n : ℕ) :
    primeValuations (I^n)=n • primeValuations I := by
  ext P
  simp only [primeValuations_apply,normalizedFactors_pow,Multiset.count_nsmul,
    Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]

@[simp] lemma idealFromValuations_zero : idealFromValuations 0=1 := by
  simp [idealFromValuations]

lemma idealFromValuations_add (v w : PrimeIdeal →₀ ℕ) :
    idealFromValuations (v+w)=idealFromValuations v*idealFromValuations w := by
  exact Finsupp.prod_add_index' (fun _=>pow_zero _) (fun _ _ _=>pow_add _ _ _)

@[simp] lemma idealFromValuations_single (P : PrimeIdeal) (n : ℕ) :
    idealFromValuations (Finsupp.single P n)=P.val^n := by
  simp [idealFromValuations]

@[simp] theorem primeValuations_idealFromValuations (v : PrimeIdeal →₀ ℕ) :
    primeValuations (idealFromValuations v)=v := by
  induction v using Finsupp.induction with
  | zero => simp only [idealFromValuations_zero,primeValuations_one]
  | @single_add P n v hP hn ih =>
    rw [idealFromValuations_add,primeValuations_mul _ _
      (idealFromValuations_ne_zero _) (idealFromValuations_ne_zero _),ih]
    simp only [idealFromValuations_single,primeValuations_pow,primeValuations_prime,
      Finsupp.smul_single,smul_eq_mul,mul_one]

@[simp] theorem idealFromValuations_primeValuations (I : Id) (hI : I≠0) :
    idealFromValuations (primeValuations I)=I := by
  have hs : ∀ P∈(factorization I).support,Prime P := by
    intro P hP
    exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp (by simpa using hP))
  unfold idealFromValuations primeValuations
  rw [Finsupp.prod_subtypeDomain_index hs]
  simp only [Finsupp.prod,support_factorization,factorization_eq_count]
  rw [← Finset.prod_multiset_count_of_subset _ _ (Finset.Subset.refl _)]
  exact Ideal.prod_normalizedFactors_eq_self hI

def nonzeroIdealValuationEquiv : {I : Id // I≠0} ≃ (PrimeIdeal →₀ ℕ) where
  toFun I := primeValuations I.val
  invFun v := ⟨idealFromValuations v,idealFromValuations_ne_zero v⟩
  left_inv I := Subtype.ext (idealFromValuations_primeValuations I.val I.property)
  right_inv := primeValuations_idealFromValuations

lemma primeIdeal_coprime (P Q : PrimeIdeal) (h : P≠Q) : IsCoprime P.val Q.val := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : Q.val.IsPrime := Ideal.isPrime_of_prime Q.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  let : Q.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance Q.property.ne_zero
  exact Ideal.isCoprime_of_isMaximal (fun hh=>h (Subtype.ext hh))

def finsuppPairEquiv {α β γ : Type*} [Zero β] [Zero γ] :
    ((α→₀β)×(α→₀γ)) ≃ (α→₀(β×γ)) where
  toFun v := Finsupp.zipWith Prod.mk rfl v.1 v.2
  invFun v := (v.mapRange Prod.fst rfl,v.mapRange Prod.snd rfl)
  left_inv v := by
    apply Prod.ext <;> ext a <;> rfl
  right_inv v := by
    apply Finsupp.ext
    intro a
    exact Prod.eta (v a)

abbrev HighValuation := (ℕ×ℕ)×(ℕ×ℕ)
abbrev NonzeroIdeal := {I : Id // I≠0}

def highValuationEquiv : ((NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal)) ≃
    (PrimeIdeal→₀HighValuation) :=
  (Equiv.prodCongr
    (Equiv.prodCongr nonzeroIdealValuationEquiv nonzeroIdealValuationEquiv)
    (Equiv.prodCongr nonzeroIdealValuationEquiv nonzeroIdealValuationEquiv)).trans
      ((Equiv.prodCongr finsuppPairEquiv finsuppPairEquiv).trans finsuppPairEquiv)

@[simp] lemma highValuationEquiv_apply
    (a : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal)) (P : PrimeIdeal) :
    highValuationEquiv a P =
      ((primeValuations a.1.1.val P,primeValuations a.1.2.val P),
        (primeValuations a.2.1.val P,primeValuations a.2.2.val P)) := rfl

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]

def zeroIndexTerm (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) (k m : ℕ) : ℂ :=
  (if k=0 then 1 else (χ^k) (Ideal.Quotient.mk _ (p^(6*m)))) * W^k * V^m

def zeroIndexSeries (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) : ℂ :=
  ∑' k, ∑' m, zeroIndexTerm p χ W V k m

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma outside_mul (S : Finset Id) (hS : ∀P∈S,Prime P) (A B : Id) :
    (∀P∈S,¬P∣A*B) ↔ (∀P∈S,¬P∣A) ∧ (∀P∈S,¬P∣B) := by
  constructor
  · intro h
    constructor
    · intro P hP hd
      exact h P hP ((hS P hP).dvd_mul.mpr (Or.inl hd))
    · intro P hP hd
      exact h P hP ((hS P hP).dvd_mul.mpr (Or.inr hd))
  · rintro ⟨hA,hB⟩ P hP hd
    exact ((hS P hP).dvd_mul.mp hd).elim (hA P hP) (hB P hP)

def highExclusion (S : Finset Id) (hS : ∀P∈S,Prime P) : Id→*ℂ where
  toFun A := if ∀P∈S,¬P∣A then 1 else 0
  map_one' := by
    rw [if_pos]
    intro P hP hd
    exact (hS P hP).not_isUnit (isUnit_of_dvd_one hd)
  map_mul' A B := by
    simp only [outside_mul S hS A B]
    split_ifs <;> simp_all

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def completedValuationMark (_P : PrimeIdeal) (b : HighValuation) : ℂ :=
  if b.1.1+3*b.1.2≠0 then 1 else 0

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

def smallPrimeSet (N : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le N).toFinset.filter Prime

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace SevenEighths.ProbePrincipalResidueActual
open HeckeFamily
open ProbeEuler ProbePhysical
open ActualEisensteinCubic

def residueWeights {κ : Type*} (W : κ → ℝ → ℝ) (scale : κ → ℝ)
    (j : κ) (p : PrimeIdeal) : ℝ :=
  W j ((Ideal.absNorm p.val : ℝ)/scale j) * (Ideal.absNorm p.val : ℝ)^(-(5/6 : ℝ))

end SevenEighths.ProbePrincipalResidueActual
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawRadial
open HeckeFamily
open ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O

theorem exists_raw_radial_majorant :
    ∃Φ : 𝓢(ℝ,ℂ),HasCompactSupport (Φ:ℝ→ℂ) ∧
      (∀x,0≤(Φ x).re) ∧ (∀x∈Set.Icc (0:ℝ) 1,Φ x=1) := by
  have hsub : Set.Icc (0:ℝ) 1⊆Set.Ioo (-1) 2 := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v : ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv : ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by simpa using hf : ContDiff ℝ ∞ f).pow 2)
  have hsupp : Function.support v⊆Set.Icc (-1) 2 := by
    intro x hx
    have hn : x∈Function.support f := by
      intro hz
      exact hx (by simp [v,hz])
    rw [hs] at hn
    exact ⟨hn.1.le,hn.2.le⟩
  have hvc:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,?_⟩
  · intro x
    change 0≤(f x)^2
    positivity
  · intro x hx
    change (((f x)^2:ℝ):ℂ)=1
    rw [(hone x).mp hx]
    norm_num

end SevenEighths.DetectorDictionaryInverseRawRadial

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseMarkedPadding
open HeckeFamily
open ConcreteTraceCRT ActualEisensteinCubic
local notation "O" => HeckeFamily.O

def radialMajorant : 𝓢(ℝ,ℂ) :=
  Classical.choose DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant

variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

end SevenEighths.DetectorDictionaryInverseMarkedPadding

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

abbrev Tuple (L:ι→Finset (Ideal O)) := ∀i,↥(L i)
abbrev Assigned (L:ι→Finset (Ideal O))(J:Finset ι) := ∀i:↥J,↥(L i.val)
abbrev Remaining (L:ι→Finset (Ideal O))(J:Finset ι) := ∀i:{i:ι // i∉J},↥(L i.val)

def joinTuple (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)(y:Remaining L J) : Tuple L :=
  (Equiv.piEquivPiSubtypeProd (fun i=>i∈J) (fun i=>↥(L i))).symm (x,y)

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def assignedIdeal (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J) : Ideal O :=
  ∏i:↥J,(x i).val

def remainingIdeal (L:ι→Finset (Ideal O))(J:Finset ι)(y:Remaining L J) : Ideal O :=
  ∏i:{i:ι // i∉J},(y i).val

omit [Fintype ι] in
@[simp] theorem joinTuple_assigned (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(i:↥J) : joinTuple L J x y i.val=x i := by
  simp [joinTuple,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

omit [Fintype ι] in
@[simp] theorem joinTuple_remaining (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(i:{i:ι // i∉J}) : joinTuple L J x y i.val=y i := by
  simp [joinTuple,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic
namespace SevenEighths.InverseInitialCommonRatios
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def survivingProduct (I:Finset σ)(q:∀i∈I,Ideal Eis) : Ideal Eis :=
  ∏i∈I.attach,q i.val i.property

end SevenEighths.InverseInitialCommonRatios

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapFourier
open InverseMoment
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def density (g : 𝓢(ℝ,ℂ)) (xj t : ℝ) : ℂ := (𝓕 g) t*logPhase t xj

end SevenEighths.InverseInitialOverlapFourier

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic
namespace SevenEighths.InverseInitialOverlapIdealFourier
open InverseMoment InverseInitialOverlapFourier
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def activeIndices (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (c : Ideal Eis) : Finset ι := (I.biUnion L).filter (fun p=>primes p∣c)

end SevenEighths.InverseInitialOverlapIdealFourier

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic
namespace SevenEighths.InverseInitialCommonProfile
open InverseMoment InverseInitialCommonRatios
open InverseInitialOverlapFourier InverseInitialOverlapIdealFourier
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def slotRatio (Z:ℝ)(ell:σ→ℝ)(i:σ)(P:Ideal Eis) : ℝ := (P.absNorm:ℝ)/Z^(ell i)

end SevenEighths.InverseInitialCommonProfile

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
namespace SevenEighths.InverseInitialCommonCutoff
open InverseMoment InverseInitialCommonProfile InverseInitialCommonRatios
open InverseInitialOverlapIdealFourier
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def tupleProfile (I:Finset σ)(L:σ→Finset (Ideal Eis))(a:σ→Ideal Eis→ℂ)
    (Z:ℝ)(ell:σ→ℝ)(W:ℝ→ℂ)(yj yc:ℝ)(c:Ideal Eis) : ℂ :=
  ∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
    (if survivingProduct I q∣c then
      W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) else 0)

end SevenEighths.InverseInitialCommonCutoff

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedPool
local notation "O"=>ActualEisensteinCubic.O

def outside (E:Finset (Ideal O))(I:Ideal O):Prop:=∀P∈E,¬P∣I

def originalOutside (A E:Finset (Ideal O)):Finset (Ideal O):=A.filter (outside E)

end SevenEighths.InverseInitialExcludedPool

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter
namespace SevenEighths.CenteredMomentRankin
local notation "O" => ActualEisensteinCubic.O

def primeMass (P : Ideal O) (δ : ℝ) : ℝ := ((Ideal.absNorm P:ℝ)^δ-1)⁻¹

end SevenEighths.CenteredMomentRankin

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinCount
open UniqueFactorizationMonoid CenteredMomentRankin
local notation "O" => ActualEisensteinCubic.O

def powerCode (R : Finset (Ideal O)) (I : Ideal O) (P : R) : ℕ :=
  (normalizedFactors I).count (P:Ideal O)-1

end SevenEighths.CenteredMomentRankinCount

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentHeckeWindowEnergy
open HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

def heightCost (t θ : ℝ) : ℝ := (1+‖t‖+2*Real.pi*‖θ‖)*(1+2*Real.pi)

end SevenEighths.CenteredMomentHeckeWindowEnergy

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialExcludedPeriod
open ActualEisensteinCubic
open UniqueFactorizationMonoid HeckeFamily
local notation "O" => ActualEisensteinCubic.O

def deletedPeriod (q:ℕ):ℕ := 2592*q^2

end SevenEighths.InverseInitialExcludedPeriod

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentPartitionNorm
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def commonIdeal (p : ι → O) (c d : ι → ℕ) : Ideal O :=
  ∏ i, Ideal.span {p i} ^ min (c i) (d i)

def unitIdeal (p : ι → O) (U : Finset ι) : Ideal O := ∏ i ∈ U, Ideal.span {p i}

end SevenEighths.CenteredMomentPartitionNorm

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentForcing
open UniqueFactorizationMonoid CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def movingIdeal (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  (∏ i, P i ^ min (c i) (d i)) * ∏ i ∈ V, P i

def forcingSet (c d : ι → ℕ) (V : Finset ι) : Finset ι :=
  V.filter (fun i => c i = 1 ∧ d i = 1)

def forcingIdeal (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  ∏ i ∈ forcingSet c d V, P i

def movingElement (p : ι → O) (c d : ι → ℕ) (V : Finset ι) : O :=
  (∏ i, p i ^ min (c i) (d i)) * ∏ i ∈ V, p i

end SevenEighths.CenteredMomentForcing

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentLiveSupport
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentLiveSupport

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNonprincipalGate
open HeckeFamily
local notation "O" => HeckeFamily.O

def unitCharacter : Character := Character.ofResidue ⊤ top_ne_bot 1 (by
  intro u
  exact MulChar.one_apply (IsUnit.map (Ideal.Quotient.mk ⊤) u.isUnit))

end SevenEighths.CenteredMomentNonprincipalGate

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialCommonRatios
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def remainingIndexEquiv (J:Finset ι) : {i:ι // i∉J} ≃ ↥(Finset.univ\J) where
  toFun i:=⟨i.val,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩⟩
  invFun i:=⟨i.val,(Finset.mem_sdiff.mp i.property).2⟩
  left_inv _:=rfl
  right_inv _:=rfl

def remainingPi (L:ι→Finset (Ideal O))(J:Finset ι)(q:Remaining L J) :
    ∀i∈Finset.univ\J,Ideal O := fun i hi=>(q ⟨i,(Finset.mem_sdiff.mp hi).2⟩).val

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialCommonRatios InverseInitialExcludedPool
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def remainingFromPi (L:ι→Finset (Ideal O))(J:Finset ι)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) : Remaining L J :=
  fun i=>⟨t i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩),
    Finset.mem_pi.mp ht i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩)⟩

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.DetectorDictionaryInverseAssignedCount
local notation "O" => ActualEisensteinCubic.O

def assignedTuples {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) : Finset (ι → Ideal O) := Fintype.piFinset L

@[simp] theorem mem_assignedTuples {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (q : ι → Ideal O) :
    q ∈ assignedTuples L ↔ ∀ i, q i ∈ L i := by
  simp [assignedTuples]

def assignedConstant (K : ℕ) (b : ℝ) : ℝ := (128*b)^K

def assignedCoefficient {ι : Type*} [Fintype ι]
    (a : ι → Ideal O → ℂ) (q : ι → Ideal O) : ℂ := ∏ i, a i (q i)

end SevenEighths.DetectorDictionaryInverseAssignedCount

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDescentLedger
open CenteredMomentPartitionNorm
local notation "O" => ActualEisensteinCubic.O

def firstSaving (c D₀ w q wo B g ell : ℝ) : ℝ :=
  c/6+5*D₀/6+w/3+q/6+wo+B-5*g/6+ell

end SevenEighths.CenteredMomentDescentLedger

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.CenteredMomentDyadicCount

def indices (a b : ℝ) : Finset ℤ :=
  Finset.Icc ⌈Real.logb 2 a⌉ ⌊Real.logb 2 (4*b)⌋

end SevenEighths.CenteredMomentDyadicCount

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def physicalCaps (b Z D T:ℝ) : Fin 4→ℝ := ![b*Z^D,b*Z^D,b*Z^D,T]

variable (hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicTailBound
open ActualEisensteinCubic ConcreteTraceCRT SecondPassArithmetic
open InverseInitialDyadicAssembly
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def idealIndex : Fin 5→Fin 6 := ![0,1,2,4,5]

end SevenEighths.InverseInitialDyadicTailBound

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O)
  (hp : Prime p)
  [(Ideal.span {p}:Ideal O).IsMaximal]

def rowZeroIndexTerm (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) (j k m : ℕ) : ℂ :=
  (if k=0 then 1 else (χ^k) (Ideal.Quotient.mk _ (p^(j+6*m))))*W^k*V^m

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbePhysical ProbeEuler
local notation "O" => HeckeFamily.O

def firstPrimeDefectBound (eps : ℝ) (P : PrimeIdeal) : ℝ :=
  240*(P.val.absNorm : ℝ)^(-1-min eps (1/50:ℝ))

structure FirstTail (eps : ℝ) (S : Finset (Ideal O)) : Prop where
  positive : 0<eps
  norm_four : ∀P : PrimeIdeal,P.val∉S → 4≤P.val.absNorm
  small : (∑' P : {P : PrimeIdeal // P.val∉S},firstPrimeDefectBound eps P.val)≤1/6

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbePhysical
local notation "O" => HeckeFamily.O

def markExclusions (S : Finset (Ideal O)) (T : Finset PrimeIdeal) : Finset (Ideal O) :=
  S∪T.image Subtype.val

theorem markExclusions_prime (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) : ∀P∈markExclusions S T,Prime P := by
  intro P hP
  rcases Finset.mem_union.mp hP with hP|hP
  · exact hS P hP
  · obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    exact Q.property

@[simp] theorem mem_markExclusions (S : Finset (Ideal O)) (T : Finset PrimeIdeal) (P : PrimeIdeal) :
    P.val∈markExclusions S T ↔ P.val∈S ∨ P∈T := by
  simp only [markExclusions,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro (h|⟨Q,hQ,he⟩)
    · exact Or.inl h
    · exact Or.inr ((Subtype.ext he : Q=P) ▸ hQ)
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr ⟨P,h,rfl⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeSelectedPrimeSums
local notation "O" => ActualEisensteinCubic.O

def annularPower (a b r : ℝ) : ℝ := max (a^r) (b^r)

end SevenEighths.ProbeSelectedPrimeSums
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbePhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def coarsePrimeCost (T : Finset PrimeIdeal) : ℝ := ∏P∈T,(8192:ℝ)*(P.val.absNorm:ℝ)^3

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical

def gaussianMellinProfile (y : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
    Complex.exp (-(Complex.log (y:ℂ))^2/4)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianCompletedProfile (y : ℝ) : ℂ := gaussianMellinProfile y/(Real.sqrt y:ℂ)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
namespace SevenEighths.ProbePhysical
open DyadicTransfer

def gaussianCutoff (y : ℝ) : ℂ := (Real.smoothTransition (2-y):ℂ)
def gaussianAnnulus (y : ℝ) : ℂ := annularCutoff gaussianCutoff y

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]
abbrev ResidueQ (a : A) := A⧸Ideal.span {a}

def condition (C n₁ n₂ k : A) (p : ResidueQ (C*n₁) × ResidueQ (C*n₂)) : Prop :=
  scaledResidue (C*n₁) (C*n₂) ((C*n₁)*(C*n₂)) rfl p.1-
    scaledResidue (C*n₂) (C*n₁) ((C*n₁)*(C*n₂)) (mul_comm _ _) p.2=
    Ideal.Quotient.mk (Ideal.span {(C*n₁)*(C*n₂)}) (C*k)

abbrev Solutions (C n₁ n₂ k : A) := {p : ResidueQ (C*n₁) × ResidueQ (C*n₂) // condition C n₁ n₂ k p}

def leftParam (C n₁ b k : A) (t : ResidueQ C) : ResidueQ (C*n₁) :=
  Ideal.Quotient.mk _ (b*k)+scaledResidue C n₁ (C*n₁) rfl t

def rightParam (C n₂ a k : A) (t : ResidueQ C) : ResidueQ (C*n₂) :=
  Ideal.Quotient.mk _ (-a*k)+scaledResidue C n₂ (C*n₂) rfl t

omit [IsDomain A] in
@[simp] lemma leftParam_mk (C n₁ b k t : A) :
    leftParam C n₁ b k (Ideal.Quotient.mk _ t)=Ideal.Quotient.mk _ (b*k+n₁*t) := by
  simp only [leftParam,scaledResidue_mk,map_add]

omit [IsDomain A] in
@[simp] lemma rightParam_mk (C n₂ a k t : A) :
    rightParam C n₂ a k (Ideal.Quotient.mk _ t)=Ideal.Quotient.mk _ (-a*k+n₂*t) := by
  simp only [rightParam,scaledResidue_mk,map_add]

omit [IsDomain A] in
lemma param_condition (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (t : ResidueQ C) :
    condition C n₁ n₂ k (leftParam C n₁ b k t,rightParam C n₂ a k t) := by
  obtain ⟨t,rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [leftParam_mk,rightParam_mk]
  unfold condition
  rw [scaledResidue_congruence]
  have he : C*n₂*(b*k+n₁*t)-C*n₁*(-a*k+n₂*t)-C*k=C*k*(a*n₁+b*n₂-1) := by ring
  rw [he,hab,sub_self,mul_zero]
  exact dvd_zero _

def param (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (t : ResidueQ C) : Solutions C n₁ n₂ k :=
  ⟨(leftParam C n₁ b k t,rightParam C n₂ a k t),param_condition C n₁ n₂ a b k hab t⟩

lemma param_injective (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (hn₁ : n₁≠0) :
    Function.Injective (param C n₁ n₂ a b k hab) := by
  intro t u he
  have hl : leftParam C n₁ b k t=leftParam C n₁ b k u := congrArg (fun p=>p.val.1) he
  apply scaledResidue_injective C n₁ (C*n₁) rfl hn₁
  exact add_left_cancel hl

lemma condition_divided (C n₁ n₂ k x y : A) (hC : C≠0)
    (hc : condition C n₁ n₂ k (Ideal.Quotient.mk _ x,Ideal.Quotient.mk _ y)) :
    C*n₁*n₂∣n₂*x-n₁*y-k := by
  unfold condition at hc
  rw [scaledResidue_congruence] at hc
  have hh : C*(C*n₁*n₂)∣C*(n₂*x-n₁*y-k) := by convert (preTransparency := .instances) hc using 1 <;> ring
  exact (mul_dvd_mul_iff_left hC).mp hh

lemma param_surjective (C n₁ n₂ a b k : A) (hC : C≠0) (hab : a*n₁+b*n₂=1) :
    Function.Surjective (param C n₁ n₂ a b k hab) := by
  intro p
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective p.val.1
  obtain ⟨y,hy⟩ := Ideal.Quotient.mk_surjective p.val.2
  have hc : condition C n₁ n₂ k (Ideal.Quotient.mk _ x,Ideal.Quotient.mk _ y) := by
    rw [hx,hy]
    exact p.property
  have hd := condition_divided C n₁ n₂ k x y hC hc
  refine ⟨Ideal.Quotient.mk _ (a*x+b*y),?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change leftParam C n₁ b k (Ideal.Quotient.mk _ (a*x+b*y))=p.val.1
    rw [leftParam_mk,←hx,Ideal.Quotient.eq]
    apply Ideal.mem_span_singleton.mpr
    have hh : C*n₁∣n₂*x-n₁*y-k := (dvd_mul_right (C*n₁) n₂).trans hd
    have he : b*k+n₁*(a*x+b*y)-x= -b*(n₂*x-n₁*y-k) := by
      linear_combination x*hab
    rw [he]
    exact dvd_mul_of_dvd_right hh _
  · change rightParam C n₂ a k (Ideal.Quotient.mk _ (a*x+b*y))=p.val.2
    rw [rightParam_mk,←hy,Ideal.Quotient.eq]
    apply Ideal.mem_span_singleton.mpr
    have hh : C*n₂∣n₂*x-n₁*y-k := by
      apply dvd_trans _ hd
      exact ⟨n₁,by ring⟩
    have he : -a*k+n₂*(a*x+b*y)-y=a*(n₂*x-n₁*y-k) := by
      linear_combination y*hab
    rw [he]
    exact dvd_mul_of_dvd_right hh _

def solutionEquiv (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1) : ResidueQ C≃Solutions C n₁ n₂ k :=
  Equiv.ofBijective (param C n₁ n₂ a b k hab)
    ⟨param_injective C n₁ n₂ a b k hab hn₁,param_surjective C n₁ n₂ a b k hC hab⟩

@[simp] lemma solutionEquiv_val (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1) (t : ResidueQ C) :
    (solutionEquiv C n₁ n₂ a b k hC hn₁ hab t).val=(leftParam C n₁ b k t,rightParam C n₂ a k t) := rfl

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

def lowOuterCutoff (a b x : ℝ) : ℂ :=
  (Real.smoothTransition (2*x/a-1):ℂ)*(Real.smoothTransition (2-x/b):ℂ)

lemma lowOuterCutoff_small (a b : ℝ) (ha : 0<a) (x : ℝ) (hx : x≤a/2) :
    lowOuterCutoff a b x=0 := by
  have h : 2*x/a-1≤0 := by
    have hh : 2*x/a≤1 := (div_le_iff₀ ha).mpr (by linarith)
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.zero_of_nonpos h,Complex.ofReal_zero,zero_mul]

lemma lowOuterCutoff_large (a b : ℝ) (hb : 0<b) (x : ℝ) (hx : 2*b≤x) :
    lowOuterCutoff a b x=0 := by
  have h : 2-x/b≤0 := by
    have hh : 2≤x/b := (le_div_iff₀ hb).mpr hx
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.zero_of_nonpos h,Complex.ofReal_zero,mul_zero]

lemma lowOuterCutoff_smooth (a b : ℝ) : ContDiff ℝ ∞ (lowOuterCutoff a b) := by
  unfold lowOuterCutoff
  exact (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))).mul
    (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop)))

lemma lowOuterCutoff_support (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    Function.support (lowOuterCutoff a b)⊆Set.Icc (a/2) (2*b) := by
  intro x hx
  constructor
  · by_contra hh
    exact hx (lowOuterCutoff_small a b ha x (le_of_lt (lt_of_not_ge hh)))
  · by_contra hh
    exact hx (lowOuterCutoff_large a b hb x (le_of_lt (lt_of_not_ge hh)))

lemma lowOuterCutoff_compact (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    HasCompactSupport (lowOuterCutoff a b) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (lowOuterCutoff_support a b ha hb)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramRemainders (F : Finset O) : Finset Id :=
  F.image (fun z=>sixthRemainder (Ideal.span {z}))

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.ProbeGramFrequencySummation
local notation "O" => ActualEisensteinCubic.O

def frequencyNorm (k : O) : ℝ := Ideal.absNorm (Ideal.span {k})

end SevenEighths.ProbeGramFrequencySummation

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowPrimeIdealList (T : Finset PrimeIdeal) : Finset Id := T.image Subtype.val

def lowPrimeListEquiv (T : Finset PrimeIdeal) : T≃lowPrimeIdealList T :=
  Equiv.ofBijective (fun p=>⟨p.val.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩) (by
    constructor
    · intro p q h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : lowPrimeIdealList T=>x.val) h))
    · intro I
      obtain ⟨P,hP,h⟩ := Finset.mem_image.mp I.property
      exact ⟨⟨P,hP⟩,Subtype.ext h⟩)

@[simp] lemma lowPrimeListEquiv_val (T : Finset PrimeIdeal) (p : T) :
    (lowPrimeListEquiv T p).val=p.val.val := rfl

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def actualPuncturePrimes (lists : σ→Finset (Ideal Eis)) (m : Eis) : Finset (Ideal Eis) :=
  (Finset.univ.biUnion lists).filter (fun P => m∈P)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowRemote (Z ell ε T : ℝ) : Prop :=
  T/Z^(1+ell)≤(Z^(ε/2))⁻¹ ∨ Z^(ε/2)≤T/Z^(1+ell)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalRemainderBounds
open HeckeFamily ProbePhysical ProbeEuler
local notation "Id" => Ideal ActualEisensteinCubic.O

def slotConstant {ι : Type*} (J : Finset ι) (c d B ξ : ℝ) : ℝ :=
  (3/2)*∏_j∈J,(1+1440*(480:ℝ)^(-(7/8:ℝ)))*(128*d*B*c^(ξ-1))

def scalePower (X Y Z a ξ υ : ℝ) : ℝ :=
  X^(1/2-ξ)*Z^(a+ξ-1)*Y^(υ-1)

end SevenEighths.ProbePrincipalRemainderBounds

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology SchwartzMap ContDiff
namespace SevenEighths.ProbeDetectorInverseMarkedField
open HeckeFamily InverseMoment
open ProbeHighRowFamily Filter
open DetectorDictionaryInverseMarkedReference
local notation "O"=>HeckeFamily.O

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

end SevenEighths.ProbeDetectorInverseMarkedField

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedProfileMeasure
open HeckeFamily FourierBridge
local notation "O" => HeckeFamily.O

def logWindow (V : ℝ→ℂ) (x : ℝ) : ℂ := if 0<x then V (Real.log x) else 0

end SevenEighths.CenteredMomentReflectedProfileMeasure

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawRealRadial
open ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

theorem exists_real_raw_radial_majorant:
    ∃Φ:𝓢(ℝ,ℂ),HasCompactSupport (Φ:ℝ→ℂ) ∧
      (∀x,0≤(Φ x).re) ∧ (∀x,(Φ x).im=0) ∧
      (∀x∈Set.Icc (0:ℝ) 1,Φ x=1):=by
  have hsub:Set.Icc (0:ℝ) 1⊆Set.Ioo (-1) 2:=by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v:ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv:ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by simpa using hf:ContDiff ℝ ∞ f).pow 2)
  have hsupp:Function.support v⊆Set.Icc (-1) 2:=by
    intro x hx
    have hn:x∈Function.support f:=by
      intro hz
      exact hx (by simp [v,hz])
    rw [hs] at hn
    exact ⟨hn.1.le,hn.2.le⟩
  have hvc:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,?_,?_⟩
  · intro x
    change 0≤(f x)^2
    positivity
  · intro x
    exact Complex.ofReal_im _
  · intro x hx
    change (((f x)^2:ℝ):ℂ)=1
    rw [(hone x).mp hx]
    norm_num

end SevenEighths.DetectorDictionaryInverseRawRealRadial

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.ProbeDetectorInverseRawField
open HeckeFamily InverseMoment
open ProbeHighRowFamily

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

end SevenEighths.ProbeDetectorInverseRawField

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentWholeDivisorShell
open UniqueFactorizationMonoid
open CenteredMomentDyadicCount
local notation "O" => ActualEisensteinCubic.O

def live (Ds : Finset (Ideal O)) : Finset (Ideal O) := Ds.filter (fun D=>(moebius D:ℂ)≠0)

def normKey (D : Ideal O) : ℤ := ⌊Real.logb 2 (D.absNorm:ℝ)⌋
def shell (Ds : Finset (Ideal O)) (n : ℤ) : Finset (Ideal O) := (live Ds).filter (fun D=>normKey D=n)
def selectedShells (Ds : Finset (Ideal O)) : Finset ℤ := (live Ds).image normKey

end SevenEighths.CenteredMomentWholeDivisorShell

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

def logWindow (a b : ℝ) : ℝ := max |Real.log a| |Real.log b|

variable {ι : Type*} [DecidableEq ι]

end SevenEighths.CenteredMomentSlotRatios

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedDomain
open CenteredMomentLiveSupport
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentRestrictedDomain

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedSourceNormalization
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentRestrictedSourceNormalization

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstWholeKernel
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O

def windows (V : Fin 4 → ℝ → ℂ) (K H A B K₀ H₀ A₀ B₀ : ℝ) : ℂ :=
  V 0 (Real.log (K/K₀))*V 1 (Real.log (H/H₀))*
    V 2 (Real.log (A/A₀))*V 3 (Real.log (B/B₀))

end SevenEighths.CenteredMomentFirstWholeKernel

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondWholeKernel
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstWholeKernel
local notation "O" => ActualEisensteinCubic.O

def secondEffectiveScale (C D : Ideal O) (A : O) (K : ℝ) : ℝ :=
  K*‖eisEmbedding A‖^2/((Ideal.absNorm C:ℝ)*(Ideal.absNorm D:ℝ))

end SevenEighths.CenteredMomentSecondWholeKernel

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondDyadicPartition
open HeckeFamily ConcreteTraceCRT
open CenteredMomentSecondWholeKernel CenteredMomentFirstWholeKernel
open CenteredMomentDyadicCount
local notation "O" => ActualEisensteinCubic.O

abbrev Blocks (a b : Fin 4→ℝ) := ∀ i : Fin 4,↥(indices (a i) (b i))

end SevenEighths.CenteredMomentSecondDyadicPartition

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSourceSupport
open ActualEisensteinCubic ConcreteTraceCRT
open HeckeFamily
open CenteredMomentFirstWholeKernel
local notation "O"=>ActualEisensteinCubic.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

end SevenEighths.CenteredMomentFirstPhysicalSourceSupport

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationActiveFactor
local notation "O" => ActualEisensteinCubic.O

def errorMovingExponent (n : ℕ) : ℕ := if n=5 then 0 else 1

end SevenEighths.CenteredMomentAmplificationActiveFactor

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationLiveEnergy
open CenteredMomentLiveSupport
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentAmplificationLiveEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationChildEnergy
open CenteredMomentAmplificationLiveEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentAmplificationChildEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationErrorEnergy
local notation "O" => ActualEisensteinCubic.O

def localErrorCost (p : O) (n : ℕ) : ℝ :=
  if n=5 then (1-(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹)^2
  else (Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹

end SevenEighths.CenteredMomentAmplificationErrorEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationOriginalErrors
open HeckeFamily
open CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationChildEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentAmplificationOriginalErrors

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentAmplificationEligibility
local notation "O" => ActualEisensteinCubic.O

def exclusionIdeal (R s : Ideal O) (h : O) : Ideal O := R*s*Ideal.span {h}

def eligible (R s : Ideal O) (h p : O) : Prop := ¬Ideal.span {p}∣exclusionIdeal R s h

end SevenEighths.CenteredMomentAmplificationEligibility

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentAmplificationRadicalFamily
open HeckeFamily
open CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationChildEnergy
open CenteredMomentAmplificationEligibility
local notation "O"=>ActualEisensteinCubic.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def radicalBound (η:Character)(m p:O)(k:ℕ):ℕ :=
  η.modulus.absNorm*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*
    (if k=0 then 1 else (Ideal.span {p}).absNorm)

end SevenEighths.CenteredMomentAmplificationRadicalFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentOriginalRadialComparison
open HeckeFamily ConcreteTraceCRT
local notation "O" => HeckeFamily.O

def radialEnergy (F : O→ℂ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑'z:O,if keep z then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0

end SevenEighths.CenteredMomentOriginalRadialComparison

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

universe u
namespace SevenEighths.CenteredMomentEnergyFirstAnnularAdmission
open HeckeFamily ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def amplifierCap (A D ξcap:ℝ):ℝ:=3*max A D+ξcap/2+1

end SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLiveHeight
open HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentCommonLiveHeight

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFixedQForcingCount
open HeckeFamily
open CenteredMomentForcing
open UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def goodSet (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Finset ι :=
  (forcingSet c d V).filter (fun i => IsCoprime Q (P i))

def excludedSet (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Finset ι :=
  (forcingSet c d V).filter (fun i => ¬IsCoprime Q (P i))

def goodIdeal (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  ∏ i ∈ goodSet Q P c d V, P i

def excludedIdeal (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  ∏ i ∈ excludedSet Q P c d V, P i

end SevenEighths.CenteredMomentFixedQForcingCount

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondFrozenSupported
open HeckeFamily ConcreteTraceCRT
open Filter
local notation "O" => ActualEisensteinCubic.O

variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentSecondFrozenSupported

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondFrozenPhysical
open HeckeFamily ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

open Filter
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondWholeKernel

end SevenEighths.CenteredMomentSecondFrozenPhysical

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondFrozenRatioCost
open HeckeFamily ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

open Filter
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondWholeKernel

end SevenEighths.CenteredMomentSecondFrozenRatioCost

end

end OAI
end


