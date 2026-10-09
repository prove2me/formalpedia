-- Prove2me | Definitions.Def_OAIHecke78B025
-- name    : OAIHecke78B025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T02:17:47.962274+00:00
-- url     : https://prove2.me/theorems/2751ed1e-ea49-4f80-95cd-6de603260cf0
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 26 of 29
-- statement:
--   Definitions bundle 26 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B023`, `OAIHecke78B024` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Moments.SecondMovingSupport`, `Moments.SecondSixthReduction`, `Moments.SecondSixthSource`, `Moments.AllocatedNaturalSource`, `Moments.AmplifiedRetainedRadius`, `Moments.SecondCanonicalScalar`, `Moments.SecondPhysicalBlock`, `Moments.SecondBlockAggregate`, `Moments.SecondLiveBlock`, `Moments.CommonExceptionalCost`, `Moments.CommonRadialPointwise`, `Moments.CommonHeightEnvelope`, `Moments.SecondExceptionalFamily`, `Moments.OriginalCommonHarmonic`, `Moments.SecondEnergySplit`, `Moments.SecondOriginalChildren`, `Moments.SecondNonexceptionalChosenBlock`, `Moments.AllocatedNaturalRadial`, `Energy.AllocatedChildren`, `Moments.FiniteProfileExceptionalStability`, `Energy.Profiles`, `Energy.AllocatedProfiles`, `Moments.AllocatedRayDictionary`, `Moments.AmplificationChildInput`, `Moments.AmplificationChildSourceCaps`, `Moments.FirstAnnularActiveInput`, `Energy.AmplifiedRayDictionary`, `Moments.FirstPhysicalDyadicAssembly`, `Moments.FirstRetainedAssembly`, `Moments.FirstRetainedNorm`, `Moments.SourceInputTailUniform`, `Moments.FirstSourceReduction`, `Energy.OriginalSource`, `Moments.AllocatedChildCapacity`, `Moments.SecondBlockHarmonicMass`, `Moments.FirstMaskedFamily`, `Moments.FirstPhysicalSourceWindowEnergy`, `Moments.FirstPhysicalSourceFixedFamily`, `Moments.SecondPhysicalLedger`, `Moments.FirstSecondInputGates`, `Moments.FirstSecondActiveErrorGates`, `Energy.AmplifiedChildWidth`, `Energy.DeletedChildCapacity`, `Energy.FirstLiveAdmission`, `Energy.ZeroComparison`, `Energy.FixedRadialEntry`, `Energy.NaturalInputMatches`, `Energy.ReferenceChild`, `Energy.ReferenceLowChild`, `Energy.ZeroReferencePhysical`, `Moments.FiniteProfileExceptionalPhysicalBlock`, `Moments.FiniteProfileExceptionalPhysicalBudget`, `Moments.FirstChildProfileControl`, `Moments.FirstNonexceptionalWeightSum`, `Moments.FirstNonexceptionalLocalWeightSum`, `Moments.FirstReferenceEnergy`, `Moments.SecondChildPowerBudget`, `Moments.SecondExceptionalOriginalBlock`, `Moments.SecondExceptionalBudget`, `Moments.SecondFrozenChosen`, `Moments.SourceInputReindex`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B023
import Definitions.Def_OAIHecke78B024

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B025

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Moments.SecondMovingSupport
  Moments.SecondSixthReduction
  Moments.SecondSixthSource
  Moments.AllocatedNaturalSource
  Moments.AmplifiedRetainedRadius
  Moments.SecondCanonicalScalar
  Moments.SecondPhysicalBlock
  Moments.SecondBlockAggregate
  Moments.SecondLiveBlock
  Moments.CommonExceptionalCost
  Moments.CommonRadialPointwise
  Moments.CommonHeightEnvelope
  Moments.SecondExceptionalFamily
  Moments.OriginalCommonHarmonic
  Moments.SecondEnergySplit
  Moments.SecondOriginalChildren
  Moments.SecondNonexceptionalChosenBlock
  Moments.AllocatedNaturalRadial
  Energy.AllocatedChildren
  Moments.FiniteProfileExceptionalStability
  Energy.Profiles
  Energy.AllocatedProfiles
  Moments.AllocatedRayDictionary
  Moments.AmplificationChildInput
  Moments.AmplificationChildSourceCaps
  Moments.FirstAnnularActiveInput
  Energy.AmplifiedRayDictionary
  Moments.FirstPhysicalDyadicAssembly
  Moments.FirstRetainedAssembly
  Moments.FirstRetainedNorm
  Moments.SourceInputTailUniform
  Moments.FirstSourceReduction
  Energy.OriginalSource
  Moments.AllocatedChildCapacity
  Moments.SecondBlockHarmonicMass
  Moments.FirstMaskedFamily
  Moments.FirstPhysicalSourceWindowEnergy
  Moments.FirstPhysicalSourceFixedFamily
  Moments.SecondPhysicalLedger
  Moments.FirstSecondInputGates
  Moments.FirstSecondActiveErrorGates
  Energy.AmplifiedChildWidth
  Energy.DeletedChildCapacity
  Energy.FirstLiveAdmission
  Energy.ZeroComparison
  Energy.FixedRadialEntry
  Energy.NaturalInputMatches
  Energy.ReferenceChild
  Energy.ReferenceLowChild
  Energy.ZeroReferencePhysical
  Moments.FiniteProfileExceptionalPhysicalBlock
  Moments.FiniteProfileExceptionalPhysicalBudget
  Moments.FirstChildProfileControl
  Moments.FirstNonexceptionalWeightSum
  Moments.FirstNonexceptionalLocalWeightSum
  Moments.FirstReferenceEnergy
  Moments.SecondChildPowerBudget
  Moments.SecondExceptionalOriginalBlock
  Moments.SecondExceptionalBudget
  Moments.SecondFrozenChosen
  Moments.SourceInputReindex
-/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondMovingSupport
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSupport CenteredMomentSupportedCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

def fixedExponent (C D : Ideal O) (U : Finset (CommonIndex C D)) (P : CommonIndex C D) : ℕ :=
  min (leftExponent C D P) (rightExponent C D P)+if P∈nonunitPartitionSet C D U then 1 else 0

def fixedActiveSet (C D : Ideal O) (U : Finset (CommonIndex C D)) : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P=>¬6∣fixedExponent C D U P)

end SevenEighths.CenteredMomentSecondMovingSupport

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSixthReduction
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondMovingSupport CenteredMomentFixedRowMask
open CenteredExceptionalProfile CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

def reducedNumerator (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^(fixedExponent C D U P%6)

def sixthFactor (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^(fixedExponent C D U P/6)

end SevenEighths.CenteredMomentSecondSixthReduction

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSixthSource
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

abbrev ActiveIndex (C D : Ideal O) (U : Finset (CommonIndex C D)) := ↥(fixedActiveSet C D U)

def activePrime (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : O := commonPrime C D P.val

def activeExponent (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : ℕ := fixedExponent C D U P.val%6

end SevenEighths.CenteredMomentSecondSixthSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentAllocatedNaturalSource
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentHeckeTwist CenteredMomentHeckeVolume CenteredMomentHeckeCancellation
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained
local notation "O" => HeckeFamily.O

structure Plain where
  W : ℝ→ℂ
  a : ℝ
  b : ℝ
  a_pos : 0<a
  support : Function.support W⊆Set.Icc a b
  smooth : ContDiff ℝ ∞ W

def Plain.profile (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  if h : 1≤U*V.b then retainedProfile V.W V.a V.b V.a_pos V.support V.smooth U hU h t else 0

lemma Plain.profile_retained (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) (h : 1≤U*V.b) :
    V.profile U hU t=retainedProfile V.W V.a V.b V.a_pos V.support V.smooth U hU h t := by
  simp [Plain.profile,h]

lemma Plain.profile_zero (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) (h : U*V.b<1) :
    V.profile U hU t=0 := by simp [Plain.profile,not_le.mpr h]

variable {α : Type*} [Fintype α] [DecidableEq α]

def rawScale (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) (X : ℝ) (j : Fin 2) : ℝ :=
  X/Ideal.absNorm (selectedPlain D a j)

lemma rawScale_pos (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (X : ℝ) (hX : 0<X) (j : Fin 2) : 0< rawScale D a X j := by
  apply div_pos hX
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (selectedDivisor_ne_zero D Finset.univ a _))

def SharedBound (F : Finset α) (b M : α→ℝ) (C ε : ℝ) : Prop :=
    ∀{ι : Type*} [Fintype ι],
      ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)(χ : ι→Character)
        (W₁ W₂ : ι→𝓢(ℝ,ℂ))(X₁ X₂ : ι→ℝ)
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ),
      (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      (∀i j,j∈F → ∀I∈pool i j,Prime I) → (∀i j,j∈F → 0<P i j) →
      (∀i j,j∈F → ∀I∈pool i j,‖β i j I‖≤M j) →
      (∀i j,j∈F → ∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
      ∀E : ℝ,0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false (W₁ i)
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false (W₂ i)
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ i) (pool i j) (β i j) (P i j)‖^2)≤E) →
      (∑i,‖HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
        HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
        ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j)‖^2)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E

def child (χ : Character) (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (D₁ D₂ : Finset (Ideal O)) (J : Finset α) : ℂ :=
  HeckeDyadic.polynomial χ false (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
  HeckeDyadic.polynomial χ false (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
  ∏i∈liveIndices D a\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)

structure Slots (α : Type*) (b M : α→ℝ) where
  pool : α→Finset (Ideal O)
  ν : α→Ideal O→ℂ
  W : α→ℝ→ℂ
  P : α→ℝ
  prime : ∀i,∀I∈pool i,Prime I
  P_pos : ∀i,0<P i
  ν_bound : ∀i I,‖ν i I‖≤1
  W_bound : ∀i x,‖W i x‖≤M i
  support : ∀i,Function.support (W i)⊆Set.Iic (b i)

def Slots.coefficient {b M : α→ℝ} (s : Slots α b M) (i : α) (I : Ideal O) : ℂ :=
  s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)

structure Row (α : Type*) (b M : α→ℝ) where
  η : Character
  z : O
  z_ne : z≠0
  plain₁ : Plain
  plain₂ : Plain
  slots : Slots α b M
  t : ℝ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  X₁_pos : 0<X₁
  X₂_pos : 0<X₂
  Y₁_pos : 0<Y₁
  Y₂_pos : 0<Y₂
  same_product : X₁*X₂=Y₁*Y₂

def commonSlots (s : CenteredMomentCommonRadialData.Input α) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    Slots (CenteredMomentCommonProfile.liveIndices B.val) (fun i=>s.hi i) (fun i=>s.M i) where
  pool:=fun i=>s.slots i
  ν:=fun i=>s.ν i
  W:=fun i=>s.W i
  P:=fun i=>s.P i
  prime:=fun i=>s.prime i
  P_pos:=fun i=>s.P_pos i
  ν_bound:=fun i=>s.ν_bound i
  W_bound:=fun i=>s.W_bound i
  support:=fun i _ hx=>(s.support i hx).2

end SevenEighths.CenteredMomentAllocatedNaturalSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplifiedRetainedRadius
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstAmplificationChoice CenteredMomentGaussEnergy
open CenteredMomentOriginalChildEnergy
open CenteredMomentAmplificationErrorEnergy CenteredMomentSectorLocalization
open CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

theorem ballProfile_support_upper (x : ℝ) (hx : 0≤x) (h : ballProfile x≠0) : x<2 := by
  have hb : x∈Function.support QuadraticInitialBound.sieveBump := by
    intro hz
    exact h (by simp only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,hz,Complex.ofReal_zero])
  rw [QuadraticInitialBound.sieveBump.support_eq] at hb
  simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hx,
    QuadraticInitialBound.sieveBump] using hb

def mainCommonRadius (Z d K0 c sigma δ reserve : ℝ) : ℝ :=
  Z^(K0+max (d-c) 0+2*sigma+δ+reserve)

def errorCommonRadius (Z d K0 c sigma δ reserve : ℝ) (p : O) (k : ℕ) : ℝ :=
  Z^(K0+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+δ+reserve)

open CenteredMomentFirstScale

open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationOriginalErrors CenteredMomentAmplificationGlobal

end SevenEighths.CenteredMomentAmplifiedRetainedRadius

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalScalar
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSectorLocalization CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

def normalizer (C D : Ideal O) (U : Finset (CommonIndex C D)) : ℝ :=
  partitionNormalizer (commonPrime C D) (leftExponent C D) (rightExponent C D) U

def retainedScalar (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) (h : O) : ℂ :=
  canonicalPartitionScalar C D U (nonunitFrequencyGenerator C D U*h)*
    (retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)):ℂ)

end SevenEighths.CenteredMomentSecondCanonicalScalar

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondSectorRetained CenteredMomentSecondWholeKernel
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

def outerScalar (C D : Ideal O) (K : ℝ) (n : Fin 4→ℤ) : ℝ :=
  K/(Real.sqrt (Ideal.absNorm C:ℝ)*Real.sqrt (Ideal.absNorm D:ℝ)*
    Real.sqrt (dyadicScale (n 2))*Real.sqrt (dyadicScale (n 3)))

def physicalBlock (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) : ℂ :=
  let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  ∑z∈rows,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*z) then
    ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        idealCorrelation (C*I) (D*J)
          ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
          ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
      ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
      (physicalKernel C D W K R (A*z) I J*
        ((dyadicWeight (n 0) (secondEffectiveScale C D A K)*dyadicWeight (n 1) (normValue z)*
          dyadicWeight (n 2) (Ideal.absNorm (I:Ideal O):ℝ)*
          dyadicWeight (n 3) (Ideal.absNorm (J:Ideal O):ℝ):ℝ):ℂ)) else 0

def normalizedBlock (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) : ℂ :=
  let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  ∑z∈rows,retainedScalar C D U R z*
    ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        idealCorrelation (C*I) (D*J)
          ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
          ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
      ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
      wholeKernel W (fun _=>logAnnulus)
        (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
        (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
        (Real.log (normValue z/dyadicScale (n 1)))
        (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/dyadicScale (n 2)))
        (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/dyadicScale (n 3)))

end SevenEighths.CenteredMomentSecondPhysicalBlock

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondBlockAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst
open CenteredMomentSecondLocalization
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorColumns
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentHeckeColumnWindow
open CenteredMomentSectorLocalization CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondRetainedRows
open CenteredMomentSecondActiveDyadic CenteredMomentSecondDyadicPartition
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondWholeKernel
local notation "O" => ActualEisensteinCubic.O

abbrev ActiveLabel (S : Finset (Ideal O)) (β : Ideal O→ℂ) :=
  ↥(commonLabels (supportedColumns (activeSource S β)) (supportedColumns (activeSource S β)))

abbrev SourceBlocks (C D : Ideal O) (U : Finset (CommonIndex C D)) (K R H : ℝ) :=
  Blocks (sourceLower C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K)
    (sourceUpper C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K R H)

end SevenEighths.CenteredMomentSecondBlockAggregate

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondLiveBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorRetained
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
local notation "O" => HeckeFamily.O

def liveLabels (η:Character) (S:Finset (Ideal O)) (β:Ideal O→ℂ):Finset (ActiveLabel S β):=
  Finset.univ.filter (fun p=>idealCoeff η p.val.1≠0 ∧ idealCoeff η p.val.2≠0)

def liveRows (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O):Finset O:=
  rows.filter (fun z=>retainedWeight R
    (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0)

end SevenEighths.CenteredMomentSecondLiveBlock

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonExceptionalCost
open HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def frozenProfile (s:Input ι):ℝ:=(∏i,s.M i)*(max 1 s.upper)^Fintype.card ι

end SevenEighths.CenteredMomentCommonExceptionalCost

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialData
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

 def profileCost (s:Input ι) : ℝ :=
  ((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)*s.toData.profileFactor

end SevenEighths.CenteredMomentCommonRadialPointwise

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonHeightEnvelope
open HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentCommonRadialPointwise CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentCommonAllocationSum CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

 local instance instDecidableEqSumFinOfNatNat_solutions_re2792e_1 : DecidableEq (ι⊕Fin 2) := Classical.decEq _
def withHeight (s:Input ι) (η:Character) (t:ℝ) : Input ι := {s with η:=η,t:=t}

 def envelope (s:Input ι) (C L:Ideal O) (C0 Z δ E:ℝ) : ℝ :=
  C0*Z^δ*(profileCost s*E)*(s.X₁*s.X₂*∏i,s.P i)/((Ideal.absNorm C:ℝ)*Ideal.absNorm L)

end SevenEighths.CenteredMomentCommonHeightEnvelope

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology

namespace SevenEighths.CenteredMomentSecondExceptionalFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentPartitionNorm
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource
open CenteredMomentSecondLiveBlock
open CenteredMomentSecondPhysicalBlock CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentRestrictedEnergy CenteredMomentSectorLocalization RayFourExpansion
open CenteredExceptionalProfile CenteredMomentReflectedSource
local notation "O" => HeckeFamily.O

structure Family (η:Character) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (τ:RayCharacter→Character) : Prop where
  element_eq : ∀χ n,elementCoeff (τ χ) n=
    rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n
  height_eq : ∀χ I,Supported I→(IsCoprime C I ∨ IsCoprime D I)→∀t,
    heightCoeff (τ χ) t I=heightCoeff η t I*
      idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
      rayCharacter χ (primaryGenerator I)
  physical_budget : ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U R rows W K n≠0→∀χ,
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
      (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
    ∀Z:ℝ,1<Z→∀z∈liveRows C D U R rows,
      Real.logb Z (normValue z)+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
        Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ))

def expandedConductor (τ:Character)(R C:Ideal O)(z:O):ℕ :=
  τ.modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
    (R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm

def expandedFactor (η:Character):ℕ :=
  1296*η.modulus.absNorm*fixedFactor*(Ideal.span {fixedBadMask}).absNorm*
    (Ideal.span {(72:O)}).absNorm

end SevenEighths.CenteredMomentSecondExceptionalFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentOriginalCommonHarmonic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSupportedZeroEnergy CenteredMomentAddedZeroUniform
open CenteredMomentSecondActiveCount CenteredMomentActiveSource CenteredMomentCommonHarmonicMass
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance instDecidableEqSumFinOfNatNat_solutions : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def coefficient (s:Input ι) (R seed:Ideal O) : Ideal O→ℂ:=
  finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)

def sourceRadius (s:Input ι):ℝ:=(∏i,s.hi i)*s.b₁*s.b₂*(s.X₁*s.X₂)*(∏i,s.P i)

end SevenEighths.CenteredMomentOriginalCommonHarmonic

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondEnergySplit
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentRestrictedEnergy
open CenteredMomentChildRows RayFourExpansion
local notation "O"=>HeckeFamily.O

def sourceRows (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):Finset O:=
  liveRows C D U R (retainedRows R (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))

def partRows (exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):Finset O:=
  (sourceRows C D U R).filter (fun z=>if exceptional then
    CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z
    else nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z)

def partEnergy (exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ):ℂ:=
  ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          W K (fun i=>(n i:ℤ))

end SevenEighths.CenteredMomentSecondEnergySplit

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondOriginalChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

local instance instDecidableEqSumFinOfNatNat_solutions_re2792e_2 : DecidableEq (ι⊕Fin 2) := Classical.decEq _
def core (s:Input ι) (C:Ideal O) (C0 Z δ E:ℝ) : ℝ :=
  C0*Z^δ*(profileCost s*E)*(s.X₁*s.X₂*∏i,s.P i)/(Ideal.absNorm C:ℝ)

def sourceRadial (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (H:ℝ) (hH:0<H)
    (hΦ:∀z:O,0≤(Φ (normValue z/H)).re) : Radial :=
  ⟨keep,Φ,H,hH,fun z=>by simpa only [normValue_eq_embedding] using hΦ z⟩

end SevenEighths.CenteredMomentSecondOriginalChildren

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentSecondOriginalChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondWholeKernel
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair

local instance instDecidableEqSumFinOfNatNat_solutions_re2792e_3 : DecidableEq (ι⊕Fin 2) := Classical.decEq _
def canonicalRadial (τ:Character)(Q:Ideal O)(n:Fin 4→ℤ):Radial:=
  sourceRadial (fun z=>z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow τ Q fixedBadMask 1 z)
    ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _z=>ballProfile_nonneg _)

end SevenEighths.CenteredMomentSecondNonexceptionalChosenBlock

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentAllocatedNaturalRadial
open HeckeFamily HeckeDyadic ConcreteTraceCRT MeasureTheory
open CenteredMomentAllocatedNaturalSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentRetainedProfile CenteredMomentLattice
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentOriginalRadialComparison
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentRadialEligibleEnergy
local notation "O" => HeckeFamily.O

def naturalCharacter (η : Character) (z : O) : Character :=
  if h : z≠0 then (naturalRow η z h).character else η

variable {α : Type*} [Fintype α] [DecidableEq α]

def Shared (F : Finset α) (b M : α→ℝ) (C ε : ℝ) : Prop :=
  ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)
      (χ : O→Character)(W₁ W₂ : 𝓢(ℝ,ℂ))(X₁ X₂ a₁ b₁ a₂ b₂ : ℝ)
      (pool : α→Finset (Ideal O))(β : α→Ideal O→ℂ)(P : α→ℝ)
      (keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K E : ℝ),
      0<X₁ → 0<X₂ → 0≤b₁ → 0≤b₂ →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      (∀j∈F,∀I∈pool j,Prime I) → (∀j∈F,0<P j) →
      (∀j∈F,∀I∈pool j,‖β j I‖≤M j) →
      (∀j∈F,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) →
      0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) → 0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        radialEnergy (fun z=>polynomial (χ z) false W₁
          (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          polynomial (χ z) false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j)) keep Φ K≤E) →
      radialEnergy (fun z=>polynomial ((χ z).excludePrimes R hR) false W₁ X₁ 0 0 *
        polynomial ((χ z).excludePrimes R hR) false W₂ X₂ 0 0 *
        ∏j∈F,naturalSlot ((χ z).excludePrimes R hR) (pool j) (β j) (P j)) keep Φ K≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E

def commonChild (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂ : Plain) (left : Bool) (z : O) (D₁ D₂ : Finset (Ideal O))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) : ℂ :=
  let d:=commonData (withHeight s τ v) C R B
  if left then child (naturalCharacter τ z) L a V₁ V₂ d.slots d.coefficient d.P v
    d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J
  else child (naturalCharacter τ z) L a V₁ V₂ d.slots d.coefficient d.P v
    d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J

def CommonBound (b M : α→ℝ) (C₀ ε : ℝ) : Prop :=
  ∀s : Input α,(∀i,s.hi i≤b i) → (∀i,s.M i≤M i) →
    ∀(τ : Character) (v : ℝ) (C R : Ideal O),R≠0 → ∀B : actualAllocations s.pools C,
    ∀(L : Ideal O) (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂ : Plain,V₁.W=s.W₁ → V₂.W=s.W₂ → ∀r : Radial,(∀z,r.keep z → z≠0) →
    ∀E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ true z D₁ D₂ J) r.keep r.profile r.scale≤E₁) →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ false z D₁ D₂ J) r.keep r.profile r.scale≤E₂) →
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂)

end SevenEighths.CenteredMomentAllocatedNaturalRadial

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedChildren
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentDetectorDictionary CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentSecondHeightFamily CenteredMomentHeckeHeight
open CenteredMomentOriginalRadialComparison CenteredMomentInductionEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentRetainedProfile CenteredMomentCommonAllocationSum

def allocatedEnergy (η:Character)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2))) (V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O))(J:Finset α):ℝ:=
  CenteredMomentInductionEnergy.energy (ι := ↥(liveIndices D a\J)) η
    (fixedBadMask*ConcretePrimeRowBridge.idealGenerator (1:Ideal O)) 1 0
    (V₁.profile (rawScale D a X₁ 0) (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile (rawScale D a X₂ 1) (rawScale_pos D a X₂ hX₂ 1) t)
    (fun i:↥(liveIndices D a\J)=>pool i) (fun i:↥(liveIndices D a\J)=>heightCoefficient (β i) t)
    (fun i:↥(liveIndices D a\J)=>P i)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    r.keep r.profile r.scale

def commonAllocatedEnergy (s:Input α)(τ:Character)(v:ℝ)(C R:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂:Plain)(r:Radial)(left:Bool)(D₁ D₂:Finset (Ideal O))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)):ℝ:=
  let d:=commonData (withHeight s τ v) C R B
  if left then allocatedEnergy τ r D a V₁ V₂ d.slots d.coefficient d.P
    v d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J
  else allocatedEnergy τ r D a V₁ V₂ d.slots d.coefficient d.P
    v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J

end SevenEighths.CenteredMomentEnergyAllocatedChildren

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff FourierTransform

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open CenteredMomentRetainedProfile CenteredMomentAllocatedNaturalSource
open EisensteinSchwartzPoisson CenteredMomentLattice

def sourcePlain (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) : Plain :=
  ⟨W,a,b,ha,hs,W.smooth ⊤⟩

theorem sourcePlain_support (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (U:ℝ) (hU:0<U) (t:ℝ) :
    Function.support ((sourcePlain a b ha W hs).profile U hU t:ℝ→ℂ)⊆
      Set.Icc (a/max 1 b) b := by
  by_cases hret:1≤U*b
  · rw [Plain.profile_retained _ U hU t hret]
    exact retainedProfile_support W a b ha hs (W.smooth ⊤) U hU hret t
  · rw [Plain.profile_zero _ U hU t (lt_of_not_ge hret)]
    simp

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentEnergyProfiles
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedNaturalSource
open CenteredMomentScaleSupremum

structure Test (a b:ℝ) where
  profile : 𝓢(ℝ,ℂ)
  support : Function.support (profile:ℝ→ℂ)⊆Set.Icc a b

def lower (a b:ℝ):ℕ→ℝ
  | 0=>a
  | n+1=>lower a b n/max 1 b

def derivativeChoice (W:𝓢(ℝ,ℂ))(j:Fin 2):𝓢(ℝ,ℂ):=
  if j=0 then W else DetectorDictionaryInverseUniform.scaleCLM W

lemma derivativeChoice_apply (W:𝓢(ℝ,ℂ))(j:Fin 2):
    (derivativeChoice W j:ℝ→ℂ)=scaleTest W j:=by
  unfold derivativeChoice scaleTest
  split_ifs
  · rfl
  · exact funext (DetectorDictionaryInverseUniform.scaleCLM_apply W)

lemma derivativeChoice_support (a b:ℝ)(W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)(j:Fin 2):
    Function.support (derivativeChoice W j:ℝ→ℂ)⊆Set.Icc a b:=by
  rw [derivativeChoice_apply]
  exact scaleTest_support W a b hs j

def step (a b:ℝ)(ha:0<a)(W:Test a b)(U:ℝ)(hU:0<U)(t:ℝ)(j:Fin 2):
    Test (a/max 1 b) b where
  profile:=derivativeChoice ((sourcePlain a b ha W.profile W.support).profile U hU t) j
  support:=derivativeChoice_support _ _ _ (sourcePlain_support a b ha W.profile W.support U hU t) j

open CenteredMomentSectorLocalization in
lemma annulus_support : Function.support (fun x:ℝ=>(annulus x:ℂ))⊆Set.Icc (1/4:ℝ) 1:=by
  intro x hx
  have hn:annulus x≠0:=by simpa using hx
  exact ⟨(lt_of_not_ge (fun h=>hn (annulus_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hn (annulus_zero_high x h))).le⟩

def annulusTemplate:Test (1/4) 1 where
  profile:=(HasCompactSupport.of_support_subset_isCompact isCompact_Icc annulus_support).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp CenteredMomentSectorLocalization.annulus_smooth)
  support:=annulus_support

def annulusSeed (a b:ℝ)(ha:a≤1/4)(hb:1≤b):Test a b where
  profile:=annulusTemplate.profile
  support:=fun _x hx=>⟨ha.trans (annulusTemplate.support hx).1,
    (annulusTemplate.support hx).2.trans hb⟩

end SevenEighths.CenteredMomentEnergyProfiles

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedProfiles
open CenteredMomentFiniteProfileExceptional

def retainedPair (a b:ℝ)(ha:0<a)(p:Profiles a b)
    (U:Fin 2→ℝ)(hU:∀i,0<U i)(t:ℝ):Profiles (a/max 1 b) b where
  profile:=fun i=>(sourcePlain a b ha (p.profile i) (p.support i)).profile (U i) (hU i) t
  support:=fun i=>sourcePlain_support a b ha (p.profile i) (p.support i) (U i) (hU i) t

end SevenEighths.CenteredMomentEnergyAllocatedProfiles

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentAllocatedRayDictionary
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentHeckeTwist CenteredMomentHeckeCancellation
local notation "O" => HeckeFamily.O

variable {α : Type*} [Fintype α] [DecidableEq α]

def originalEmbedding (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C) :
    CenteredMomentCommonProfile.liveIndices B.val ↪ α :=
  ⟨Subtype.val, Subtype.val_injective⟩

def remaining (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    Finset (CenteredMomentCommonProfile.liveIndices B.val) :=
  CenteredMomentDivisorRaw.liveIndices (ι := CenteredMomentCommonProfile.liveIndices B.val) L a \ J

def originalImage (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) : Finset α :=
  (remaining s C B L a J).map (originalEmbedding s C B)

section RayData
variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

structure Matches (s : Input α) (η₀ : Character)
    (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
    (W : ℝ → ℂ) (bslot Z : ℝ) : Prop where
  character : ∀ i I, s.ν i I = idealCoeff (relativeCharacter M H hH η₀ (θ i)) I
  profile : ∀ i y, s.W i y = W y * (y : ℂ)^(-HeckeDyadic.shift (σ i) (freq i))
  pool : ∀ i, s.slots i = primePool M H bslot (Z^(w i))
  scale : ∀ i, s.P i = Z^(w i)

variable {M H hH}
variable {s : Input α} {η₀ : Character} {θ : α → RayQuotient.Characters M H}
  {w σ freq : α → ℝ} {W : ℝ → ℂ} {bslot Z : ℝ}
  (h : Matches M H hH s η₀ θ w σ freq W bslot Z)

include h

omit h

end RayData
end SevenEighths.CenteredMomentAllocatedRayDictionary

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationChildInput
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRectangle CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentRemainingBox
open CenteredMomentHeckeColumnWindow CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationShortening
open CenteredMomentAmplificationLiveMask CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectors CenteredMomentRectangle
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance instDecidableEq_solutions {κ : Type*} : DecidableEq κ := Classical.decEq _

def original (s : Input ι) (R seed : Ideal O) : OriginalData ι where
  S := s.pools
  R := R
  s := seed
  nu := s.ν
  slot := s.W
  lengths := s.P
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  B₁ := 1
  B₂ := 1

def volume (s : Input ι) : ℝ := s.X₁*s.X₂*∏i,s.P i

theorem volume_pos (s : Input ι) : 0<volume s :=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

theorem residual_ne (S : Finset (Ideal O)) (hS : ∀I∈S,I≠0)
    (B : Ideal O) (hB : B≠0) : ∀I∈residualPool B hB S,I≠0 := by
  intro I hI
  exact right_ne_zero_of_mul (hS (B*I) ((mem_residualPool B hB S I).mp hI))

theorem residual_coverage (S : Finset (Ideal O)) (W : ℝ→ℂ)
    (B : Ideal O) (hB : B≠0) (X Y : ℝ) (h : PlainCoverage S W 1 X Y) :
    PlainCoverage (residualPool B hB S) W 1 (X/B.absNorm) (Y/B.absNorm) := by
  have he := plainCoverage_residualPool S W 1 B hB X Y h
  intro I hi
  apply he I
  simpa only [one_mul,map_mul,map_one,Nat.cast_mul,Nat.cast_one,mul_one,div_div_eq_mul_div,mul_comm] using hi

def child (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : Input (liveIndices B.val) where
  toData := {commonData s C R B with η:=τ,t:=t}
  plain₁ := residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) s.plain₁
  plain₂ := residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) s.plain₂
  plain₁_ne := residual_ne s.plain₁ s.plain₁_ne _ _
  plain₂_ne := residual_ne s.plain₂ s.plain₂_ne _ _
  coverage₁ := residual_coverage s.plain₁ s.W₁ _ _ _ _ s.coverage₁
  coverage₂ := residual_coverage s.plain₂ s.W₂ _ _ _ _ s.coverage₂
  ν_bound := fun i=>s.ν_bound i.val
  W_bound := fun i=>s.W_bound i.val
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := fun i=>s.lower_le i.val
  upper_ge := fun i=>s.upper_ge i.val

@[simp] theorem child_modulus (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).m=fixedBadMask*idealGenerator (R*C) := rfl

@[simp] theorem child_character (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).η=τ := rfl

@[simp] theorem child_height (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).t=t := rfl

def normalizedGaussSource (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (sourceGaussEnergy (original s R seed).columns (original s R seed).beta
    (heightCoeff s.η s.t) W K).re / volume s

def childNormalizedGaussSource (s : Input ι) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  normalizedGaussSource (child s C R B τ t) (R*C) seed W K

end SevenEighths.CenteredMomentAmplificationChildInput

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplificationChildSourceCaps
open ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow
open CenteredMomentCommonAllocationSum CenteredMomentCommonRawScale
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

local instance instDecidableEq_solutions_re2792e_1 {κ : Type*} : DecidableEq κ := Classical.decEq _
def geometry (N : ℕ) (b b₁ b₂ : ℝ) : ℝ := b^(2*N)*b₁*b₂

def nominal (s : Input ι) (K : ℝ) : ℝ := CenteredMomentAmplificationChildInput.volume s^2/K

lemma nominal_pos (s : Input ι) (K : ℝ) (hK : 0<K) : 0<nominal s K :=
  div_pos (sq_pos_of_pos (CenteredMomentAmplificationChildInput.volume_pos s)) hK

def Endpoints (b b₁ b₂ : ℝ) (s : Input ι) : Prop :=
  s.upper≤b ∧ (∀i,0≤ s.hi i) ∧ 0≤ s.b₁ ∧ s.b₁≤b₁ ∧ 0≤ s.b₂ ∧ s.b₂≤b₂

def twiceChild (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :=
  child (child s C R B τ t) (Q^k) (R*C) Bp υ v

end SevenEighths.CenteredMomentAmplificationChildSourceCaps

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily

variable {ι:Type*}[Fintype ι]

def activeInput (s:Input ι):Input ι:={s with
  slots:=fun i=>(s.slots i).filter (fun I=>s.W i ((I.absNorm:ℝ)/s.P i)≠0)
  prime:=fun i I hI=>s.prime i I (Finset.mem_filter.mp hI).1
  coefficient_bound:=fun i I hI=>s.coefficient_bound i I (Finset.mem_filter.mp hI).1}

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary
open HeckeFamily CenteredMomentSecondHeightFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedRayDictionary
open CenteredMomentFirstAnnularInput CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentEligibleEnergy CenteredMomentCommonHeightEnvelope
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]

local instance instDecidableEq_solutions_re2792e_2 {β : Type*} : DecidableEq β := Classical.decEq _
lemma active_pools_subset (s : Input α) (j : α⊕Fin 2) :
    (activeInput s).pools j⊆s.pools j := by
  cases j with
  | inl i => exact Finset.filter_subset _ _
  | inr j => exact Finset.Subset.refl _

lemma actualAllocations_mono {β : Type*} [Fintype β]
    (S T : β→Finset (Ideal O)) (h : ∀i,S i⊆T i) (C : Ideal O) :
    actualAllocations S C⊆actualAllocations T C := by
  intro B hB
  obtain ⟨hlabel,hprod⟩ := Finset.mem_filter.mp hB
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp hlabel
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v,?_,hvB⟩,hprod⟩
  exact Fintype.mem_piFinset.mpr (fun i=>h i (Fintype.mem_piFinset.mp hv i))

abbrev restoreAllocation (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : actualAllocations s.pools C :=
  ⟨B.val,actualAllocations_mono _ _ (active_pools_subset s) C B.property⟩

@[simp] lemma restoreAllocation_val (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : (restoreAllocation s C B).val=B.val := rfl

def restoredError (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) : Input (liveIndices Bp.val) :=
  twiceChild s C R B τ t Q k (restoreAllocation (child s C R B τ t) (Q^k) Bp) υ v

section Ray
variable (M : Ideal O) [NeZero M]
local instance instDecidableEq_solutions_re2792e_3 {β : Type*} : DecidableEq β := Classical.decEq _
local instance instFiniteQuotientOIdeal_solutions : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {s : Input α} {η₀ : Character} {θ : α→RayQuotient.Characters M H}
  {w σ freq : α→ℝ} {W : ℝ→ℂ} {bslot Z : ℝ}

end Ray
end SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicAssembly
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstReduced CenteredMomentFirstColumns CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentRowNorm
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentDyadicCount CenteredMomentPrimitive
local notation "O"=>ActualEisensteinCubic.O

def retainedBlock (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑h∈rows,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (retainedWeight R (‖eisEmbedding h‖^2):ℂ)*
        EisensteinSchwartzPoisson.paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
      else 0

def retainedIndices (R:ℝ):Finset ℤ := (finite_retained_integral_dyads R).toFinset

def bands (K R A B:ℝ):Fin 4→Finset ℤ :=
  ![indices K K,retainedIndices R,indices 1 A,indices 1 B]

abbrev Blocks (K R A B:ℝ):=∀i:Fin 4,↥(bands K R A B i)

def effectiveScale (C D:Ideal O)(E:Finset (CommonIndex C D))(K:ℝ):ℝ:=
  (K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2)/
    ‖eisEmbedding (activeConductor C D)‖^2

def retainedInfiniteBlock (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑'h:O,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (retainedWeight R (‖eisEmbedding h‖^2):ℂ)*
        EisensteinSchwartzPoisson.paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
      else 0

end SevenEighths.CenteredMomentFirstPhysicalDyadicAssembly

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedAssembly
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceRow CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation CenteredMomentHeckeExpansion
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentLogDyadic
local notation "O"=>ActualEisensteinCubic.O

def infiniteSector (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    retainedInfiniteBlock η m A t S c C D hC hD E W K
      (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ)

def physicalSector {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))

end SevenEighths.CenteredMomentFirstRetainedAssembly

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedNorm
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstRetainedAssembly
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors CenteredMomentHeckeExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceRow CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentLogDyadic
open CenteredMomentActiveSource (activeSource)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def sector (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))

def sectorMass (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℝ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      ‖block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))‖

end SevenEighths.CenteredMomentFirstRetainedNorm

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputTailUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance instDecidableEqSumFinOfNatNat_solutions : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def plainControl (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)):ℝ:=
  (∏i,s.M i)*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂

end SevenEighths.CenteredMomentSourceInputTailUniform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSourceReduction
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open CenteredMomentSourceInputFirstRemainder CenteredMomentFirstRetainedNorm
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors
open CenteredMomentActiveSource (activeSource)
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance instDecidableEqSumFinOfNatNat_solutions : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def physicalMass (s:Input ι)(R seed:Ideal O)(m A:O)(Φ:𝓢(ℝ,ℂ))(K Z ξ:ℝ):ℝ:=
  let β:=coefficient s R seed
  let T:=activeSource (finiteColumns (Fintype.piFinset s.pools)) β
  ∑p:commonLabels (supportedColumns T) (supportedColumns T),
    sectorMass s R seed m A s.t T p.val.1 p.val.2
      (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
      (volume s.toData) Z ξ

end SevenEighths.CenteredMomentFirstSourceReduction

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyOriginalSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentSourceRectangle
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentHeckeHeight
open CenteredMomentDivisorRowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentRowNorm
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance energyOriginalSourceDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def completeInput (s : Data ι) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hν : ∀i I,‖s.ν i I‖≤1) (hW : ∀i x,‖s.W i x‖≤ s.M i)
    (lo hi : ℝ) (hlo : 0<lo) (hl : ∀i,lo≤ s.lo i) (hh : ∀i,s.hi i≤hi) : Input ι where
  toData := s
  plain₁ := plainSupportPool s.b₁ s.X₁ s.Y₁
  plain₂ := plainSupportPool s.b₂ s.X₂ s.Y₂
  plain₁_ne := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI|hI
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
  plain₂_ne := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI|hI
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
  coverage₁ := plainSupportPool_coverage s.W₁ s.b₁ s.X₁ s.Y₁ hz₁ s.support₁ s.X₁_pos s.Y₁_pos
  coverage₂ := plainSupportPool_coverage s.W₂ s.b₂ s.X₂ s.Y₂ hz₂ s.support₂ s.X₂_pos s.Y₂_pos
  ν_bound := hν
  W_bound := hW
  lower := lo
  upper := hi
  lower_pos := hlo
  lower_le := hl
  upper_ge := hh

section Natural
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
variable {Z Bmask bΦ a b : ℝ}
variable (state : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0<a)
variable (S : ι→Finset (Ideal O)) (hp : ∀i,∀I∈S i,Prime I)
variable (ν : ι→Character) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
variable (hP : ∀i,0<P i) (hM : ∀i,1≤M i)
variable (aslot bslot : ℝ) (haslot : 0<aslot)
variable (hsSlot : ∀i,Function.support (Wslot i)⊆Set.Icc aslot bslot)
variable (hWslot : ∀i x,‖Wslot i x‖≤M i)
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hsame : Y₁*Y₂=X₁*X₂)

def naturalData : Data ι where
  η := state.character
  m := state.mask
  A := 1
  t := t
  slots := S
  prime := hp
  ν := fun i=>idealCoeff (ν i)
  W := Wslot
  lo := fun _=>aslot
  hi := fun _=>bslot
  P := P
  lo_pos := fun _=>haslot
  P_pos := hP
  support := hsSlot
  W₁ := p.profile 0
  W₂ := p.profile 1
  X₁ := X₁
  X₂ := X₂
  Y₁ := Y₁
  Y₂ := Y₂
  M := M
  M_ge_one := hM
  coefficient_bound := fun i I _=>by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one (ν i) I) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hWslot i ((Ideal.absNorm I:ℝ)/P i))
  b₁ := b
  b₂ := b
  support₁ := fun x hx=>(p.support 0 hx).2
  support₂ := fun x hx=>(p.support 1 hx).2
  X₁_pos := hX₁
  X₂_pos := hX₂
  Y₁_pos := hY₁
  Y₂_pos := hY₂
  same_product := hsame
  rows := ∅
  weight := fun _=>0
  weight_nonneg := fun _ _=>le_refl _

def naturalInput : Input ι :=
  completeInput (naturalData state p S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame)
    (CenteredMomentDetectorPlainSource.support_zero (p.profile 0) a b ha (p.support 0))
    (CenteredMomentDetectorPlainSource.support_zero (p.profile 1) a b ha (p.support 1))
    (fun i I=>idealCoeff_norm_le_one (ν i) I) hWslot aslot bslot haslot
    (fun _=>le_refl _) (fun _=>le_refl _)

end Natural
end SevenEighths.CenteredMomentEnergyOriginalSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained CenteredMomentEligibleEnergy
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

def clippingLoss (Z U₁ U₂ : ℝ) : ℝ :=
  max (-Real.logb Z U₁) 0+max (-Real.logb Z U₂) 0

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def plainLogs (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ : ℝ) : ℝ :=
  Real.logb Z (clippedScale (rawScale D a X₁ 0))+
    Real.logb Z (clippedScale (rawScale D a X₂ 1))

def remainingLogs (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z : ℝ) (P : ι→ℝ) : ℝ := ∑i∈liveIndices D a,Real.logb Z (P i)

def preVolume (s : Data ι) : ℝ := s.X₁*s.X₂*∏i,s.P i

end SevenEighths.CenteredMomentAllocatedChildCapacity

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondBlockHarmonicMass
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedAggregate CenteredMomentSourceMass
open CenteredMomentSecondBlockAggregate
open CenteredMomentSecondActiveCount CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSecondCanonicalNonunit CenteredMomentRankinRadical
open CenteredMomentCommonHarmonicMass CenteredMomentOriginalCommonHarmonic
local notation "O" => ActualEisensteinCubic.O

abbrev ActiveSubsets (S : Finset (Ideal O)) (β : Ideal O→ℂ) :=
  (p : ActiveLabel S β) × Finset (CommonIndex p.val.1 p.val.2)

abbrev ActiveBlocks (S : Finset (Ideal O)) (β : Ideal O→ℂ) (K R H : ℝ) :=
  (q : ActiveSubsets S β) × SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H

def pairWeight (C D : Ideal O) : ℝ := 1/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)

def activeSubsetLabel (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (q : ActiveSubsets S β) : Label := (q.1.val,q.2.image Subtype.val)

end SevenEighths.CenteredMomentSecondBlockHarmonicMass

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMaskedFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFixedRowMask
open CenteredMomentFirstFamily CenteredMomentFirstIdealFamily CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentCanonicalFirst CenteredMomentCommonSupport
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationShortening CenteredMomentAmplificationSourceDomain
open CenteredMomentAmplificationFamily
open CenteredMomentOriginalChildEnergy
open CenteredMomentGaussEnergy CenteredMomentLiveDomain CenteredMomentPrimaryCharacter
open ActualEisensteinCubic ConcreteTraceCRT CenteredMomentChildAssembly CenteredMomentChildRows
local notation "O" => HeckeFamily.O
local notation "fixedBadMask" => (goodLambda*(2:O))

lemma fixed_mask_ne_zero : fixedBadMask≠0 :=
  mul_ne_zero PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero (by norm_num)

def idealMask (u : O) (I : Ideal O) : ℂ := if IsCoprime I (Ideal.span {u}) then 1 else 0

def maskedSource (u : O) (β : Ideal O → ℂ) (I : Ideal O) : ℂ := β I * idealMask u I

lemma idealMask_span (u n : O) : idealMask u (Ideal.span {n}) =
    if IsCoprime n u then 1 else 0 := by
  simp only [idealMask, Ideal.isCoprime_span_singleton_iff]

lemma idealMask_primary (u : O) (I : Ideal O) (hI : Supported I) :
    idealMask u I = if IsCoprime (primaryGenerator I) u then 1 else 0 := by
  conv_lhs => rw [←primary_span_supported I hI, idealMask_span]

lemma rowWeight_mask_factor (η : Character) (u : O) (I : Ideal O)
    (hI : Supported I) (t : ℝ) :
    rowWeight η (fixedBadMask*u) 1 1 t I =
      idealMask u I * rowWeight η fixedBadMask 1 1 t I := by
  rw [rowWeight_one_primary η (fixedBadMask*u) t I hI,
    rowWeight_one_primary η fixedBadMask t I hI, idealMask_primary u I hI]
  change elementCoeff η (primaryGenerator I) *
      (if IsCoprime (fixedBadMask*u) (primaryGenerator I) then (1:ℂ) else 0) *
      (Ideal.absNorm I:ℂ)^(Complex.I*t) =
    (if IsCoprime (primaryGenerator I) u then (1:ℂ) else 0) *
      (elementCoeff η (primaryGenerator I) *
        (if IsCoprime fixedBadMask (primaryGenerator I) then (1:ℂ) else 0) *
        (Ideal.absNorm I:ℂ)^(Complex.I*t))
  rw [IsCoprime.mul_left_iff]
  by_cases hm : IsCoprime fixedBadMask (primaryGenerator I)
  <;> by_cases hu : IsCoprime (primaryGenerator I) u
  <;> simp [hm, hu, show IsCoprime u (primaryGenerator I) ↔
      IsCoprime (primaryGenerator I) u from isCoprime_comm]

theorem exists_canonical_masked_pair (η : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character, τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I)) =
          idealMask u I*heightCoeff τ₁ t I) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I)) =
          idealMask u I*heightCoeff τ₂ t I) := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩ := exists_first_ideal_pair η fixedBadMask fixed_mask_ne_zero
    (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda) C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,?_,?_⟩
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,heightCoeff,h₁ I hI t]
    ring
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,heightCoeff,h₂ I hI t]
    ring

end SevenEighths.CenteredMomentFirstMaskedFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy
open CenteredMomentSecondSectorColumns IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]

def commonEnergy (s:OriginalData ι)(C:Ideal O)(hC:Supported C)(τ:Character)
    (t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):ℂ:=
  let Q:=residualPool C hC.1 s.columns
  gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then s.beta (C*I) else 0)*heightCoeff τ t I) U K

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy CenteredMomentCommonSupport
open CenteredMomentChildAssembly CenteredMomentAddedZeroUniform RayFourExpansion CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

structure FixedPair (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter) where
  left : Character
  right : Character
  left_modulus : left.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}
  right_modulus : right.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}
  left_height : ∀I:Ideal O,Supported I→∀t:ℝ,
    heightCoeff left t I=rowWeight η fixedBadMask 1 1 t I*
      (leftCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
          (activeExponent C D)) (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))
  right_height : ∀I:Ideal O,Supported I→∀t:ℝ,
    heightCoeff right t I=rowWeight η fixedBadMask 1 1 t I*
      (rightCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
          (activeExponent C D)) (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))

def fixedPair (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter):FixedPair η C D hC E ξ₁ ξ₂:=
  Classical.choice (by
    obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,_,_⟩:=exists_canonical_masked_pair η C D hC E ξ₁ ξ₂
    exact ⟨⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩⟩)

variable {ι:Type*}[Fintype ι]
local instance firstFixedFamilyDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalLedger
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSupport CenteredMomentHeckeColumnWindow
open CenteredMomentForcing
open CenteredMomentFirstWholeKernel
open CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

def forcingNorm (C D:Ideal O) (U:Finset (CommonIndex C D)) : ℝ :=
  Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U))

def saving (C D:Ideal O) (U:Finset (CommonIndex C D)) (Z:ℝ) : ℝ :=
  Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)-
    5*Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)/6-
    Real.logb Z (Ideal.absNorm (∏ P:CommonIndex C D,P.val):ℝ)+
    Real.logb Z (Ideal.absNorm (∏ P∈U,P.val):ℝ)+
    Real.logb Z (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ)/6+
    Real.logb Z (forcingNorm C D U)/3

def centralPhysicalCost (C D:Ideal O) (U:Finset (CommonIndex C D))
    (K H:ℝ) (n:Fin 4→ℤ) : ℝ :=
  (1/H)*outerScalar C D K n*normalizer C D U*
    (dyadicScale (n 1))^(1/6:ℝ)/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))*
    (H^2/((C.absNorm:ℝ)*D.absNorm))*(Ideal.absNorm (∏ P:CommonIndex C D,P.val):ℝ)/
    (forcingNorm C D U)^(1/3:ℝ)

end SevenEighths.CenteredMomentSecondPhysicalLedger

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSecondInputGates
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

local instance instDecidableEq_solutions_re2792e_4 {α:Type*}:DecidableEq α:=Classical.decEq _
def exponent (A D P q ε ξ:ℝ):ℝ:=
  max (A+ε) (max (2*A+D+ε+ξ/2) (max (A+P+ε) q))

structure Ready {ι:Type*}[Fintype ι](s:Input ι)(R:Ideal O)(K Z ξ B:ℝ):Prop where
  puncture_ne : R≠0
  scale_pos : 0<K
  volume_cap : volume s≤Z^B
  source_nonneg : 0≤ sourceRadius s
  source_cap : sourceRadius s≤Z^B
  conductor_cap : (s.η.modulus.absNorm:ℝ)≤Z^B
  puncture_cap : (R.absNorm:ℝ)≤Z^B
  nominal_pos : 0<nominal s K
  nominal_cap : nominal s K≤Z^B
  frequency_pos : 0<frequencyRadius (nominal s K) Z ξ
  frequency_cap : frequencyRadius (nominal s K) Z ξ≤Z^B

end SevenEighths.CenteredMomentFirstSecondInputGates

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSecondActiveErrorGates
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstSecondInputGates CenteredMomentFirstAnnularInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

local instance instDecidableEq_solutions_re2792e_5 {α : Type*} : DecidableEq α := Classical.decEq _
def errorInput (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) : Input (liveIndices Bp.val) :=
  child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v

end SevenEighths.CenteredMomentFirstSecondActiveErrorGates

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyAmplifiedChildWidth
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstAnnularInput CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondDyadicRowSupport CenteredMomentSecondRadicalBudget
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstScale CenteredMomentAmplifiedChildWidth
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι]

local instance instDecidableEq_solutions_re2792e_6 {α:Type*}:DecidableEq α:=Classical.decEq _
def geometry (N:ℕ)(b:ℝ):ℝ := (b^N)^2

lemma geometry_pos (N:ℕ)(b:ℝ)(hb:1≤b):0<geometry N b := by
  unfold geometry
  exact sq_pos_of_pos (pow_pos (zero_lt_one.trans_le hb) _)

def mainRadius (C D:Ideal O)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ):ℝ :=
  mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V))
    (Real.logb Z (C.absNorm:ℝ)) σ δ reserve

def errorRadius (C D:Ideal O)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ)(p:O)(k:ℕ):ℝ :=
  errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V))
    (Real.logb Z (C.absNorm:ℝ)) σ δ reserve p k

def threshold (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ):ℝ :=
  fixedWidthThreshold 2 (geometry N b) σ (by norm_num) (geometry_pos N b hb) hσ

end SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyDeletedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedChildCapacity
open CenteredMomentRetainedProfile CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentDivisorRaw CenteredMomentEnergyBands
open CenteredMomentLiveCapacity
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def postmaskLength (Z U : ℝ) (F : Finset (Ideal O)) : ℝ :=
  length Z (clippedScale U/((∏I∈F,I).absNorm:ℝ))

def deletedExcess (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι) : ℝ :=
  excess (liveIndices D a\J) (fun i=>Real.logb Z (P i))
    (postmaskLength Z (rawScale D a X₁ 0) F₁)
    (postmaskLength Z (rawScale D a X₂ 1) F₂) M κ

end SevenEighths.CenteredMomentEnergyDeletedChildCapacity

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstLiveAdmission
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open ActualEisensteinCubic CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstSecondInputGates CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstPhysicalSource
open CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAnnularInput CenteredMomentSectorLocalization
open CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceConductorCaps
open CenteredMomentEnergyBands
open CenteredMomentEnergyAmplifiedChildWidth CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentActiveSource
open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CompletedGauss RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentRowNorm
local notation "O" => HeckeFamily.O
local instance instDecidableEqSumFinOfNatNat_solutions {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def columnIdeal (C D : Ideal O) (right : Bool) : Ideal O := if right then D else C

def oppositeIdeal (C D : Ideal O) (right : Bool) : Ideal O := if right then C else D

def columnMainRadius (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) (right : Bool) : ℝ :=
  mainCommonRadius Z (Real.logb Z ((oppositeIdeal C D right).absNorm : ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K V))
    (Real.logb Z ((columnIdeal C D right).absNorm : ℝ)) σ δ reserve

def columnErrorRadius (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) (right : Bool) (p : O) (k : ℕ) : ℝ :=
  errorCommonRadius Z (Real.logb Z ((oppositeIdeal C D right).absNorm : ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K V))
    (Real.logb Z ((columnIdeal C D right).absNorm : ℝ)) σ δ reserve p k

def readyBudget (A P : ℝ) : ℝ := 4*A + P + 10

end SevenEighths.CenteredMomentEnergyFirstLiveAdmission

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroComparison
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEnergyOriginalSource
open CenteredMomentRadialEligibleEnergy CenteredMomentInductionEnergy
open CenteredMomentRetainedProfile CenteredMomentRetainedEnergy
open CenteredMomentHeckeExpansion CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentSourceRow
open CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceProfileMass CenteredMomentHeckeHeight CenteredMomentSourceMass
local notation "O" => HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

local instance instDecidableEqSumFinOfNatNat_solutions_re2792e_4 : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum
def smallScale (b:ℝ):ℝ:=1/(2*max 1 b)

lemma smallScale_pos (b:ℝ):0<smallScale b:=by unfold smallScale;positivity

def zeroData (s:Input ι):CenteredMomentEligibleEnergy.Data ι := { s.toData with
  Y₁ := smallScale s.b₁
  Y₂ := s.X₁*s.X₂/smallScale s.b₁
  Y₁_pos := smallScale_pos _
  Y₂_pos := div_pos (mul_pos s.X₁_pos s.X₂_pos) (smallScale_pos _)
  same_product := by field_simp [ne_of_gt (smallScale_pos s.b₁)] }

def zeroInput (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0):Input ι :=
  completeInput (zeroData s) hz₁ hz₂ s.ν_bound s.W_bound s.lower s.upper
    s.lower_pos s.lower_le s.upper_ge

omit [DecidableEq ι] in
@[simp] lemma zeroInput_volume (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0):
    volume (zeroInput s hz₁ hz₂)=volume s:=rfl

end SevenEighths.CenteredMomentEnergyZeroComparison

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFixedRadialEntry
open ConcretePrimeRowBridge QuadraticInitialBound CenteredMomentSourceMass
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEnergyOriginalSource
open CenteredMomentSourceRow
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentRadialEligibleEnergy
open CenteredMomentEnergyZeroComparison CanonicalQuadraticSieve
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance instDecidableEqSumFinOfNatNat_solutions : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

end SevenEighths.CenteredMomentEnergyFixedRadialEntry

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyNaturalInputMatches
open HeckeFamily HeckePrimeAnnular CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonRadialData CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
local notation "O" => HeckeFamily.O

def profile (W : ℝ → ℂ) (σ freq y : ℝ) : ℂ :=
  W y * (y : ℂ)^(-HeckeDyadic.shift σ freq)

lemma profile_support (W : ℝ → ℂ) (a b : ℝ)
    (hWs : Function.support W ⊆ Set.Icc a b) (σ freq : ℝ) :
    Function.support (profile W σ freq) ⊆ Set.Icc a b := by
  intro y hy
  apply hWs
  intro hz
  exact hy (by simp only [profile, hz, zero_mul])

lemma profile_norm (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (σ freq y : ℝ) :
    ‖profile W σ freq y‖ = ‖W y‖ * y^(-σ) := by
  by_cases hz : W y = 0
  · simp only [profile, hz, zero_mul, norm_zero]
  · have hy : 0 < y := ha.trans_le (hWs hz).1
    simp only [profile, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
      Complex.neg_re, HeckeDyadic.shift_re]

theorem exists_profile_bound (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ σ ∈ Set.Icc lo hi, ∀ freq y : ℝ,
      ‖profile W σ freq y‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro σ hσ freq y
  by_cases hz : W y = 0
  · simpa only [profile, hz, zero_mul, norm_zero] using
      (zero_le_one.trans (le_max_left 1 C))
  · rw [profile_norm W a b ha hWs]
    exact (hb σ hσ y (hWs hz)).trans (le_max_right _ _)

def profileBound (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) : ℝ :=
  (exists_profile_bound W hW a b lo hi ha hWs).choose

lemma profileBound_ge_one (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) :
    1 ≤ profileBound W hW a b lo hi ha hWs :=
  (exists_profile_bound W hW a b lo hi ha hWs).choose_spec.1

lemma norm_profile_le (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b)
    (σ : ℝ) (hσ : σ ∈ Set.Icc lo hi) (freq y : ℝ) :
    ‖profile W σ freq y‖ ≤ profileBound W hW a b lo hi ha hWs :=
  (exists_profile_bound W hW a b lo hi ha hWs).choose_spec.2 σ hσ freq y

section Input
variable {ι : Type*} [Fintype ι]
variable (Q : Ideal O) [NeZero Q]
local instance instFiniteQuotientOIdeal_solutions : Finite (O ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne Q)
variable (H : Subgroup (O ⧸ Q)ˣ) (hH : RayOrthogonality.globalUnits Q ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters Q H)
variable (W : ℝ → ℂ) (hW : Continuous W)
variable (aslot bslot lo hi : ℝ) (haslot : 0 < aslot)
variable (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z Bmask bΦ a b : ℝ}
variable (state : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0 < a)
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hsame : Y₁ * Y₂ = X₁ * X₂)

def input : Input ι :=
  CenteredMomentEnergyOriginalSource.naturalInput state p ha
    (fun i => primePool Q H bslot (Z^(w i)))
    (fun _ _ hI => (Finset.mem_filter.mp hI).2.1)
    (fun i => relativeCharacter Q H hH η₀ (θ i))
    (fun i => profile W (σ i) (freq i)) (fun i => Z^(w i))
    (fun _ => profileBound W hW aslot bslot lo hi haslot hWs)
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans_le state.base_ge_one) _)
    (fun _ => profileBound_ge_one W hW aslot bslot lo hi haslot hWs)
    aslot bslot haslot (fun i => profile_support W aslot bslot hWs (σ i) (freq i))
    (fun i => norm_profile_le W hW aslot bslot lo hi haslot hWs (σ i) (hσ i) (freq i))
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame

local notation "inp" => input Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame

end Input
end SevenEighths.CenteredMomentEnergyNaturalInputMatches

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceChild
open HeckeFamily HeckeDyadic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentEnergyAllocatedChildren
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentEnergyProfiles CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily CenteredMomentLattice CenteredMomentRetainedProfile CenteredMomentTwist
local notation "O"=>HeckeFamily.O

def unpuncturedState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):NaturalState Z 0 bΦ where
  character:=s.character
  fixedModulus:=s.fixedModulus
  puncture:=1
  radial:=(effectiveState s).radial
  rowWidth:=s.rowWidth
  characterWidth:=s.characterWidth
  base_ge_one:=s.base_ge_one
  row_nonneg:=s.row_nonneg
  character_nonneg:=s.character_nonneg
  scale_eq:=s.scale_eq
  modulus_bound:=s.modulus_bound
  puncture_ne_zero:=one_ne_zero
  puncture_bound:=by simp
  radial_support:=s.radial_support
  row_ne_zero:=fun z hz=>s.row_ne_zero z hz.1
  nonexceptional:=by
    intro z hz hh
    have hn:=s.row_ne_zero z hz.1
    have hunit:CenteredExceptionalProfile.FixedInducingRow s.character s.fixedModulus fixedBadMask 1 z:=
      (CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff s.character s.fixedModulus
        fixedBadMask (idealGenerator 1) 1 z fixedBadMask_ne_zero
        (idealGenerator_ne_zero 1 one_ne_zero) one_ne_zero hn
        (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hh
    exact s.nonexceptional z hz.1
      ((CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff s.character s.fixedModulus
        fixedBadMask (idealGenerator s.puncture) 1 z fixedBadMask_ne_zero
        (idealGenerator_ne_zero _ s.puncture_ne_zero) one_ne_zero hn
        (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hunit)

def independentProfiles {a b:ℝ}(ha:0<a)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)(t₁ t₂:ℝ):Profiles a b where
  profile:=fun i=>if i=0 then normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
    else normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  support:=by
    intro i
    split_ifs
    · exact (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans hs₁
    · exact (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans hs₂

end SevenEighths.CenteredMomentEnergyReferenceChild

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowChild
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

def unitBudgetState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(hB:0≤Bmask):
    NaturalState Z Bmask bΦ:=
  {unpuncturedState s with
    puncture_bound:=by simpa only [unpuncturedState,map_one,Nat.cast_one] using Real.one_le_rpow s.base_ge_one hB}

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyReferenceLowChild

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferencePhysical
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState
open CenteredMomentEnergyOriginalSource
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
local notation "O"=>HeckeFamily.O

local instance instDecidableEqSumFinOfNatNat_solutions_re2792e_5 : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _
def balancedInput {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)
    (ha:0<a)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):Input (Fin 0):=
  naturalInput s p ha (fun _=>∅) (by simp) (fun _=>s.character) (fun _=>0)
    (fun _=>1) (fun _=>1) (by simp) (by simp) 1 1 (by norm_num)
    (by simp) (by simp) t X₁ X₂ (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
    hX₁ hX₂ (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

end SevenEighths.CenteredMomentEnergyZeroReferencePhysical

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance instDecidableEqSumFinOfNatNat_solutions_1 {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def sourceBudget {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
    Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
      (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
      2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*
    ((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*
      frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss UniqueFactorizationMonoid
open CenteredMomentSecondPhysicalLedger
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentForcing CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def profileFactor {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q:Ideal O)(K:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*J)*
    p.control Sprofile^2*(1+‖s.t‖)^(2*J)*slotControl s.toData^2*frozenProfile s^2*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstChildProfileControl
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonRadialPointwise CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mass (s : Input ι) : ℝ := ∏ i,s.M i

def exceptionalConstant (N : ℕ) (b : ℝ) (J : ℕ) (Q : Ideal O) (K : ℝ) : ℝ :=
  K*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    (1+2*Real.pi)^(4*J)*
    (∫u:ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
      CenteredMomentLogDyadic.logAnnulus CenteredMomentLogDyadic.logAnnulus_compact
      CenteredMomentLogDyadic.logAnnulus_smooth u‖)^2*
    ((128*b)^N)^2*(b^N)^2

end SevenEighths.CenteredMomentFirstChildProfileControl

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalWeightSum
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonRadialData
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentActiveSource CenteredMomentSupportedCorrelation CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentRankinRadical
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance instDecidableEqSumFinOfNatNat_solutions : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Labels (s:Input ι)(R seed:Ideal O):=
  ActiveLabel (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)

end SevenEighths.CenteredMomentFirstNonexceptionalWeightSum

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentFirstPhysicalSource
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentExceptionalAmplitudePair
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

local instance instDecidableEqSumFinOfNatNat_solutions_re2792e_6 : DecidableEq (ι⊕Fin 2):=Classical.decEq _
def localRadius (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  frequencyRadius (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)) Z ξ

end SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstReferenceEnergy
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstSourceReduction CenteredMomentFirstInactiveRadicalMass
open CenteredMomentSecondRetainedAggregate CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentExceptionalAmplitudePair CenteredMomentRankinRadical
open CenteredMomentAmplificationChildInput CenteredMomentGaussEnergy CenteredMomentChildAssembly
open CenteredMomentCommonSupport CenteredMomentMobiusRegroup CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstMixedAllowance CenteredMomentSecondWindowBudget CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance instDecidableEqSumFinOfNatNat_solutions : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev supported (s:Input ι)(R seed:Ideal O)(p:Labels s R seed):=
  commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property

def ColumnBounds (s:Input ι)(R seed:Ideal O)(Z:ℝ)(J₁ J₂:ℕ)(EL ER:Fin 4→ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(n:Fin 4→ℤ):Prop:=
  let C:=p.val.1; let D:=p.val.2; let h:=supported s R seed p
  let F:=fixedPair s.η C D h.1 E 1 1
  let V:=volume s.toData
  let refL:=(F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)
  let refR:=(F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)
  (∀L∈divisorPool (Finset.univ:Finset (columns C D h.2.1 (original s R seed).columns))
    (fun b=>Ideal.span {element C D h.2.1 (original s R seed).columns b}),
    (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
    (commonEnergy (original s R seed) C h.1 (fixedPair s.η C D h.1 E χ χ).left v L
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      ((∑i,refL*EL i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) ∧
  (∀L∈divisorPool (Finset.univ:Finset (columns C D h.2.1 (original s R seed).columns))
    (fun b=>Ideal.span {element C D h.2.1 (original s R seed).columns b}),
    (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
    (commonEnergy (original s R seed) D h.2 (fixedPair s.η C D h.1 E χ χ).right v L
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      ((∑i,refR*ER i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂))

def pairedBudget (J₁ J₂:ℕ)(t:ℝ)(EL ER:Fin 4→ℝ):ℝ:=
  ∑i:Fin 4,∑j:Fin 4,windowBudget J₁ t (EL i)*windowBudget J₂ t (ER j)

def sourceFactor (s:Input ι)(a₁ a₂ K:ℝ):ℝ:=
  (Real.exp (Real.log 4)/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ)

end SevenEighths.CenteredMomentFirstReferenceEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondChildPowerBudget
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEligibleEnergy
open CenteredMomentFirstChildProfileControl CenteredMomentCommonRadialPointwise
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def powers (ε : ℝ) : Fin 4→ℝ := ![1,1/3,ε,0]

def coefficients {wlo whi : ℝ} (N : ℕ) (b b₁ b₂ A : ℝ)
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O)
    (K t ε seedNorm : ℝ) (a : Fin 4→ℝ) : Fin 4→ℝ :=
  ![a 0*(2*(b₁*b₂)*b^N*A^2)*(b^N*b₁*b₂)/seedNorm,
    a 1*exceptionalConstant N b J Q K*p.control S^2*(1+‖t‖)^(2*J)*A^4/seedNorm,
    a 2*4*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2*(1+b^N*whi^2)^(1+ε)/seedNorm,
    a 3*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2]

def sourceCost {wlo whi : ℝ} (s : Input ι) (S : Finset (ℕ×ℕ))
    (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O) (K ε seedNorm : ℝ)
    (a : Fin 4→ℝ) : ℝ :=
    a 0*profileCost s*sourceRadius s/seedNorm+
    a 1*profileFactor S s p J Q K*(CenteredMomentAmplificationChildInput.volume s)^(1/3:ℝ)/seedNorm+
    a 2*(2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*mass s)^2*
      (1+(∏i,s.hi i)*whi*whi)^(1+ε)*(CenteredMomentAmplificationChildInput.volume s)^ε/seedNorm+
    a 3*plainControl s (p.profile 0) (p.profile 1)^2

end SevenEighths.CenteredMomentSecondChildPowerBudget

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalOriginalBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentSecondHeightFamily
open CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

local instance instDecidableEqSumFinOfNatNat_solutions_re2792e_7 {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
def sourceBudget (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
    Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
      (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
      2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*
    ((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*
      frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

end SevenEighths.CenteredMomentSecondExceptionalOriginalBlock

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalBudget
open HeckeFamily CanonicalQuadraticSieve CompletedGauss UniqueFactorizationMonoid
open CenteredMomentSecondExceptionalOriginalBlock CenteredMomentSecondPhysicalLedger
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentForcing CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def profileFactor (s:Input ι)(p:Tests)(J:ℕ)(Q:Ideal O)(K:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*J)*
    p.heightWeight s.t^(2*J)*slotControl s.toData^2*frozenProfile s^2*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

end SevenEighths.CenteredMomentSecondExceptionalBudget

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondFrozenChosen
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSourceLiveColumn
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance instDecidableEqSumFinOfNatNat_solutions : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondOriginalChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondWholeKernel
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair

def canonicalRadial (τ:Character)(Q:Ideal O)(n:Fin 4→ℤ):Radial:=
  sourceRadial (fun z=>z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow τ Q fixedBadMask 1 z)
    ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _z=>ballProfile_nonneg _)

end SevenEighths.CenteredMomentSecondFrozenChosen

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSourceInputReindex
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstAmplificationChoice CenteredMomentOriginalChildEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
variable {α β : Type*} [Fintype α] [Fintype β]
local instance instDecidableEq_solutions_re2792e_7 {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance instDecidableEqSumFinOfNatNat_solutions_re2792e_8 : DecidableEq (α⊕Fin 2) := Classical.decEq _
local instance instDecidableEqSumFinOfNatNat_solutions_1 : DecidableEq (β⊕Fin 2) := Classical.decEq _

def reindex (e : α≃β) (s : Input α) : Input β where
  η := s.η
  m := s.m
  A := s.A
  t := s.t
  slots := fun i=>s.slots (e.symm i)
  prime := fun i=>s.prime (e.symm i)
  ν := fun i=>s.ν (e.symm i)
  W := fun i=>s.W (e.symm i)
  lo := fun i=>s.lo (e.symm i)
  hi := fun i=>s.hi (e.symm i)
  P := fun i=>s.P (e.symm i)
  lo_pos := fun i=>s.lo_pos (e.symm i)
  P_pos := fun i=>s.P_pos (e.symm i)
  support := fun i=>s.support (e.symm i)
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  M := fun i=>s.M (e.symm i)
  M_ge_one := fun i=>s.M_ge_one (e.symm i)
  coefficient_bound := fun i=>s.coefficient_bound (e.symm i)
  b₁ := s.b₁
  b₂ := s.b₂
  support₁ := s.support₁
  support₂ := s.support₂
  X₁_pos := s.X₁_pos
  X₂_pos := s.X₂_pos
  Y₁_pos := s.Y₁_pos
  Y₂_pos := s.Y₂_pos
  same_product := s.same_product
  rows := s.rows
  weight := s.weight
  weight_nonneg := s.weight_nonneg
  plain₁ := s.plain₁
  plain₂ := s.plain₂
  plain₁_ne := s.plain₁_ne
  plain₂_ne := s.plain₂_ne
  coverage₁ := s.coverage₁
  coverage₂ := s.coverage₂
  ν_bound := fun i=>s.ν_bound (e.symm i)
  W_bound := fun i=>s.W_bound (e.symm i)
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := fun i=>s.lower_le (e.symm i)
  upper_ge := fun i=>s.upper_ge (e.symm i)

def tupleMap (e : α≃β) : Tuple α≃Tuple β :=
  (e.sumCongr (Equiv.refl (Fin 2))).arrowCongr (Equiv.refl (Ideal O))

end SevenEighths.CenteredMomentSourceInputReindex

end

end OAI
end


