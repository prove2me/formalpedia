-- Prove2me | Definitions.Def_OAIHecke78B028
-- name    : OAIHecke78B028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T02:20:20.438071+00:00
-- url     : https://prove2.me/theorems/9013fef3-571f-4da4-8b41-26dd01ec6129
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 29 of 29
-- statement:
--   Definitions bundle 29 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B027` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Moments.SecondSectorFrequency`, `PrimeRows.CubeFiniteError`, `Detector.LowPeriodFilter`, `Reflection.Projections`, `Reflection.NormalizedColumns`, `Reflection.Energy`, `Reflection.ExtractedKernel`, `Reflection.ActualWeightedEnergy`, `Reflection.WeightedSourceSum`, `Reflection.Denominator`, `Reflection.KernelActual`, `Reflection.PhysicalIntegral`, `Reflection.Surviving`, `Reflection.SectorData`, `Reflection.FullRaw`, `Reflection.FullDyadic`, `Reflection.ShellRows`, `Reflection.WholeRow`, `Reflection.WholePair`, `Detector.LowTruePeriodPuncture`, `Reflection.FamilyTail`, `Reflection.SourcePhysical`, `Moments.NaturalFixedRaySourceFreeExceptional`, `Detector.DetectorPlainMarkedFineField`, `Moments.CommonLinearSource`, `Moments.CommonLinearNormalization`, `Moments.CommonPairedSource`, `Moments.CommonWindowColumn`, `Moments.ExceptionalHeight`, `Moments.SecondExceptionalPairBound`, `Moments.FirstSectorLocalization`, `Moments.FirstRetainedSector`, `Moments.FirstRetainedPhysical`, `Moments.FirstPhysicalSourceOriginalData`, `Moments.FirstPhysicalSourceWindowCanonical`, `Moments.SecondNonexceptionalScalar`, `Moments.SecondCapacitySourceShift`, `Moments.FirstAmplifiedCapacityCommon`, `Energy.ChildEnvelopeFitting`, `Energy.FirstRawScaleAdmission`, `Energy.ZeroGrowth`, `Inversion.InitialOriginalHeight`, `Moments.FiniteProfileExceptionalCommonHeight`, `Moments.FirstAllocationGaussEnergy`, `Moments.FirstAmplifiedFourCoefficients`, `Moments.FirstPhysicalDyadicRows`, `Moments.FirstDivisorCommonBound`, `Moments.FirstPhysicalActiveDictionary`, `Moments.SecondReferenceNormalization`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B028

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Moments.SecondSectorFrequency
  PrimeRows.CubeFiniteError
  Detector.LowPeriodFilter
  Reflection.Projections
  Reflection.NormalizedColumns
  Reflection.Energy
  Reflection.ExtractedKernel
  Reflection.ActualWeightedEnergy
  Reflection.WeightedSourceSum
  Reflection.Denominator
  Reflection.KernelActual
  Reflection.PhysicalIntegral
  Reflection.Surviving
  Reflection.SectorData
  Reflection.FullRaw
  Reflection.FullDyadic
  Reflection.ShellRows
  Reflection.WholeRow
  Reflection.WholePair
  Detector.LowTruePeriodPuncture
  Reflection.FamilyTail
  Reflection.SourcePhysical
  Moments.NaturalFixedRaySourceFreeExceptional
  Detector.DetectorPlainMarkedFineField
  Moments.CommonLinearSource
  Moments.CommonLinearNormalization
  Moments.CommonPairedSource
  Moments.CommonWindowColumn
  Moments.ExceptionalHeight
  Moments.SecondExceptionalPairBound
  Moments.FirstSectorLocalization
  Moments.FirstRetainedSector
  Moments.FirstRetainedPhysical
  Moments.FirstPhysicalSourceOriginalData
  Moments.FirstPhysicalSourceWindowCanonical
  Moments.SecondNonexceptionalScalar
  Moments.SecondCapacitySourceShift
  Moments.FirstAmplifiedCapacityCommon
  Energy.ChildEnvelopeFitting
  Energy.FirstRawScaleAdmission
  Energy.ZeroGrowth
  Inversion.InitialOriginalHeight
  Moments.FiniteProfileExceptionalCommonHeight
  Moments.FirstAllocationGaussEnergy
  Moments.FirstAmplifiedFourCoefficients
  Moments.FirstPhysicalDyadicRows
  Moments.FirstDivisorCommonBound
  Moments.FirstPhysicalActiveDictionary
  Moments.SecondReferenceNormalization
-/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorFrequency
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSectorColumns CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLedger CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

def sectorFrequency (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (F : O→Ideal O→Ideal O→ℂ) (j : O) : ℂ :=
  ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
    (if IsCoprime (I:Ideal O) (J:Ideal O) then
      idealCorrelation (C*I) (D*J)
        ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
        ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) j
      else 0)*((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*F j I J

end SevenEighths.CenteredMomentSecondSectorFrequency

end

end OAI
end

section

namespace OAI
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def finiteCentralCubeRows {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z e : ℝ) (a H : FreeRow→ℝ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
    centralCubeIntegral S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
      η u W0 W1 X Y Z (a u) e (H u)

end SevenEighths.ProbeHighRowFamily

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

def lowPeriodIdeal (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : Id :=
  lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS)*Ideal.span {(72:O)}

def lowPeriodPrimeList (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) : Finset PrimeIdeal :=
  T.filter (fun P=>IsCoprime P.val (lowPeriodIdeal η S hS))

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {a c : Eis} {mode : Bool}

def actualRowPhase (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) : ℂ :=
  sourceRowPhase s (F.sum (PrimeFamily.residual K hK)).generator_ne_zero
    (F.sum (PrimeFamily.residual K hK)).generator_good (Sum.elim jF (fun _ => 1))
    (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m

def actualSlotPhase (F : PrimeFamily φ) (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) : ℂ :=
  sourceSlotPhase s (F.sum S).generator_ne_zero (F.sum S).generator_good
    (Sum.elim jF (fun _ => 0)) (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def actualFrozenPhase (F : PrimeFamily φ) (jF : φ → ℕ) (κ : ℂ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) : ℂ :=
  star κ * frozenCore F.generator_ne_zero F.generator_good c jF Finset.univ *
    ramifiedBlock F.generator_good jF Finset.univ
      (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)

def normalizedFrozenColumn (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) : ℂ :=
  (frozenBranchScale F jF e : ℂ)⁻¹ * frozenBranchColumn F jF e A n b

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def actualRowPhaseExtension (F : PrimeFamily φ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (u : Eisˣ) (m : ℕ) (K : Ideal Eis) : ℂ :=
  if hK : Admissible K then actualRowPhase F K hK jF s u m else 0

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def extractedRowFactor (D1 D2 K : Ideal Eis) : ℂ := quadraticRow K (primaryGenerator (D1*D2))
def extractedSlotFactor (D1 D2 P : Ideal Eis) : ℂ :=
  inverseCubicKernel P D1 * (if IsCoprime P D2 then 1 else 0)

def extractedFrozenColumn {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
    (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) : ℂ :=
  normalizedFrozenColumn F jF e A ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def weightedReflectedBranchHybridRow (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (S : Ideal Eis → PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis → Ideal Eis → ℂ)
    (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ)
    (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis) : ℂ :=
  ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF κ s u m*
    actualRowPhaseExtension F jF s u m K*r K)*
    hybridRow Pset nset bset (fun P => actualSlotPhase F (S P) jF s u m*aw P)
      (frozenBranchColumn F jF e (fun n b => A n b*w n b)) K

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ ι : Type*} [Fintype φ] [Fintype σ] [Fintype ι]
variable {N a c : Eis} {mode : Bool}

def weightedPhysicalReflectedRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ) : ℂ :=
  ∑ P : Pset, ∑ n ∈ nset, ∑ b ∈ bset,
    r K*aw P.val*w n b*(if h : IsCoprime K P.val then
      actualMixedCoefficient F K hK (S P.val) jF (D P h) s hc u m n b else 0)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open InverseReflectedNormalization InverseKernelSourceUniform
noncomputable section
variable {φ : Type*} [Fintype φ]

def extractedOutsideScalar (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (r U B R : ℝ) : ℝ :=
  smallScalar R / (r*Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*U)*
    ((Ideal.absNorm (frozenExtracted F jF e 2):ℝ)*B))

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def actualKernelCoefficient (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (m : ℕ) (X : ℝ) : ℝ :=
  fixedKernelCoefficient X (sourceCuspScale s.index) (ramifiedScale 1 completedRamifiedStep m)
    (Ideal.span {c}*(∏ i, F.ideal i)) 1 1

def actualKernelSourceTerm (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (windows : Fin 4→ℝ→ℂ)
    (QK QP Qn Qb : ℝ) (W : ℝ→ℂ) (θ X : ℝ) : ℂ :=
  actualMixedCoefficient F K hK S jF D s hc u m n b *
    ((∏ i, windows i (kernelLogCoordinates QK QP Qn Qb (Ideal.absNorm K:ℝ)
      (Ideal.absNorm (∏ i, S.ideal i):ℝ) (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ) i)) /
      ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ):ℝ):ℂ) *
      CubicReflectionKernel.paperKernel (Vstar (CompletedHeight.normTwistedSource W θ))
        ((X/(27*(sourceCuspScale s.index)^2*
          (Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep m)^3*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3))

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def weightedFinitePhysicalKernelRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ)
    (W : ℝ→ℂ) (θ X : ℝ) (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ) : ℂ :=
  ∑ x : CoprimeSourceIndex K Pset nset bset,
    (r₀ K*aw₀ x.1.val.val*w₀ x.2.1.val x.2.2.val)*actualKernelSourceTerm F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc
      u m x.2.1.val x.2.2.val windows QK QP Qn Qb W θ X

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {a c : Eis} {mode : Bool}

def survivingFrozenBranches (F : PrimeFamily φ) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) : Finset (φ→Fin 3) :=
  Finset.univ.filter (fun e => ∃ n∈nset, ∃ b∈bset, frozenBranchColumn F jF e A n b≠0)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

structure SectorArithmetic (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows, Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0) where
  referenceIndex : Type (max u v)
  [referenceFintype : Fintype referenceIndex]
  referencePrimes : PrimeFamily referenceIndex
  referenceArithmetic : ControlledStratumArithmetic referencePrimes.generator N a c mode
  completion : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
    ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode
  fixedFactor_eq : ∀ K P hp, (completion K P hp).fixedFactor=referenceArithmetic.fixedFactor
  cuspColumn_eq : ∀ K P hp u m n b,
    actualCuspColumn (completion K P hp) s hc u m n b=actualCuspColumn referenceArithmetic s hc u m n b

attribute [instance] SectorArithmetic.referenceFintype

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def thetaRawIndex (t : ThetaFullIndex) : Eisˣ×RawTailIndex :=
  (t.1,t.2.1,⟨t.2.2.1.val,t.2.2.1.property.1.ne_zero⟩,
    ⟨t.2.2.2.val,primaryGenerator_ne_zero_ideal _ t.2.2.2.property⟩)

def literalRawScale (G : PrimeFamily ι)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (X : ℝ) : ℝ :=
  X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c*∏ i,G.generator i}):ℝ)^2)

def literalRawSeries (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) (t : Eisˣ×RawTailIndex) : ℂ :=
  rawDualKernelTerm (Vstar W) (literalRawScale G s X) 1 completedRamifiedStep
    (literalRawCoefficient G D s hc j S t.1) t.2

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def literalDyadicBlock (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) (u : Eisˣ) (i : ℕ×ℕ×ℕ) : ℂ :=
  ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
    literalRawSeries G D s hc j S W X
      (u,i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def literalDyadicRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) : ℂ :=
  ∑ P : {P : Pset // IsCoprime K P.val}, r K*aw P.val.val*
    literalDyadicBlock (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc
      (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) X u i

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def literalWholeRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) : ℂ :=
  ∑ P : {P : Pset // IsCoprime K P.val}, r K*aw P.val.val*
    mixedReflectedValue (D P.val P.property) s (F.reflected K hK (S P.val.val)).generator_ne_zero hc
      (F.reflected K hK (S P.val.val)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def literalPairEntry (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (K P : Ideal Eis) : ℂ :=
  if hK:K∈rows then if hP:P∈Pset then if hp:IsCoprime K P then
    r K*aw P*mixedReflectedValue (D ⟨K,hK⟩ ⟨P,hP⟩ hp) s
      (F.reflected K (hrows K hK) (S P)).generator_ne_zero hc
      (F.reflected K (hrows K hK) (S P)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X
  else 0 else 0 else 0

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss RayFourExpansion SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowTruePeriodGenerator (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : O := ConcretePrimeRowBridge.idealGenerator (lowPeriodIdeal η S hS)

def lowReflectionPeriod (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : Id :=
  lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS)

def lowReflectionMask (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : O :=
  (calibrationForSet S hS).generator*lowTruePeriodGenerator η S hS

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def familyRawScale (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (X QK QP : ℝ) : ℝ :=
  actualKernelCoefficient F s 0 X/(QK^2*QP^2)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily τ) (FF : φ→Ideal Eis) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (lists : σ→Finset (Ideal Eis)) (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) (T : Finset σ)

abbrev OriginalSplitCompletion :=
    ∀ K : rows,∀ _b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val,
      ∀ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator N a c mode

def originalInactivePhysical
    (D : OriginalSplitCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G FF rows hrows lists hmax hgood T)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) (K : rows) : ℂ :=
    ∑ b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
      ∑ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
        (∏ i : T,w i.val (p.val i))*mixedReflectedValue (D K b p) s
        (G.reflected K.val (hrows K.val K.property)
          (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val K.property)
          (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
        (reflectedExponent jF) (slotIndices τ (PrimeIndex K.val) T) W X
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily UniqueFactorizationMonoid
open CenteredMomentDetectorDictionary CenteredExceptionalProfile CenteredExceptionalCount
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

variable {Δ : ℝ} {D : Parameters.HighData Δ}

def sourceExceptionalBound (F : ProbeFinalAssembly.SourceData D) (η : Character) : ℕ :=
  HeckeExceptionalRows.bound (normalizedFactors (internalQ (sourceFixedIdeal F) η)).toFinset

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.ProbeDetectorPlainMarkedFineField
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles ProbeHighRowFamily ProbeFinalAssembly
open QuadraticInitialBound CenteredMomentDetectorDictionary
open CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainMomentParameters CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
local notation "O"=>HeckeFamily.O

def PositiveFineSourceInput {Δ:ℝ}{D:Parameters.HighData Δ}(S:SourceData D)(mesh:ℝ):Prop:=
  ∀bΦ:ℝ,0<bΦ→∃degree:ℕ,∃seminorms:Finset (ℕ×ℕ),
    ∀η₀:Character,∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,
      PositiveAt (α:=Fin D.N) S.modulus ⊤ le_top (fun x=>conj (S.W x))
        2 (1/4) (9/4) bΦ 0 1 mesh (33/50) (33/50) 2 (stageError D)
        (kappaPlain D) U η₀ (sourceFixedIdeal S) degree seminorms C

end SevenEighths.ProbeDetectorPlainMarkedFineField

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLinearSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentEligibleEnergy
open CenteredMomentSourceRectangle
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentOriginalChildEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedDomain
open CenteredMomentAmplificationLiveMask CenteredMomentExceptionalMaskedSource
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance instDecidableEqSumFinOfNatNat_solutions : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def sourceColumn (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(z:O):ℂ:=
  let Q:=residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))
  let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  rowPolynomial Finset.univ (sourceGenerator Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then β (C*I) else 0)*heightCoeff s.η s.t I) z

def liveColumn (s:Input ι)(C R L:Ideal O)(B:actualAllocations s.pools C)(z:O):ℂ:=
  let S:=liveBox s.pools B.val (alloc_ne s C B)
  rowPolynomial Finset.univ (sourceGenerator (finiteColumns S))
    (fun I:supportedColumns (finiteColumns S)=>finiteColumnCoefficient S
      (maskedLiveProfile B.val C R L s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I*
        heightCoeff s.η s.t I) z

end SevenEighths.CenteredMomentCommonLinearSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLinearNormalization
open HeckeFamily CenteredMomentCommonLinearSource CenteredMomentCommonRadialData
open CenteredMomentCommonRawScale CenteredMomentEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAmplitudePair
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def commonScalar (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):ℂ:=
  (Real.sqrt (rawReduction B.val s.P):ℂ)⁻¹*frozenCoefficient B.val C R s.ν s.W s.P

end SevenEighths.CenteredMomentCommonLinearNormalization

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonPairedSource
open HeckeFamily UniqueFactorizationMonoid CanonicalQuadraticSieve
open CenteredMomentCommonLinearSource CenteredMomentCommonLinearNormalization
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def normalizedColumn (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(z:O):ℂ:=
  (Real.sqrt (volume s.toData):ℂ)⁻¹*sourceColumn s C hC R seed L z

end SevenEighths.CenteredMomentCommonPairedSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentCommonWindowColumn
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonPairedSource
open CenteredMomentCommonLinearSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentSmooth
local notation "O" => HeckeFamily.O
local instance instDecidableEqSumFinOfNatNat_solutions {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def columns (s:Input ι)(C:Ideal O)(hC:Supported C):Finset (Ideal O):=
  residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))

def coefficient (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (I:supportedColumns (columns s C hC)):ℂ:=
  (Real.sqrt (volume s.toData):ℂ)⁻¹*
    (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then
      finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I) else 0)

def windowColumn (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
    (fun I=>coefficient s C hC R seed L I*heightCoeff η t I*
      columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) z

end SevenEighths.CenteredMomentCommonWindowColumn

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalHeight
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentCommonRadialData
open CenteredMomentHeckeWindowEnergy HeckeFamily CenteredMomentAllocatedDetectorAmplitude
universe u

def cost (p:Tests)(t θ:ℝ):ℝ:=‖p.height 0‖+‖p.height 1‖+heightCost t θ

def mass {ι κ:Type u}[Fintype ι][Fintype κ]
    (s:Input ι)(v:Input κ)(p q:Tests)(t₁ t₂ θ₁ θ₂:ℝ)(J:ℕ):ℝ:=
  cost p t₁ θ₁^J*cost q t₂ θ₂^J*slotControl s.toData*slotControl v.toData*
    Real.sqrt (volume s.toData)*Real.sqrt (volume v.toData)

end SevenEighths.CenteredMomentExceptionalHeight

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalPairBound
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary
local notation "O" => HeckeFamily.O
local instance instDecidableEqSumFinOfNatNat_solutions {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def originalPair (s:Input ι)(η:Character)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y:ℝ)(Ds:Finset (Ideal O))(rows:Finset O):ℝ:=
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
        (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
          (movingCoefficient A (sectorElement C hC.1 S)
            (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
          columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) w) z‖*
      ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*
          star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) w)) (-z)‖)

end SevenEighths.CenteredMomentSecondExceptionalPairBound

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorLocalization
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentFirstTailAggregate
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentFirstLocalization

def retainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalRetainedTerm I J hI hJ E W K
    (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ

def discardedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K
    (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ

def retainedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      retainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ

def discardedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      discardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ

end SevenEighths.CenteredMomentFirstSectorLocalization

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedSector
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentFirstSectorLocalization CenteredMomentFirstCommonFourierTransport
open CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentCompleteCommon CenteredMomentSecondSectorColumns
open CenteredMomentHeckeColumnWindow
open CenteredMomentSupport CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

def retainedKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  if hI : Supported I then if hJ : Supported J then CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ else 0 else 0

end SevenEighths.CenteredMomentFirstRetainedSector

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedPhysical
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform CenteredMomentSourceRow
open CenteredMomentFirstRetainedSector CenteredMomentFirstCommonFourierTransport
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource
open CenteredMomentSupportedCorrelation CenteredMomentHeckeExpansion CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentFirstReduced
local notation "O"=>ActualEisensteinCubic.O

def fixedRetainedSector (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
          fixedRetainedTerm C D hC (element C C hC.1 S a) (element C D hD.1 S b)
            (element_supported C C hC.1 S a) (element_supported C D hD.1 S b) E W K X Z ξ
      else 0

end SevenEighths.CenteredMomentFirstRetainedPhysical

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationLiveMask CenteredMomentLiveDomain CenteredMomentRemainingBox
open CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentSecondHeightFamily CenteredMomentOriginalChildEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance instDecidableEqSumFinOfNatNat_solutions : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def allocatedData (D:OriginalData ι)(C L:Ideal O)(B:actualAllocations D.S C):
    OriginalData (liveIndices B.val) where
  S:=remainingSets B.val (fun i=>residualPool (B.val i)
    ((allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1 i) (D.S i))
  R:=D.R*C
  s:=L
  nu:=fun i=>D.nu i.val
  slot:=fun i=>D.slot i.val
  lengths:=fun i=>D.lengths i.val
  W₁:=D.W₁
  W₂:=D.W₂
  X₁:=D.X₁
  X₂:=D.X₂
  Y₁:=D.Y₁
  Y₂:=D.Y₂
  B₁:=D.B₁*B.val (Sum.inr 0)
  B₂:=D.B₂*B.val (Sum.inr 1)

def commonGauss (D:OriginalData ι)(C:Ideal O)(hC:Supported C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):ℂ:=
  let Q:=residualPool C hC.1 D.columns
  gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then D.beta (C*I) else 0)*heightCoeff τ t I) z

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSectorColumns
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport RayFourExpansion IdealMobiusDivisorSum
open FourierBridge
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]

def leftWindowChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C C hC.1 s.columns) (element_supported C C hC.1 s.columns)
    (fun I=>divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=>coefficient η m 1 t s.beta C a*leftCoefficient e r ρ (element C C hC.1 s.columns a)) χ I*
      columnPhase V (Real.log (‖eisEmbedding (element C C hC.1 s.columns I)‖^2/X)) θ) z

def rightWindowChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C D hD.1 s.columns) (element_supported C D hD.1 s.columns)
    (fun I=>divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=>coefficient η m 1 t s.beta D a*rightCoefficient e r ρ (element C D hD.1 s.columns a)) χ I*
      star (columnPhase V (Real.log (‖eisEmbedding (element C D hD.1 s.columns I)‖^2/X)) θ)) z

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondNonexceptionalScalar
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization
open CenteredMomentSecondRadicalBudget
open CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O

def childEnvelope (η:Character)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ :=
  (fixedFactor:ℝ)*η.modulus.absNorm*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)

end SevenEighths.CenteredMomentSecondNonexceptionalScalar

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondCapacitySourceShift
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSectorLocalization
open CenteredMomentSecondRadicalBudget
open CenteredMomentSupport CenteredMomentSecondWholeKernel ConcretePrimeRowBridge CenteredMomentSourceRow
local notation "O"=>HeckeFamily.O

def adjustedEnvelopeRef (qref:ℝ)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  (fixedFactor:ℝ)*qref*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)*
    max 1 (1/(dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))))

end SevenEighths.CenteredMomentSecondCapacitySourceShift

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn
open CenteredMomentSecondCapacitySourceShift
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondRadicalBudget
open CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentFirstScale
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

local instance instDecidableEq_solutions_rcac458_1 {κ:Type*}:DecidableEq κ:=Classical.decEq _
def envelopeRef (qref:ℝ)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  (fixedFactor:ℝ)*qref*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)

def ratioPenalty (n:Fin 4→ℤ):ℝ:=
  max 1 (1/(dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))))

end SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyChildEnvelopeFitting
open HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O" => HeckeFamily.O

def coefficient {a b:ℝ}(Cc C₀ C₁:ℝ)(p:Profiles a b)(T:Finset (ℕ×ℕ))
    (height:ℝ)(degree:ℕ)(Z exponent:ℝ):ℝ:=
  Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
    (p.control T)^2*(1+height)^degree*Z^exponent

end SevenEighths.CenteredMomentEnergyChildEnvelopeFitting

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α]

local instance instDecidableEq_solutions_rcac458_2 {ι:Type*}:DecidableEq ι:=Classical.decEq _
def parentLower (s:Input α)(Z:ℝ):ℝ:=
  min (min (Real.logb Z s.X₁) (Real.logb Z s.X₂))
    (min (Real.logb Z s.Y₁) (Real.logb Z s.Y₂))

end SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowth
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

def ZeroGrowthAt (Q : Ideal O) (a b bΦ Bmask L M ε Z : ℝ)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalState Z Bmask bΦ, s.fixedModulus = Q → s.width ≤ M →
  ∀ p : Profiles a b, ∀ t X₁ X₂ : ℝ,
    0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    s.plainEnergy p t X₁ X₂ ≤
      C * diagonalControl s.radial.profile * (p.control S) ^ 2 *
        (1 + ‖t‖) ^ degree *
        Z ^ (max s.width (length Z X₁ + length Z X₂) + ε)

end SevenEighths.CenteredMomentEnergyZeroGrowth

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical SchwartzMap ContDiff FourierTransform
namespace SevenEighths.InverseInitialOriginalHeight
open InverseMoment InverseInitialProfile InverseInitialProfileBounds FourierBridge
open JointLogSeparation CompletedHeight

theorem child_eq_normTwisted (W:ℝ→ℂ)(θ:ℝ):childLogTest W θ=normTwistedSource W θ:=by
  rw [childLogTest_eq_clipped]
  funext x
  simp only [clippedSource,normTwistedSource,one_mul]

theorem child_support (W:ℝ→ℂ)(θ:ℝ):
    Function.support (childLogTest W θ)⊆Function.support W:=by
  rw [child_eq_normTwisted]
  exact normTwistedSource_support W θ

theorem child_smooth (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(θ:ℝ):
    ContDiff ℝ ∞ (childLogTest W θ):=by
  rw [child_eq_normTwisted]
  exact CanonicalRowCompletion.normTwistedSource_contDiff W a b ha hs hW θ

end SevenEighths.InverseInitialOriginalHeight

end

end OAI
end

section

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentExceptionalAmplitudePair CenteredMomentCommonRadialData
open CenteredMomentHeckeWindowEnergy
open HeckeFamily CenteredMomentAllocatedDetectorAmplitude CenteredMomentFiniteProfileExceptional
universe u

def mass {lo hi:ℝ} (R:Finset (ℕ×ℕ)) {ι κ:Type u}[Fintype ι][Fintype κ]
    (s:Input ι)(v:Input κ)(p q:Profiles lo hi)(t₁ t₂ θ₁ θ₂:ℝ)(J:ℕ):ℝ:=
  p.control R*q.control R*heightCost t₁ θ₁^J*heightCost t₂ θ₂^J*
    slotControl s.toData*slotControl v.toData*
    Real.sqrt (volume s.toData)*Real.sqrt (volume v.toData)

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAllocationGaussEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentSourceRow
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentCommonRawScale CenteredMomentAddedZeroUniform
open CenteredMomentGaussEnergy
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

local instance instDecidableEqSumFinOfNatNat_solutions_rcac458_1 : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
def commonEnergy (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, ‖commonGauss D C hC τ t L z‖^2 *
    (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re

def allocatedEnergy (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (sourceGaussEnergy (allocatedData D C L B).columns
    (allocatedData D C L B).beta (heightCoeff τ t) W K).re

def rawVolume (D : OriginalData ι) : ℝ :=
  (D.X₁*D.X₂/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂)) * ∏ i,D.lengths i

def frozenControl (B : Tuple ι) (M : ι → ℝ) : ℝ :=
  ∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),M i

end SevenEighths.CenteredMomentFirstAllocationGaussEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedAllowance
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization
open CenteredMomentSuccessorPaidParameters
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

def reference (q V C Z allowance:ℝ):ℝ:=q*(V/C)^2*Z^allowance

def mainCores (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ):Fin 4→ℝ:=
  ![(V/C)*q*(V/C)*Z^(ell+deficit/6+paid)/reference q V C Z allowance,
    (V/C)*(V/C)^((1:ℝ)/3)*Kmain^((5:ℝ)/6)*Z^(-2*max r 0/3)/reference q V C Z allowance,
    (V/C)*Kmain*(V/C)^eps/reference q V C Z allowance,
    (V/C)*Kmain*Z^(-saving)/reference q V C Z allowance]

def errorCores (p:O)(k:ℕ)(q V C Z allowance Kerror deficit paid eps saving r:ℝ):Fin 4→ℝ:=
  ![(V/C)*localErrorCost p (k-1)*q*Z^(errorMoving p Z k)*
      (V/C/(normValue p)^k)*Z^(errorRemoval p Z k+deficit/6+paid)/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*(V/C/(normValue p)^k)^((1:ℝ)/3)*
      Kerror^((5:ℝ)/6)*Z^(-2*max r 0/3)/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*Kerror*(V/C/(normValue p)^k)^eps/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*Kerror*Z^(-saving)/reference q V C Z allowance]

def lossVector (sigma delta reserve paid eps Mcap saving:ℝ):Fin 4→ℝ:=
  ![paid,3*sigma/2+5*(delta+reserve)/6,
    2*sigma+delta+reserve+eps*Mcap,2*sigma+delta+reserve-saving]

def averagedCoefficients (P:Finset (Ideal O))(mainFactor:ℝ)(H main:Fin 4→ℝ)
    (error:elementPool P→Fin 3→Ray→Fin 4→ℝ):Fin 4→ℝ:=fun j=>
  (56/(P.card:ℝ))*(mainFactor*H j*main j+
    ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)

def sourceCoefficients (P:Finset (Ideal O))(mainFactor:ℝ)(amain:Fin 4→ℝ)
    (aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ):Fin 4→ℝ:=fun j=>
  (56/(P.card:ℝ))*(mainFactor*amain j+
    ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*localErrorCost p (errorIndex i)*
      ∑χ:Ray,aerror p i χ j*((normValue p)^(errorIndex i+1))^(-alpha j))

def mainPowers (q Z Kmain ell deficit paid saving r:ℝ):Fin 4→ℝ:=
  ![q*Z^(ell+deficit/6+paid),Kmain^((5:ℝ)/6)*Z^(-2*max r 0/3),Kmain,Kmain*Z^(-saving)]

def errorPowers (p:O)(k:ℕ)(q Z Kerror deficit paid saving r:ℝ):Fin 4→ℝ:=
  ![q*Z^(errorMoving p Z k)*Z^(errorRemoval p Z k+deficit/6+paid),
    Kerror^((5:ℝ)/6)*Z^(-2*max r 0/3),Kerror,Kerror*Z^(-saving)]

end SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicRows
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentRowNorm
local notation "O" => HeckeFamily.O

def activeRows (rows : Finset O) (n : Fin 4→ℤ) : Finset O :=
  rows.filter (fun h => h∈dyadRows (n 1))

end SevenEighths.CenteredMomentFirstPhysicalDyadicRows

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstDivisorCommonBound
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentChildAssembly
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSecondWindowBudget
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentMobiusRegroup
open CenteredMomentSecondHeightFamily
local notation "O"=>ActualEisensteinCubic.O

def pairMajorant {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : α→ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑i∈S,∑j∈S,b i*b j*‖∑'z:O,(gaussRow (a i) (ha i) z*star (gaussRow (a j) (ha j) z))*
    W (‖eisEmbedding z‖^2/K)‖

variable {ι : Type*} [Fintype ι]

def coarse (s : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  pairMajorant Finset.univ (sourceGenerator (residualPool C hC.1 s.columns))
    (sourceGenerator_supported _) (fun I:supportedColumns (residualPool C hC.1 s.columns)=>
      ‖if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then s.beta (C*I) else 0‖) W K

universe u

end SevenEighths.CenteredMomentFirstDivisorCommonBound

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalActiveDictionary
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentPrimitive IdealMobiusDivisorSum
open CenteredMomentFirstPhysicalSource CenteredMomentActiveSource
local notation "O" => HeckeFamily.O

lemma primary_supported (I : Ideal O) (hI : Supported I) :
    Supported (Ideal.span {CompletedGauss.primaryGenerator I}) := by
  rw [primary_span_supported I hI]
  exact hI

def physicalTerm (η : Character) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) : ℂ :=
  if hI : Supported I then if hJ : Supported J then
    let na:=CompletedGauss.primaryGenerator I
    let nb:=CompletedGauss.primaryGenerator J
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
    let k:=K/‖eisEmbedding e‖^2
    let r:=activeConductor C D
    if IsCoprime I J then
      (tripleRow na nb r (supportedModulusCharacter na (primary_supported I hI))
        (supportedModulusCharacter nb (primary_supported J hJ))⁻¹ (activeFunction C D hC) e *
      ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
      tripleFourier na nb r
        (supported_element_ne_zero _ (primary_supported I hI))
        (supported_element_ne_zero _ (primary_supported J hJ))
        (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (primary_supported I hI))
        (supportedModulusCharacter nb (primary_supported J hJ))⁻¹ (activeFunction C D hC) h)*
      (coefficient η m A t β C I*star (coefficient η m A t β D J))*
      windows V (k/‖eisEmbedding r‖^2) (‖eisEmbedding h‖^2)
        (‖eisEmbedding na‖^2) (‖eisEmbedding nb‖^2) K₀ H₀ A₀ B₀*
      EisensteinSchwartzPoisson.paperRadialFourier W
        (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
    else 0
  else 0 else 0

variable {ι : Type*} [Fintype ι]
local instance instDecidableEqSumFinOfNatNat_solutions : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
open CenteredMomentCommonRadialData
open CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentLogDyadic

end SevenEighths.CenteredMomentFirstPhysicalActiveDictionary

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondReferenceNormalization
open HeckeFamily CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondNonexceptionalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentSectorLocalization CenteredMomentSecondSourcePowerDescent
open CenteredMomentSecondSourceSeededPowerDescent
local notation "O"=>HeckeFamily.O

def referenceEnvelope (qref:ℝ)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  (fixedFactor:ℝ)*qref*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)

end SevenEighths.CenteredMomentSecondReferenceNormalization

end

end OAI
end


