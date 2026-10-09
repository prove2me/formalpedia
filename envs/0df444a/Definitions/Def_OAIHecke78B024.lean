-- Prove2me | Definitions.Def_OAIHecke78B024
-- name    : OAIHecke78B024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T02:11:51.35132+00:00
-- url     : https://prove2.me/theorems/4e4a86f1-4b36-4e0c-be24-c9e693d7f540
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 25 of 29
-- statement:
--   Definitions bundle 25 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B022` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `GaussSum.FixedRayFibers`, `GaussSum.ResidualEquivalence`, `RowCompletion.RowAmplitudes`, `Descent.ActiveCusp`, `Descent.ReflectedDual`, `Reflection.Coefficient`, `Reflection.Rows`, `Reflection.Actual`, `Reflection.Columns`, `Reflection.MarkedRow`, `Reflection.MarkedSource`, `Reflection.MarkedActualSource`, `Reflection.MarkedFiber`, `Reflection.OriginalMask`, `Reflection.TupleFamily`, `Reflection.SlotCoefficients`, `Reflection.CubeSlots`, `Reflection.RawCoefficient`, `Reflection.Pullback`, `Reflection.CompletedFiberSource`, `Moments.HeckeVolume`, `Moments.HeckeCancellation`, `Moments.FirstCanonicalFamily`, `Moments.FirstIdealFamily`, `Descent.CanonicalEnergyExistenceData`, `Detector.RowRadicalConductor`, `Detector.CentralRepeatedProduct`, `Hecke.InverseAmplificationPrimePool`, `Hecke.DetectorRawFiber`, `Hecke.DetectorFiberPartition`, `Detector.LowPeriod`, `Detector.LowCompletion`, `Detector.LowGramArithmetic`, `Detector.FinalAssemblyData`, `Dictionary.InverseMarkedReferenceFiber`, `Dictionary.InverseRawInitialGates`, `Dictionary.InverseMarkedReferenceDeleted`, `Dictionary.InverseRawInitialEnergy`, `Moments.FirstSectorTransform`, `Moments.CommonAllocationBox`, `Moments.SourceLiveColumn`, `Moments.SecondSourceEnergy`, `Moments.SecondSectorColumns`, `Moments.SecondCanonical`, `Moments.SecondCanonicalFrequency`, `Moments.SecondCanonicalNonunit`, `Moments.FirstScale`, `Moments.FirstDiscardedEnergy`, `Moments.FirstTailAggregate`, `Hecke.MaskDescent`, `Moments.FixedRowMask`, `Moments.RestrictedEnergy`, `Moments.RestrictedSource`, `Moments.SourceRectangle`, `Moments.CommonRadialData`, `Energy.State`, `Moments.FirstLocalization`, `Moments.DetectorDictionaryFiber`, `Moments.NaturalFixedRaySourceFixedIdeal`, `Energy.Bands`, `Energy.BandMonotonicity`, `Moments.AmplificationEnergy`, `Moments.AmplificationSourceDomain`, `Moments.FirstAmplificationChoice`, `Moments.DetectorPlainSource`, `Moments.FirstCommonTransport`, `Moments.FirstCommonFourierTransport`, `Moments.FirstPhysicalSource`, `Moments.SecondActiveCount`, `Energy.ReferenceState`, `Moments.SecondRetainedAggregate`, `Moments.ExceptionalSourceShell`, `Energy.ZeroReflectionSupport`, `Energy.ZeroGrowthOriginal`, `Moments.AmplifiedChildWidth`, `Moments.FiniteProfileExceptionalCommonAsymmetric`, `Moments.FirstExceptionalPaidScales`, `Moments.FirstInactiveRadicalMass`, `Moments.FirstMixedAllowance`, `Moments.FirstMixedRightTransport`, `PrimeRows.DetectorReady`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B024

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  GaussSum.FixedRayFibers
  GaussSum.ResidualEquivalence
  RowCompletion.RowAmplitudes
  Descent.ActiveCusp
  Descent.ReflectedDual
  Reflection.Coefficient
  Reflection.Rows
  Reflection.Actual
  Reflection.Columns
  Reflection.MarkedRow
  Reflection.MarkedSource
  Reflection.MarkedActualSource
  Reflection.MarkedFiber
  Reflection.OriginalMask
  Reflection.TupleFamily
  Reflection.SlotCoefficients
  Reflection.CubeSlots
  Reflection.RawCoefficient
  Reflection.Pullback
  Reflection.CompletedFiberSource
  Moments.HeckeVolume
  Moments.HeckeCancellation
  Moments.FirstCanonicalFamily
  Moments.FirstIdealFamily
  Descent.CanonicalEnergyExistenceData
  Detector.RowRadicalConductor
  Detector.CentralRepeatedProduct
  Hecke.InverseAmplificationPrimePool
  Hecke.DetectorRawFiber
  Hecke.DetectorFiberPartition
  Detector.LowPeriod
  Detector.LowCompletion
  Detector.LowGramArithmetic
  Detector.FinalAssemblyData
  Dictionary.InverseMarkedReferenceFiber
  Dictionary.InverseRawInitialGates
  Dictionary.InverseMarkedReferenceDeleted
  Dictionary.InverseRawInitialEnergy
  Moments.FirstSectorTransform
  Moments.CommonAllocationBox
  Moments.SourceLiveColumn
  Moments.SecondSourceEnergy
  Moments.SecondSectorColumns
  Moments.SecondCanonical
  Moments.SecondCanonicalFrequency
  Moments.SecondCanonicalNonunit
  Moments.FirstScale
  Moments.FirstDiscardedEnergy
  Moments.FirstTailAggregate
  Hecke.MaskDescent
  Moments.FixedRowMask
  Moments.RestrictedEnergy
  Moments.RestrictedSource
  Moments.SourceRectangle
  Moments.CommonRadialData
  Energy.State
  Moments.FirstLocalization
  Moments.DetectorDictionaryFiber
  Moments.NaturalFixedRaySourceFixedIdeal
  Energy.Bands
  Energy.BandMonotonicity
  Moments.AmplificationEnergy
  Moments.AmplificationSourceDomain
  Moments.FirstAmplificationChoice
  Moments.DetectorPlainSource
  Moments.FirstCommonTransport
  Moments.FirstCommonFourierTransport
  Moments.FirstPhysicalSource
  Moments.SecondActiveCount
  Energy.ReferenceState
  Moments.SecondRetainedAggregate
  Moments.ExceptionalSourceShell
  Energy.ZeroReflectionSupport
  Energy.ZeroGrowthOriginal
  Moments.AmplifiedChildWidth
  Moments.FiniteProfileExceptionalCommonAsymmetric
  Moments.FirstExceptionalPaidScales
  Moments.FirstInactiveRadicalMass
  Moments.FirstMixedAllowance
  Moments.FirstMixedRightTransport
  PrimeRows.DetectorReady
-/

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

open scoped Classical BigOperators ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic CompletedGauss CubicKubota CubicJacobiGlobal ConcreteTraceCRT
open LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def sourcePhaseUnit (j:Fin 3) (w u:Eisˣ) : Eisˣ :=
  if j=0 then paperLambdaUnit*w^2*u else -(w^2*u*paperLambdaUnit⁻¹)

def sourcePhaseExponent (j:Fin 3) (m:ℕ) : ℕ :=
  if j=0 then m+1 else m-1

end

open ActualEisensteinCubic CompletedGauss CompletedDyadic CubicKubota CubicJacobiGlobal ConcreteTraceCRT
open LocalReflectionBrackets ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

def phaseUpperUnit : Eisˣ := s.upper_unit.unit

def modelDualNumerator (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  sourceCuspPhaseNumerator s.index (s.upper 0 0) (fixedCuspArrayIndex u m I J)

end FixedCuspShape

namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
noncomputable local instance coefficientField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P
noncomputable local instance coefficientFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

def activePhase (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) : ℂ :=
  ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)

def modelRowPhase (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (u:Eisˣ) (m:ℕ) : ℂ :=
  star D.fixedFactor*D.activePhase hp hg j*
    ramifiedBranchPhase (fun i=>Ideal.span {p i}) hg j
      (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)

end ControlledStratumArithmetic

end CubicEisenstein

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

open scoped BigOperators Classical MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def activeStratumDatum {ι:Type*} [Fintype ι]
    (p:ι→Eis) (hp:∀i,p i≠0) (hprimary:∀i,lambda^2∣p i-1)
    {N a0 c0:Eis} {mode:Bool}
    (D:∀A:Finset ι,ControlledStratumArithmetic (fun i:A=>p i.val) N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hc0:c0≠0)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (A:Finset ι) (v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ) : SourceCuspDatum :=
  (D A).datum hN (primary_finset_product Finset.univ (fun i:A=>p i.val)
    (fun i _=>hprimary i.val)) hbase s (fun i=>hp i.val) hc0 v

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota CubicJacobiGlobal
open CanonicalRowCompletion
local notation "Eis" => ActualEisensteinCubic.O

abbrev FixedActiveCuspIndex {ι:Type*} (c:Eis) (p:ι→Eis) :=
  Σ_h:Eis⧸Ideal.span {c},ΣA:Finset ι,∀i:A,(Eis⧸Ideal.span {p i.val})ˣ

variable {ι:Type*} [Fintype ι] (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hp:∀i,p i≠0) (hprimary:∀i,lambda^2∣p i-1)
variable (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
variable (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
variable (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h) (N:Eis)
variable (hN:∀h,(9:Eis)*(G h).c0∣N)
variable (D:∀h:Eis⧸Ideal.span {c},∀A:Finset ι,
  ControlledStratumArithmetic (fun i:A=>p i.val) N (G h).a0 (G h).c0 (G h).mode)

def fixedActiveCuspDatum (t:FixedActiveCuspIndex c p) : SourceCuspDatum :=
  activeStratumDatum p hp hprimary (D t.1) (hN t.1) (G t.1).denominator_ne_zero
    (G t.1).primary (G t.1).shape t.2.1 t.2.2

end CubicEisenstein

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion

section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

structure GoodMaskRowData (m f z:Eis) where
  maskUnit:Eisˣ
  maskLambda:ℕ
  maskTwo:ℕ
  maskGood:Eis
  maskSupported:Supported (Ideal.span {maskGood})
  maskPrimary:lambda^2∣maskGood-1
  maskFactor:m=maskUnit.val*lambda^maskLambda*(2:Eis)^maskTwo*maskGood
  numeratorUnit:Eisˣ
  numeratorLambda:ℕ
  numeratorTwo:ℕ
  numeratorGood:Eis
  numeratorSupported:Supported (Ideal.span {numeratorGood})
  numeratorPrimary:lambda^2∣numeratorGood-1
  numeratorFactor:f^4*z=numeratorUnit.val*lambda^numeratorLambda*(2:Eis)^numeratorTwo*numeratorGood

theorem exists_goodMaskRowData (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) :
    Nonempty (GoodMaskRowData m f z) := by
  obtain ⟨um,am,bm,g,hg,hpg,hmf⟩:=exists_supported_numerator_factorization m hm
  obtain ⟨u,a,b,r,hr,hpr,hxf⟩:=exists_supported_numerator_factorization (f^4*z)
    (mul_ne_zero (pow_ne_zero _ hf) hz)
  exact ⟨⟨um,am,bm,g,hg,hpg,hmf,u,a,b,r,hr,hpr,hxf⟩⟩

noncomputable def goodMaskRowData (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) :
    GoodMaskRowData m f z := Classical.choice (exists_goodMaskRowData m f z hm hf hz)

namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)

def movingIdeal : Ideal Eis := goodMaskMovingIdeal D.maskGood D.numeratorGood

lemma movingSupported : Supported D.movingIdeal :=
  goodMaskMovingIdeal_supported D.maskGood D.numeratorGood D.maskSupported D.numeratorSupported

def fixedFactor (Ψ:Eis→*ℂ) (Q:Ideal Eis) : Eis→*ℂ :=
  (Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
    D.numeratorSupported)*basePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)})

end GoodMaskRowData

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O
namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)
variable (R I F Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hF:Squarefree F)
    (hm:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
include R I F Q0 hR hI hF hm hf hz hbad hcop hA hT

noncomputable def primeFiberEquiv :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0 ≃
      FreePrimeIndex D.movingIdeal Q0 :=
  goodMaskFreePrimeFiberEquiv R I F Q0 hR hI hF m f z hm hf hz
    D.maskUnit D.maskLambda D.maskTwo D.maskGood D.maskSupported D.maskFactor
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorFactor hbad hcop hA hT

lemma primeFiberEquiv_val
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT P).val.val=
      Sum.elim Subtype.val Subtype.val P := by
  cases P <;> rfl

local notation "splitIndex" => D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT

end GoodMaskRowData

noncomputable def fiberGoodMaskRowData (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (m:Eis)
    (hm:m≠0) (hF:F≠0) (hrows:∀I∈rows,I≠0) (u:Eisˣ)
    (I:representativeRowFiber rows R (Ideal.span {m}*F)) :
    GoodMaskRowData m (ConcretePrimeRowBridge.idealGenerator F)
      (u.val*ConcretePrimeRowBridge.idealGenerator I.val) :=
  goodMaskRowData _ _ _ hm (ConcretePrimeRowBridge.idealGenerator_ne_zero F hF)
    (mul_ne_zero u.ne_zero (ConcretePrimeRowBridge.idealGenerator_ne_zero I.val
      (hrows I.val (Finset.mem_filter.mp I.property).1)))

end CanonicalRowCompletion

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

namespace CanonicalRowCompletion

variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]

def residualActivePrimes (e:α⊕β ≃ γ) : Finset γ :=
  Finset.univ.image (fun a:α=>e (Sum.inl a))

omit [Fintype β] [Fintype γ] in
lemma residualActivePrimes_not_inr (e:α⊕β ≃ γ) (b:β) :
    e (Sum.inr b)∉residualActivePrimes e := by
  intro h
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp h
  cases e.injective ha

def nonresidualComplementMap (e:α⊕β ≃ γ) : β → {g:γ // g∉residualActivePrimes e} :=
  fun b=>⟨e (Sum.inr b),residualActivePrimes_not_inr e b⟩

omit [Fintype β] [Fintype γ] in
lemma nonresidualComplementMap_bijective (e:α⊕β ≃ γ) :
    Function.Bijective (nonresidualComplementMap e) := by
  constructor
  · intro a b hab
    exact Sum.inr.inj (e.injective (congrArg Subtype.val hab))
  · intro g
    obtain ⟨x,hx⟩:=e.surjective g.val
    cases x with
    | inl a=>
      exact (g.property (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,hx⟩)).elim
    | inr b=>exact ⟨b,Subtype.ext hx⟩

noncomputable def nonresidualComplementEquiv (e:α⊕β ≃ γ) :
    β ≃ {g:γ // g∉residualActivePrimes e} :=
  Equiv.ofBijective (nonresidualComplementMap e) (nonresidualComplementMap_bijective e)

end CanonicalRowCompletion

open scoped BigOperators Classical ContDiff

open scoped Classical BigOperators ContDiff

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass
open ConcretePrimeRowBridge SecondPassArithmetic
local notation "Eis" => ActualEisensteinCubic.O

lemma normTwistedSource_contDiff (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W) (t:ℝ) :
    ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W t) := by
  have he:(CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t:ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t:=by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  rw [←he]
  exact (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t).smooth ⊤

end CanonicalRowCompletion

open scoped Classical BigOperators

open scoped BigOperators Classical

namespace CanonicalRowCompletion
variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]

def completeActiveSet (e:α⊕β ≃ γ) (B:Finset β) : Finset γ :=
  residualActivePrimes e∪B.image (fun b=>e (Sum.inr b))

omit [Fintype β] [Fintype γ] in
lemma completeActiveSet_residual (e:α⊕β ≃ γ) (B:Finset β) (a:α) :
    e (Sum.inl a)∈completeActiveSet e B :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩)

omit [Fintype γ] in
lemma optionalPrimeActive_completeActiveSet (e:α⊕β ≃ γ) (B:Finset β) :
    optionalPrimeActive e (completeActiveSet e B)=B := by
  ext b
  rw [mem_optionalPrimeActive]
  change e (Sum.inr b)∈residualActivePrimes e∪B.image (fun b=>e (Sum.inr b)) ↔ b∈B
  simp only [Finset.mem_union,residualActivePrimes_not_inr,false_or,Finset.mem_image]
  constructor
  · rintro ⟨b',hb',he⟩
    have hb:b'=b:=Sum.inr.inj (e.injective he)
    exact hb ▸ hb'
  · intro hb
    exact ⟨b,hb,rfl⟩

noncomputable def selectedActiveEquiv (e:α⊕β ≃ γ) (B:Finset β) :
    α⊕B ≃ completeActiveSet e B := by
  let t : B ≃ optionalPrimeActive e (completeActiveSet e B):={
    toFun:=fun b=>⟨b.val,by simpa only [optionalPrimeActive_completeActiveSet] using b.property⟩
    invFun:=fun b=>⟨b.val,by simpa only [optionalPrimeActive_completeActiveSet] using b.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  exact (Equiv.sumCongr (Equiv.refl _) t).trans
    (activePrimeUnionEquiv e (completeActiveSet e B) (completeActiveSet_residual e B))

end CanonicalRowCompletion

open scoped BigOperators Classical

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

def maskElement (q:ℕ) (m:Eis) : Eis := m*excludedGenerator (reflectionExcludedPrimes q)
def maskIdeal (q:ℕ) (m:Eis) (F:Ideal Eis) : Ideal Eis := Ideal.span {maskElement q m}*F
abbrev RowIndex (q:ℕ) (m:Eis) (rows:Finset (Ideal Eis)) (R F:Ideal Eis) :=
  representativeRowFiber rows R (maskIdeal q m F)

lemma maskElement_ne_zero (q:ℕ) (m:Eis) (hm:m≠0) : maskElement q m≠0 :=
  mul_ne_zero hm (reflectionExcludedGenerator_ne_zero q)

variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)

noncomputable def data (J:RowIndex q m rows R F) :
    GoodMaskRowData (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val) :=
  fiberGoodMaskRowData rows R F (maskElement q m) (maskElement_ne_zero q m hm) hF.ne_zero hrows v J

variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

end CanonicalRowCompletion.ActualFiber

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein ConcreteTraceCRT
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance activeQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _

variable {ι : Type*} [Fintype ι]

def localInactiveWeight (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (A : Finset ι) : ℂ :=
  ∏ i ∈ (Finset.univ : Finset ι) \ A,
    finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (F i) 0

def localActiveWeight (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (A : Finset ι) (v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ) : ℂ :=
  ∏ i : A, finiteAdditiveFourierCoeff (quotientTrace (p i.val) (hp i.val)) (F i.val) (v i)

def fixedActiveFunctionWeight
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (φ : Eis →* ℂ) (t : FixedActiveCuspIndex c p) : ℂ :=
  fixedThetaRowCoeff c hc φ t.1 * localInactiveWeight p hp F t.2.1 *
    localActiveWeight p hp F t.2.1 t.2.2

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups
open CompletedGauss CubicEisenstein ConcreteTraceCRT CubicKubota CompletedDyadic
open CubicJacobiGlobal ShortDraftCusp FiniteGaussPhase LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance dualQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

def mixedSmoothedValue (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ,
    fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
      (D.datum hN hr hbase s hp hc0 v).smoothedKernel W X

def mixedReflectedValue (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  fixedRadialCoefficientScalar * s.stratumShapeFactor (c0 * ∏ i, p i) *
    ∑' t : ThetaFullIndex,
      (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
        ((ramifiedScale 1 completedRamifiedStep t.2.1 *
          Real.sqrt (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ) : ℝ) : ℂ)) *
      CubicReflectionKernel.paperKernel (Vstar W)
        ((X / (27 * (sourceCuspScale s.index) ^ 2 * (Ideal.absNorm (Ideal.span {c0 * ∏ i, p i}) : ℝ) ^ 2)) *
          (ramifiedScale 1 completedRamifiedStep t.2.1) ^ 3 *
          (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ) ^ 3) *
      ((star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U
          (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))) *
        ∏ i, mixedActiveBracket hp hg j S D i
          (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
open InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance coefficientFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def sourceRowPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (R F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  residualWithFrozen hp hg c R F * ramifiedBlock hg (fun _ => 1) R
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m) * frozenArgument hg j F (∏ i ∈ R, p i)

def sourceSlotPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  markedWithFrozen hp hg c S F * ramifiedBlock hg (fun _ => 0) S
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m) * frozenArgument hg j F (∏ i ∈ S, p i)

def sourceFrozenPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  star D.fixedFactor * frozenCore hp hg c j F * ramifiedBlock hg j F
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)

def sourceColumn [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase s.index u
    (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1)*D.U))
      (s.modelDualNumerator u) u) m n b *
  ∏ i ∈ F, bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
    (Ideal.Quotient.mk _ (primaryGenerator n*(primaryGenerator b)^3))

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
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

namespace PrimeFamily
variable {ι κ : Type*}

def sum (G : PrimeFamily ι) (H : PrimeFamily κ) : PrimeFamily (ι ⊕ κ) where
  ideal := Sum.elim G.ideal H.ideal
  maximal i := by cases i with | inl i => exact G.maximal i | inr i => exact H.maximal i
  good i := by cases i with | inl i => exact G.good i | inr i => exact H.good i

def residual (K : Ideal Eis) (hK : Admissible K) : PrimeFamily (PrimeIndex K) where
  ideal := fun P => P.val
  maximal _P := inferInstance
  good := admissiblePrimeGood K hK

lemma residual_product (K : Ideal Eis) (hK : Admissible K) :
    (∏ P, (residual K hK).ideal P) = K := admissible_primeIndex_product K hK

lemma residual_dvd (K : Ideal Eis) (hK : Admissible K) (P : PrimeIndex K) : P.val ∣ K :=
  Ideal.dvd_iff_le.mpr (primeIndex_le K hK.1 P)

def reflected {φ σ : Type*} (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) : PrimeFamily (φ ⊕ (PrimeIndex K ⊕ σ)) := F.sum ((residual K hK).sum S)

end PrimeFamily
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

def actualMixedCoefficient (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  s.amplitude u m n b *
    (star D.fixedFactor * ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
      (s.modelDualNumerator u m n b)) *
    ∏ i, mixedActiveBracket (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) D i (s.modelDualNumerator u m n b)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι φ σ : Type*} [Fintype ι] [Fintype φ] [Fintype σ]
variable {p : ι → Eis} {N a c : Eis} {mode : Bool}

def actualCuspColumn (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase s.index u
    (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1)*D.U))
      (s.modelDualNumerator u) u) m n b

def frozenBranchColumn (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) : ℂ :=
  A n b * reflectedBranch (fun i => Ideal.span {F.generator i}) F.generator_good jF e
    (primaryGenerator n) (primaryGenerator b)

def frozenExtracted (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) (v : Fin 3) : Ideal Eis :=
  reflectionExtractedDivisor (fun i => Ideal.span {F.generator i}) jF e v

def frozenBranchScale (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) : ℝ :=
  Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*
    Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 2):ℝ)/
    Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 0):ℝ)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def freePrimeFamily (I Q : Ideal Eis) (hI : Supported I) : PrimeFamily (FreePrimeIndex I Q) where
  ideal P := P.val.val
  maximal _P := inferInstance
  good P := (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

def markedSumSlots {ι σ : Type*} [Fintype ι] [Fintype σ] : Finset (ι⊕σ) :=
  Finset.univ.filter (fun x => x.isRight)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

namespace PrimeFamily
variable {ι : Type*} (P : PrimeFamily ι)

def restrict (A : Finset ι) : PrimeFamily A where
  ideal i := P.ideal i.val
  maximal i := P.maximal i.val
  good i := P.good i.val

lemma restrict_pairwise (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (A : Finset ι) :
    Pairwise (Function.onFun IsCoprime (P.restrict A).ideal) := by
  intro i k hik
  exact hP (fun h => hik (Subtype.ext h))

def activeControlled [Fintype ι]
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (c : Eis) (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (h : Eis⧸Ideal.span {c}) (A : Finset ι) :
    ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode :=
  Classical.choice ((P.restrict A).exists_controlled N (G h).a0 (G h).c0 (G h).mode
    (G h).denominator_ne_zero (hN h) (G h).primary (G h).coprime
    (P.restrict_pairwise hP A) (fun i => hNp i.val))

end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

abbrev markedRowFamily {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis) :=
  (freePrimeFamily D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported).sum S

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [Fintype ι] [Fintype σ]

def joinedInactiveCoefficient (P : PrimeFamily ι) (S : PrimeFamily σ) (j : ι→ℕ) : ι⊕σ→ℂ :=
  Sum.elim (fun i => if j i=0 then 1-(Ideal.absNorm (P.ideal i):ℂ)⁻¹ else 0)
    (fun i => (Ideal.absNorm (S.ideal i):ℂ)⁻¹)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma maximal_coprime_iff_ne (P Q : Ideal Eis) [P.IsMaximal] [Q.IsMaximal] :
    IsCoprime P Q ↔ P≠Q := by
  constructor
  · intro h he
    subst Q
    exact (show P.IsPrime from inferInstance).ne_top (by simpa using h.sup_eq)
  · exact Ideal.isCoprime_of_isMaximal

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem original_slot_mask_iff (S : PrimeFamily σ) :
    (∀ P : FreePrimeIndex D.movingIdeal Q₀, ∀ t, S.ideal t≠P.val.val) ↔
    IsCoprime K (∏ t, S.ideal t) ∧
      ∀ b : FreeReflection.pool R (Ideal.span {m}*F) Q₀, ∀ t, S.ideal t≠b.val := by
  constructor
  · intro h
    constructor
    · rw [← PrimeFamily.residual_product K hK]
      apply IsCoprime.prod_left_iff.mpr
      intro a ha
      apply IsCoprime.prod_right_iff.mpr
      intro t ht
      apply Ideal.isCoprime_of_isMaximal
      have hh := h (E (Sum.inl a)) t
      rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)] at hh
      exact hh.symm
    · intro b t
      have hh := h (E (Sum.inr b)) t
      rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b)] at hh
      exact hh
  · rintro ⟨hrow,hfixed⟩ P t
    obtain ⟨x,rfl⟩ := (E).surjective P
    cases x with
    | inl a =>
      rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)]
      have hc := (hrow.of_isCoprime_of_dvd_left (PrimeFamily.residual_dvd K hK a)).of_isCoprime_of_dvd_right
        (Finset.dvd_prod_of_mem S.ideal (Finset.mem_univ t))
      exact ((maximal_coprime_iff_ne _ _).mp hc).symm
    | inr b =>
      rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b)]
      exact hfixed b t
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def tupleRepresentative (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (P : Ideal Eis) : σ→Ideal Eis :=
  if h : ∃ p∈tuples, slotTupleProduct p=P then h.choose else hne.choose

omit [DecidableEq σ] in
lemma tupleRepresentative_mem (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (P : Ideal Eis) : tupleRepresentative tuples hne P∈tuples := by
  unfold tupleRepresentative
  split
  next h => exact h.choose_spec.1
  next h => exact hne.choose_spec

omit [DecidableEq σ] in
lemma tupleRepresentative_product (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (P : Ideal Eis) (hP : P∈tuples.image slotTupleProduct) :
    slotTupleProduct (tupleRepresentative tuples hne P)=P := by
  have h : ∃ p∈tuples, slotTupleProduct p=P := Finset.mem_image.mp hP
  simp only [tupleRepresentative,dif_pos h]
  exact h.choose_spec.2

omit [DecidableEq σ] in
lemma tupleRepresentative_at_product (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (p : σ→Ideal Eis) (hp : p∈tuples) :
    tupleRepresentative tuples hne (slotTupleProduct p)=p := by
  exact hinj (tupleRepresentative_mem tuples hne _) hp
    (tupleRepresentative_product tuples hne _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))

def tuplePrimeFamily (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i) (P : Ideal Eis) : PrimeFamily σ where
  ideal := tupleRepresentative tuples hne P
  maximal := hmax _ (tupleRepresentative_mem tuples hne P)
  good := hgood _ (tupleRepresentative_mem tuples hne P)

omit [DecidableEq σ] in
lemma tuplePrimeFamily_at_product (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (p : σ→Ideal Eis) (hp : p∈tuples) :
    (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p)).ideal=p :=
  tupleRepresentative_at_product tuples hne hinj p hp

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma PrimeFamily.eq_of_ideal_eq {ι : Type*} (P Q : PrimeFamily ι) (h : P.ideal=Q.ideal) : P=Q := by
  cases P
  cases Q
  cases h
  rfl

def slotChoiceFamily (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (p : ∀ i,L i) : PrimeFamily σ where
  ideal i := (p i).val
  maximal i := hmax i _ (p i).property
  good i := hgood i _ (p i).property

omit [Fintype σ] in
lemma slotChoiceFamily_active (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (T : Finset σ) (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val) :
    (slotChoiceFamily L hmax hgood ((slotChoiceSplit L T).symm (a,b))).restrict T=
      slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) a := by
  apply PrimeFamily.eq_of_ideal_eq
  funext i
  exact congrArg Subtype.val (slotChoiceSplit_active L T a b i)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def cubeActiveSlots (H : Ideal Eis) (S : PrimeFamily σ) : Finset σ :=
  Finset.univ.filter (fun i => ¬S.ideal i∣H)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def literalRawCoefficient (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  if Squarefree n ∧ primaryGenerator n≠0 ∧ primaryGenerator b≠0 then
    (s.amplitude u m n b *
      (star D.fixedFactor*ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m n b))*
      ∏ i, mixedActiveBracket G.generator_ne_zero G.generator_good j S D i (s.modelDualNumerator u m n b)) /
        ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ):ℝ):ℂ)
  else 0

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι→Eis} {q : κ→Eis}
    {N a c : Eis} {mode : Bool}

omit [Fintype ι] [Fintype κ] in
lemma pullback_generator_eq (e : κ≃ι) (h : (fun k => p (e k))=q) :
    (fun i => q (e.symm i))=p := by
  rw [← h]
  simp only [Equiv.apply_symm_apply]

def pullbackControlled (e : κ≃ι) (h : (fun k => p (e k))=q)
    (D : ControlledStratumArithmetic q N a c mode) :
    ControlledStratumArithmetic p N a c mode :=
  castControlled (pullback_generator_eq e h) (reindexControlled D e.symm)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (parents : Finset (Ideal Eis)) (J F : Ideal Eis) (hJ : J≠0) (hF : Squarefree F)
    (m : Eis) (hm : m≠0) (hparents : ∀ I∈parents,I≠0) (v : Eisˣ)
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)

def residualOriginalData (K : originalResidualRows parents J (Ideal.span {m}*F)) :
    GoodMaskRowData m (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J (Ideal.span {m}*F) K.val)) :=
  fiberGoodMaskRowData parents J F m hm hF.ne_zero hparents v
    ⟨reconstructFiberRow J (Ideal.span {m}*F) K.val,
      (originalResidualRows_reconstruct parents J (Ideal.span {m}*F) hparents K.val K.property).1⟩

variable (Q : Ideal Eis) (hQ : Q≠0) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (hcop : ∀ K∈originalResidualRows parents J (Ideal.span {m}*F),IsCoprime (Q*Ideal.span {(72:Eis)}) K)
    (lists : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
    (hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
    (hodd : ∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2)
    (hperiod : ∀ i,∀ P∈lists i,IsCoprime (Q*Ideal.span {(72:Eis)}) P)

abbrev originalResidualAdmissible : ∀ K∈originalResidualRows parents J (Ideal.span {m}*F),Admissible K := by
  intro K hK
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  exact rowResidualPart_admissible I _ hbad

include hJ hQ hcQ hcop hdis hodd hperiod

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentHeckeVolume
open HeckeFamily CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentPrimary CanonicalQuadraticSieve QuadraticInitialBound
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open PrimaryIdealUnitReindex (GoodIdeal)
open CubicEisenstein (PrimaryLower primaryLowerIdealEquiv)
local notation "O" => ActualEisensteinCubic.O

def primaryCoefficient (ψ : Character) : Ideal O →* ℂ where
  toFun I := if primaryGenerator I=0 then 0 else idealCoeff ψ I
  map_one' := by simp only [primaryGenerator_one,one_ne_zero,ite_false,map_one]
  map_mul' := by
    intro I J
    simp only [primaryGenerator_mul,map_mul]
    by_cases hI : primaryGenerator I=0 <;> by_cases hJ : primaryGenerator J=0 <;>
      simp only [hI,hJ,mul_eq_zero,or_false,ite_true,ite_false,zero_mul,mul_zero]

def periodicValue (c : O) (ψ : Character) (r : O ⧸ Ideal.span {c}) : ℂ :=
  if (3:O) ∣ Quotient.out r-1 then elementCoeff ψ (Quotient.out r) else 0

def fixedPeriod (Q : Ideal O) : O := 3*ConcretePrimeRowBridge.idealGenerator Q

theorem fixedPeriod_ne_zero (Q : Ideal O) (hQ : Q ≠ 0) : fixedPeriod Q ≠ 0 :=
  mul_ne_zero (by norm_num) (ConcretePrimeRowBridge.idealGenerator_ne_zero Q hQ)

theorem inducedBy_of_elementCoeff_eq (χ χ' ψ : Character)
    (heq : ∀ n, elementCoeff χ' n=elementCoeff χ n)
    (hind : CenteredExceptionalProfile.InducedBy χ ψ) :
    CenteredExceptionalProfile.InducedBy χ' ψ := by
  have hideal (I : Ideal O) : idealCoeff χ' I=idealCoeff χ I := by
    by_cases hI : I=0
    · simp only [hI,map_zero]
    · conv_lhs => rw [← ConcretePrimeRowBridge.span_idealGenerator I,
        idealCoeff_span χ' (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI),heq]
      rw [← idealCoeff_span χ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI),
        ConcretePrimeRowBridge.span_idealGenerator]
  intro I
  by_cases hI : I=0
  · simp only [hI,map_zero,ite_self]
  by_cases hc : IsCoprime I χ'.modulus
  · have hn := CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I |>.mpr ⟨hI,hc⟩
    rw [hideal I] at hn
    have hc' := (CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ I).mp hn |>.2
    rw [if_pos hc,hideal I,hind I,if_pos hc']
  · have hz : idealCoeff χ' I=0 := by
      by_contra hn
      exact hc ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I).mp hn).2
    rw [if_neg hc,hz]

def density (c : O) (hc : c ≠ 0) (ψ : Character) (R : Ideal O) : ℂ :=
  letI := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  (∑ D ∈ idealDivisors R, (moebius D:ℂ)*primaryCoefficient ψ D/(Ideal.absNorm D:ℂ)) *
    (1/(‖eisEmbedding c‖^2:ℂ))*(∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r)

end SevenEighths.CenteredMomentHeckeVolume

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentHeckeCancellation
open HeckeFamily CenteredMomentHeckeVolume ConcreteTraceCRT EisensteinSchwartzPoisson
open IdealMobiusDivisorSum QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

def idealSum (χ : Character) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X)

def volumeControl (Q : Ideal O) (χ : Character) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (O ⧸ Ideal.span {fixedPeriod Q}):ℝ)*pvControl W

end SevenEighths.CenteredMomentHeckeCancellation

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstCanonicalFamily
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstFamily
open CenteredMomentFirstColumns CenteredMomentPrimitive CenteredMomentCommonSupport RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem supported_of_dvd (A B : Ideal O) (hB : Supported B) (hd : A∣B) : Supported A := by
  obtain ⟨Q,hQ⟩ := hd
  rw [hQ] at hB
  exact ((supported_mul_iff A Q).mp hB).1

theorem activeConductor_supported (I J : Ideal O) (hI : Supported I) :
    Supported (Ideal.span {activeConductor I J}) :=
  supported_of_dvd _ _ (commonPart_supported I J hI) (activeConductor_span_dvd I J)

theorem subsetGenerator_span_dvd (I J : Ideal O) (E : Finset (CommonIndex I J)) :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E}∣commonPart I J := by
  rw [primeSubsetGenerator,span_idealGenerator]
  refine (Finset.prod_dvd_prod_of_subset E Finset.univ
    (fun P : CommonIndex I J => P.val) (Finset.subset_univ _)).trans ?_
  rw [commonPart_left_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (leftExponent_pos I J P)

theorem subsetGenerator_supported (I J : Ideal O) (hI : Supported I)
    (E : Finset (CommonIndex I J)) :
    Supported (Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E}) :=
  supported_of_dvd _ _ (commonPart_supported I J hI) (subsetGenerator_span_dvd I J E)

def canonicalActiveCharacter (I J : Ideal O) (hI : Supported I) :
    MulChar (Residue (activeConductor I J)) ℂ :=
  primitiveCharacter (activePrime I J) (activeCoprime I J) (activeGood I J hI) (activeExponent I J)

@[simp] theorem canonicalActiveCharacter_mk (I J : Ideal O) (hI : Supported I) (n : O) :
    canonicalActiveCharacter I J hI (Ideal.Quotient.mk _ n)=
      finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J) n :=
  primitiveCharacter_mk _ _ _ _ n

theorem exists_canonical_first_pair (η : Character) (m : O) (hm : m≠0)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (I J : Ideal O) (hI : Supported I) (E : Finset (CommonIndex I J))
    (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
    let r := activeConductor I J
    let ρ := finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J)
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
        elementCoeff τ₁ n=elementCoeff η n*coprimalityMask m n*leftCoefficient e r ρ n*rayCharacter ξ₁ n) ∧
      (∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
        elementCoeff τ₂ n=elementCoeff η n*coprimalityMask m n*rightCoefficient e r ρ n*rayCharacter ξ₂ n) := by
  dsimp only
  obtain ⟨τ₁,hM₁,_,h₁⟩ := exists_first_character η m
    (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) (activeConductor I J) hm
    (subsetGenerator_supported I J hI E) (activeConductor_supported I J hI) hmLam hm2
    (canonicalActiveCharacter I J hI) ξ₁
  obtain ⟨τ₂,hM₂,_,h₂⟩ := exists_first_character η m
    (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) (activeConductor I J) hm
    (subsetGenerator_supported I J hI E) (activeConductor_supported I J hI) hmLam hm2
    (canonicalActiveCharacter I J hI)⁻¹ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro n hn hp
    rw [h₁ n hn hp,canonicalActiveCharacter_mk,leftCoefficient]
    ring
  · intro n hn hp
    let : Finite (Residue (activeConductor I J)) := finite_quotient_span (finitePrimeModulus_ne_zero (activePrime I J))
    rw [h₂ n hn hp,← MulChar.star_apply',canonicalActiveCharacter_mk,rightCoefficient]
    ring

end SevenEighths.CenteredMomentFirstCanonicalFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstIdealFamily
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalRowCompletion
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentSourceRow
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentFirstColumns
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_one_primary (η : Character) (m : O) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    rowWeight η m 1 1 t I=elementCoeff η (CompletedGauss.primaryGenerator I)*
      coprimalityMask m (CompletedGauss.primaryGenerator I)*(Ideal.absNorm I:ℂ)^(Complex.I*t) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primary_span_supported I hI
  have he : idealCoeff η I=elementCoeff η (CompletedGauss.primaryGenerator I) := by
    have hh := idealCoeff_span η hn
    rw [hs] at hh
    exact hh
  have hm : idealRowHom (m^6) I=coprimalityMask m (CompletedGauss.primaryGenerator I) := by
    have hh := idealRowHom_sixth_eq_mask m _ (hs.symm ▸ hI)
    rw [hs] at hh
    exact hh
  change (idealCoeff η I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
  rw [mul_one,mul_one,he,hm]

theorem ideal_height_of_primary (η τ : Character) (m : O) (F : O → ℂ)
    (hτ : ∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
      elementCoeff τ n=elementCoeff η n*coprimalityMask m n*F n)
    (I : Ideal O) (hI : Supported I) (t : ℝ) :
    idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
      rowWeight η m 1 1 t I*F (CompletedGauss.primaryGenerator I) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := CompletedGauss.primaryGenerator_spec I hn
  have he := hτ (CompletedGauss.primaryGenerator I) (hs.1.symm ▸ hI) hs.2
  rw [← idealCoeff_span τ hn,hs.1] at he
  rw [he,rowWeight_one_primary η m t I hI]
  ring

theorem exists_first_ideal_pair (η : Character) (m : O) (hm : m≠0)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O,Supported I → ∀ t : ℝ,
        idealCoeff τ₁ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
          rowWeight η m 1 1 t I*
            (leftCoefficient e r ρ (CompletedGauss.primaryGenerator I)*
              rayCharacter ξ₁ (CompletedGauss.primaryGenerator I))) ∧
      (∀ I : Ideal O,Supported I → ∀ t : ℝ,
        idealCoeff τ₂ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
          rowWeight η m 1 1 t I*
            (rightCoefficient e r ρ (CompletedGauss.primaryGenerator I)*
              rayCharacter ξ₂ (CompletedGauss.primaryGenerator I))) := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩ := exists_canonical_first_pair η m hm hmLam hm2 C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro I hI t
    apply ideal_height_of_primary η τ₁ m
      (fun n => leftCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*rayCharacter ξ₁ n) _ I hI t
    intro n hn hp
    rw [h₁ n hn hp]
    ring
  · intro I hI t
    apply ideal_height_of_primary η τ₂ m
      (fun n => rightCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*rayCharacter ξ₂ n) _ I hI t
    intro n hn hp
    rw [h₂ n hn hp]
    ring

end SevenEighths.CenteredMomentFirstIdealFamily

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseReflectedPhase
local notation "O"=>ActualEisensteinCubic.O

def CanonicalEnergyExists (Mcap Fcap c eps L:ℝ)(K:ℕ)(W:𝓢(ℝ,ℂ)):Prop :=
  ∃degree:ℕ,∃B:ℝ,1≤B ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀D:ℕ,B*Z^L≤D→
    ∀{σ:Type}[DecidableEq σ](slots:Finset σ),slots.card≤K→
    ∀(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H:σ→ℝ)(a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→
      (∀i∈slots,1≤H i)→(∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i)→
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1)→
    ∀z:ℝ,0≤z→(∏i∈slots,H i)≤Z^z→
    ∀base:O→*ℂ,(∀u,‖base u‖≤1)→
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) base→
      CompletePoolRankMoments q D slots lists a base W Z Mcap Fcap z c eps C K degree

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeRowRadicalConductor
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def fixedConductorConstant (S : Finset (Ideal O)) : ℕ :=
  ProbeHighRowFamily.conductorConstant * (∏ P ∈ S, P).absNorm

end SevenEighths.ProbeRowRadicalConductor

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedProduct
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CompletedGauss
open HeckeDeletionBounds HeckeReciprocalGrowth
local notation "O" => HeckeFamily.O

def rowCost (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (a e eps T : ℝ) : ℝ :=
  ((ProbeRowRadicalConductor.fixedConductorConstant S:ℝ)*(Ideal.span {u.val}:Ideal O).absNorm)^(a-1/2+6*e)*
    ((radical (rowCharacter S hS u).modulus).absNorm:ℝ)^(6*e+2*eps)*
    (3+T)^2*(presentationComplexity (rowCharacter S hS u) T)^eps

end SevenEighths.ProbeCentralRepeatedProduct

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

def RawScaleEnergy (data : RowData) (W : ℝ→ℂ) (U D V E : ℝ) : Prop :=
  ∀ R : Finset NonzeroElement,
    (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
    ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true W (Real.exp l) 0 0‖^2≤E

def typedPrimePool (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) : Finset PrimeIdeal :=
  (CenteredMomentPrimePool.primePool M H S a b x).subtype Prime

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set
namespace SevenEighths.HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorWitnessRows
open HeckeDetectorSupportedWitness HeckeDetectorCoefficientTransfer HeckeDetectorInverseFiberCount
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

structure Fiber (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) (Label Slot : Type*)
    (U a ε tstar T allowance : ℝ) (i : ℕ) where
  rows : Finset FreeRow
  nonempty : rows.Nonempty
  family : FreeRow→Label→Character
  witness : ∀ u,SupportedWitness (family u) U a ε tstar T allowance i
  label : Label
  left : Fin (dyadicLength U)
  right : Fin (dyadicLength U)
  fixed_label : ∀ u∈rows,(witness u).label=label
  fixed_left : ∀ u∈rows,(witness u).left=left
  fixed_right : ∀ u∈rows,(witness u).right=right
  row_norm : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U
  rowData : RowData
  reverse : Bool
  row_coeff : ∀ u∈rows,∀ J : Ideal O,idealCoeff (family u label) J=
    if reverse then starRingEnd ℂ (idealCoeff (rowData.character ⟨u.val,u.property.1⟩) J)
    else idealCoeff (rowData.character ⟨u.val,u.property.1⟩) J
  slots : Finset Slot
  profile : Slot→ℝ→ℂ
  upper : Slot→ℝ
  widths : Slot→ℝ
  external : Slot→ℂ
  bin : Slot→ℝ
  mesh : ℝ
  binWidth : ℝ
  mesh_nonneg : 0≤ mesh
  binWidth_pos : 0<binWidth
  widths_pos : ∀ s∈slots,0<widths s
  widths_mesh : ∀ s∈slots,widths s≤ mesh
  supply : 7/37≤∑ s∈slots,widths s
  fixed_bin : ∀ u∈rows,∀ s∈slots,
    HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
      (physical M H (fun u : FreeRow => u.val) profile upper widths external U u s)=bin s

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def Fiber.r (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := Real.logb U ((2 : ℝ)^F.left.val)
def Fiber.m (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := Real.logb U ((2 : ℝ)^F.right.val)
def Fiber.q (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := weightedMean F.slots F.widths F.bin
def Fiber.inverseProfile (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ→ℂ := inverseTest U tstar F.r
def Fiber.physicalProduct (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (u : FreeRow) : ℂ :=
  ∏ s∈selected,physical M H (fun u : FreeRow => u.val) F.profile F.upper F.widths F.external U u s

structure Moments (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (Δ c κ C height εm : ℝ) : Prop where
  inverse_raw : ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
    let W := twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t
    RawMoment F.rowData W c κ C ∧ RawMoment F.rowData (scaleProfile W) c κ C
  inverse_marked : ∀ selected : Finset Slot,selected⊆F.slots →
    F.r+2*(∑ s∈selected,F.widths s)<1 → 2*F.r+8*(∑ s∈selected,F.widths s)<3 →
    ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) true ((logProfile^[n]) F.inverseProfile)
        (U^F.r) s t*F.physicalProduct selected u‖^2≤C*U^(1+εm)
  plain_marked : ∀ selected : Finset Slot,selected⊆F.slots →
    2*F.m+6*(3/4+2*Δ)*(∑ s∈selected,F.widths s)≤1 →
    ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
          F.physicalProduct selected u‖^2≤C*U^(1+εm)
  plain_unmarked : ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t‖^2≤
          C*U^(max 1 (2*F.m)+εm)

end SevenEighths.HeckeDetectorRawFiber

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorFiberPartition
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection

abbrev BinLabel {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ) :=
  slots → ↥(HeckePrimeAmplitudeBins.labels cap mesh)

def amplitudeLabel {Row Slot : Type*} (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0< mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ) (u : Row) : BinLabel slots cap mesh :=
  fun s => ⟨HeckePrimeAmplitudeBins.amplitude (U^(widths s)) cap mesh (physical u s),
    HeckePrimeAmplitudeBins.amplitude_mem_labels _ _ _ _ hm⟩

def fiber {Row Label Slot : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0< mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) (bin : BinLabel slots ((2*a-1)/2) mesh)
    (label : Label) (J K : Fin (dyadicLength U)) : Finset Row :=
  rows.filter (fun u => amplitudeLabel slots U ((2*a-1)/2) mesh hm widths physical u=bin ∧
    (w u).label=label ∧ (w u).left=J ∧ (w u).right=K)

def binValue {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (bin : BinLabel slots cap mesh) (s : Slot) : ℝ :=
  if hs : s∈slots then (bin ⟨s,hs⟩).val else 0

theorem fixed_bin {Row Label Slot : Type*}
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0< mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) (bin : BinLabel slots ((2*a-1)/2) mesh)
    (label : Label) (J K : Fin (dyadicLength U)) (u : Row)
    (hu : u∈fiber rows χ U a ε tstar T allowance i w slots mesh hm widths physical bin label J K)
    (s : Slot) (hs : s∈slots) :
    HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) mesh (physical u s)=
      binValue slots ((2*a-1)/2) mesh bin s := by
  have he := (Finset.mem_filter.mp hu).2.1
  have hv := congrArg (fun f : BinLabel slots ((2*a-1)/2) mesh => (f ⟨s,hs⟩).val) he
  simpa only [amplitudeLabel,binValue,dif_pos hs] using hv

def toFiber (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) {Label Slot : Type*}
    (rows : Finset FreeRow) (χ : FreeRow→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (hrow : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U)
    (data : Label→RowData) (reverse : Label→Bool)
    (hcoeff : ∀ u∈rows,∀ j,∀ I : Ideal O,idealCoeff (χ u j) I=
      if reverse j then starRingEnd ℂ (idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
      else idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hmesh : 0≤ mesh) (hbw : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwmesh : ∀ s∈slots,widths s≤ mesh)
    (hsupply : 7/37≤∑ s∈slots,widths s)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (label : Label)
    (J K : Fin (dyadicLength U))
    (hne : (fiber rows χ U a ε tstar T allowance i w slots binWidth hbw widths
      (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K).Nonempty) :
    Fiber M H Label Slot U a ε tstar T allowance i where
  rows := fiber rows χ U a ε tstar T allowance i w slots binWidth hbw widths
    (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K
  nonempty := hne
  family := χ
  witness := w
  label := label
  left := J
  right := K
  fixed_label := fun _u hu => (Finset.mem_filter.mp hu).2.2.1
  fixed_left := fun _u hu => (Finset.mem_filter.mp hu).2.2.2.1
  fixed_right := fun _u hu => (Finset.mem_filter.mp hu).2.2.2.2
  row_norm := fun u hu => hrow u (Finset.mem_filter.mp hu).1
  rowData := data label
  reverse := reverse label
  row_coeff := fun u hu => hcoeff u (Finset.mem_filter.mp hu).1 label
  slots := slots
  profile := profile
  upper := upper
  widths := widths
  external := external
  bin := binValue slots ((2*a-1)/2) binWidth bin
  mesh := mesh
  binWidth := binWidth
  mesh_nonneg := hmesh
  binWidth_pos := hbw
  widths_pos := hw
  widths_mesh := hwmesh
  supply := hsupply
  fixed_bin := fun u hu s hs => fixed_bin rows χ U a ε tstar T allowance i w slots binWidth hbw widths
    (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K u hu s hs

end SevenEighths.HeckeDetectorFiberPartition

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def calibrationRowModulus (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : Id :=
  1*Ideal.span {B}*Ideal.span {(72:O)}*Ideal.span {D.numeratorGood}

def periodicCalibrationXi (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : O→*ℂ :=
  C.residueMonoid*actualPeriodicRow 1 B D.numeratorUnit D.numeratorLambda D.numeratorTwo
    D.numeratorGood D.numeratorSupported

def lowPeriodicBase (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) : O→*ℂ :=
  rayMonoid χ*targetMonoid η*conjugateMonoid (periodicCalibrationXi C B D)*reciprocityPhaseMonoid s hs

def lowBaseModulus (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) : Id :=
  η.modulus*(Ideal.span {C.generator}*calibrationRowModulus C B D)*Ideal.span {(4:O)}

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def calibrationLowData (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) :
    GoodMaskRowData (calibrationForSet S hS).generator 1 (calibrationForSet S hS).generator :=
  goodMaskRowData _ 1 _ (calibrationForSet S hS).generator_ne_zero one_ne_zero
    (calibrationForSet S hS).generator_ne_zero

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ConcreteTraceCRT ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def gramPeriodicMonoid (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : O→*ℂ :=
  conjugateMonoid C.residueMonoid*actualPeriodicRow 1 B D.numeratorUnit D.numeratorLambda D.numeratorTwo
    D.numeratorGood D.numeratorSupported

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
local notation "O" => HeckeFamily.O

structure SourceData {Δ : ℝ} (D : HighData Δ) where
  S : Finset (Ideal O)
  exclusions : SourceExclusions S
  maximal : ∀P∈S,P.IsMaximal
  first : FirstTail (4*D.e) S
  w : ℝ→ℝ
  W : SchwartzMap ℝ ℂ
  smooth : ContDiff ℝ ∞ w
  compact : HasCompactSupport w
  support : Function.support w⊆Set.Ioo 1 2
  positive_support : tsupport w⊆Set.Ioi 0
  bounded : ∀x,0≤w x ∧ w x≤1
  nonzero : w≠0
  complex_eq : ∀x,W x=(w x:ℂ)
  complex_nonzero : W≠0
  complex_support : Function.support W⊆Set.Icc 1 2
  real : ∀x,(W x).im=0
  nonnegative : ∀x,0≤(W x).re

def SourceData.modulus {Δ : ℝ} {D : HighData Δ} (F : SourceData D) : Ideal O := ∏P∈F.S,P

instance instNeZeroIdealOModulus {Δ : ℝ} {D : HighData Δ} (F : SourceData D) : NeZero F.modulus :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

instance instFiniteQuotientOIdealModulus {Δ : ℝ} {D : HighData Δ} (F : SourceData D) : Finite (O ⧸ F.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne F.modulus)

def SourceData.probe {Δ : ℝ} {D : HighData Δ} (F : SourceData D) (η : Character) : ℝ→ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  normalizedProbe F.modulus ⊤ F.S F.maximal D.ell 1 2 (fun _=>F.w) F.W F.W η

end SevenEighths.ProbeFinalAssembly

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialPhysicalSlots
open DetectorDictionaryInverseMarkedPadding HeckeDetectorCoefficientTransfer
open InverseInitialConjugateEnergy
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
  {U a ε tstar T allowance:ℝ}{i:ℕ}

def fiberLists (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot)
    (s:selected) : Finset (Ideal O) :=
  livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace SevenEighths.DetectorDictionaryInverseRawInitialGates
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialRayAttachment InverseInitialExcludedPeriod
open InverseInitialExcludedPool
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge UniqueFactorizationMonoid IdealMobiusDivisorSum
open DetectorDictionaryInverseRawGeometry
local notation "O"=>HeckeFamily.O

def basePeriod (data:RowData):ℕ:=(baseCharacter data).period

def excluded (data:RowData):Finset (Ideal O):=reflectionExcludedPrimes (basePeriod data)

def deletedBase (data:RowData):Character:=
  (baseCharacter data).excludePrimes (excluded data) (reflectionExcludedPrimes_prime (basePeriod data))

def completeCutoff (H b Btree cap:ℝ):ℕ:=⌈max (Btree*H^(cap+1)) (b*H)⌉₊

end SevenEighths.DetectorDictionaryInverseRawInitialGates

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialConjugateEnergy InverseInitialPhysicalSlots
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPeriod
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

def deletedSelectedSource (data:RowData)(M:Ideal O)[NeZero M]
    (H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (Z r σ freq bW:ℝ)(b ell:ι→ℝ)(ζ:ι→ℂ)(u:O) : ℂ :=
  ∑p∈Fintype.piFinset (fun i=>livePrimes M H (V i) (b i) (Z^(ell i))),
    (star (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))/
      idealCoeff (deletedBase data) (∏i,p i))*
    originalTotalPolynomial
      ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊).filter Supported)
      (∏i,p i) (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
      (twistedProfile W σ freq) Z r (∑i,ell i) u

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseRawInitialEnergy
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRawDictionary InverseInitialExcludedEnergy
open DetectorDictionaryInverseRawInitialGates CanonicalQuadraticSieve ConcreteTraceCRT
open ActualEisensteinCubic IdealMobiusDivisorSum CanonicalRowCompletion CanonicalCoefficientClass
local notation "O"=>HeckeFamily.O

def initialFunction (data:RowData)(W:ℝ→ℂ)(H b Btree cap D sigma freq:ℝ)(j:Ideal O):O→ℂ:=
  originalTotalPolynomial
    (InitialMeanSquare.outsideSquarefreeIdeals (excluded data) (completeCutoff H b Btree cap))
    1 (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
    (twistedProfile W sigma freq) H (Real.logb H (D/(j.absNorm:ℝ))) 0

end SevenEighths.DetectorDictionaryInverseRawInitialEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorTransform
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve HeckeFamily CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentSupportedCorrelation IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem residualPool_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : residualPool C hC (supportedColumns S)) : Supported (a:Ideal O) := by
  have ha := (Finset.mem_filter.mp ((mem_residualPool C hC (supportedColumns S) a).mp a.property)).2
  exact ((supported_mul_iff C a).mp ha).2

theorem commonLabels_supported (S : Finset (Ideal O))
    (p : commonLabels (supportedColumns S) (supportedColumns S)) :
    Supported p.val.1 ∧ Supported p.val.2 := by
  obtain ⟨q,hq,he⟩ := Finset.mem_image.mp p.property
  have hq₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
  have hq₂ := (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).2
  rw [← he]
  exact ⟨commonPart_supported _ _ hq₁,commonPart_supported _ _ hq₂⟩

end SevenEighths.CenteredMomentFirstSectorTransform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocationBox
open CenteredMomentSupport
open CenteredMomentFirstSectors IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def sourceFiber (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) :
    Finset (ι → Ideal O) :=
  (Fintype.piFinset S).filter (fun v => ∀ i,supportExtract (v i) (primeSupport C)=B i)

def residualBoxes (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O)
    (hB : ∀ i,B i≠0) : Finset (ι → Ideal O) :=
  Fintype.piFinset (fun i => (residualPool (B i) (hB i) (S i)).filter (IsCoprime C))

end SevenEighths.CenteredMomentCommonAllocationBox

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceLiveColumn
open CenteredMomentRemainingBox CenteredMomentCommonProfile
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationBox CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance instDecidableEqSumFinOfNatNat_solutions : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def frozenCoefficient (B : Tuple ι) (C R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) : ℂ :=
  (∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
    ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
    (if IsCoprime C R then 1 else 0)

def liveBox (S : (ι ⊕ Fin 2) → Finset (Ideal O)) (B : Tuple ι) (hB : ∀ i,B i≠0) :
    Finset (Tuple (liveIndices B)) :=
  Fintype.piFinset (remainingSets B (fun i => residualPool (B i) (hB i) (S i)))

def liveProfile (B : Tuple ι) (C R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    Tuple (liveIndices B) → ℂ :=
  profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
    (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1

end SevenEighths.CenteredMomentSourceLiveColumn

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceEnergy
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def secondSourceKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' h : O,(primaryGaussRow I h*star (primaryGaussRow J h))*
    W (‖ConcreteTraceCRT.eisEmbedding h‖^2/K)

end SevenEighths.CenteredMomentSecondSourceEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform
open CenteredMomentSecondScaled CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentFixedRay CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def sectorPool (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O)) : Finset (Ideal O) :=
  (residualPool C hC (supportedColumns S)).filter (IsCoprime C)

theorem sectorPool_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Supported (a:Ideal O) :=
  residualPool_supported C hC S ⟨a,(Finset.mem_filter.mp a.property).1⟩

def sectorElement (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : O := primaryGenerator a

end SevenEighths.CenteredMomentSecondSectorColumns

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentSupportedCorrelation
open CenteredMomentSourceRow UniqueFactorizationMonoid CenteredMomentSupport CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

def commonPrime (C D : Ideal O) (P : CommonIndex C D) : O := primaryGenerator P.val

def commonFrequencyGenerator (C D : Ideal O) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^min (leftExponent C D P) (rightExponent C D P)

end SevenEighths.CenteredMomentSecondCanonical

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalFrequency
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondLedger
open CenteredMomentPartition CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

def canonicalPartition (C D : Ideal O) (U : Finset (CommonIndex C D)) (w : O) : Prop :=
  actualUnitSet (commonPrime C D) (leftExponent C D) (rightExponent C D) w=U

def canonicalPartitionScalar (C D : Ideal O) (U : Finset (CommonIndex C D)) (w : O) : ℂ :=
  if canonicalPartition C D U w then
    (partitionNormalizer (commonPrime C D) (leftExponent C D) (rightExponent C D) U:ℂ)⁻¹ else 0

end SevenEighths.CenteredMomentSecondCanonicalFrequency

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalNonunit
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentCanonicalFirst
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentProductCRT
open CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

def equalActiveSet (C D : Ideal O) : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P=>leftExponent C D P=rightExponent C D P ∧ ¬6∣leftExponent C D P)

def nonunitPartitionSet (C D : Ideal O) (U : Finset (CommonIndex C D)) : Finset (CommonIndex C D) :=
  equalActiveSet C D\U

def nonunitFrequencyGenerator (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  ∏ P∈nonunitPartitionSet C D U,commonPrime C D P

end SevenEighths.CenteredMomentSecondCanonicalNonunit

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def firstNominalScale (I J E : Ideal O) (K X : ℝ) : ℝ :=
  (Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*X^2 /
    (K*(Ideal.absNorm (commonPart I J):ℝ)*(Ideal.absNorm (commonPart J I):ℝ))

theorem norm_pos (I : Ideal O) (hI : I≠0) : 0<(Ideal.absNorm I:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)

end SevenEighths.CenteredMomentFirstScale

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstDiscardedEnergy
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson ConcretePrimeRowBridge
open CenteredMomentFirstReduced CenteredMomentSectorLocalization CenteredMomentCorrelation
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentActive
open CenteredMomentCompleteCommon IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def canonicalDiscardedTerm (I J : Ideal O)
    (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
      (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

def inactiveSubsets (I J : Ideal O) : Finset (Finset (CommonIndex I J)) :=
  (principalSupport (Finset.univ : Finset (CommonIndex I J)) (leftExponent I J) (rightExponent I J)).powerset

def canonicalDiscardedPair (I J : Ideal O)
    (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K Tsec Z ξ

end SevenEighths.CenteredMomentFirstDiscardedEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstTailAggregate
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

def discardedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

end SevenEighths.CenteredMomentFirstTailAggregate

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.HeckeMaskDescent
open HeckeFamily CenteredExceptionalProfile CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem exists_coprime_shift (a c r : O) (hac : IsCoprime a c) (hr : r ≠ 0) :
    ∃ t : O, IsCoprime (a+t*c) r := by
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s := (normalizedFactors r).filter (fun p => ¬p ∣ a)
  refine ⟨s.prod, IsCoprime.symm ?_⟩
  apply isCoprime_of_prime_dvd (by rintro ⟨h,-⟩; exact hr h)
  intro p hp hpr hpnew
  by_cases hpa : p ∣ a
  · have hpc : ¬p ∣ c := fun h => hp.not_isUnit (hac.isUnit_of_dvd' hpa h)
    have hps : ¬p ∣ s.prod := by
      intro h
      obtain ⟨q,hq,hpq⟩ := hp.exists_mem_multiset_dvd h
      obtain ⟨hqr,hqa⟩ := Multiset.mem_filter.mp hq
      exact hqa ((hp.associated_of_dvd (prime_of_normalized_factor q hqr) hpq).dvd'.trans hpa)
    have ht : p ∣ s.prod*c := by convert (preTransparency := .instances) dvd_sub hpnew hpa using 1 ; ring
    exact (hp.dvd_or_dvd ht).elim hps hpc
  · obtain ⟨q,hq,hpq⟩ := exists_mem_normalizedFactors_of_dvd hr hp.irreducible hpr
    have hqs : q ∈ s := Multiset.mem_filter.mpr ⟨hq,fun h => hpa (hpq.dvd.trans h)⟩
    have ht : p ∣ s.prod*c := dvd_mul_of_dvd_left (hpq.dvd.trans (Multiset.dvd_prod hqs)) c
    exact hpa (by convert (preTransparency := .instances) dvd_sub hpnew ht using 1 ; ring)

theorem exists_primitive_above (χ : Character) (Q : Ideal O)
    (hdesc : FiniteConductor.FactorsThroughIdeal χ.residue
      (Q.map (Ideal.Quotient.mk χ.modulus))) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ ψ := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  obtain ⟨K,φ,hMK,hQK,hK,hprim,hnorm,hmask⟩ :=
    ConductorPresentation.exists_primitive_presentation_above_quotient
      χ.modulus χ.residue (Q.map (Ideal.Quotient.mk χ.modulus)) hdesc
  have hu : IdealCharacter.UnitInvariant K φ := by
    intro u
    have h := hmask (u : O)
    simpa only [χ.unit_trivial u,u.isUnit.map (Ideal.Quotient.mk χ.modulus),ite_true] using h.symm
  refine ⟨Character.ofResidue K hK φ hu,hprim,?_,?_⟩
  · exact (Ideal.le_comap_map).trans hQK
  · exact IdealCharacter.ofResidue_source_mask χ.modulus K χ.residue φ χ.unit_trivial hu hmask

theorem descent_of_mask (χ χ' ψ : Character) (r : O) (hr : r ≠ 0)
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0)
    (hind : InducedBy χ' ψ) :
    FiniteConductor.FactorsThroughIdeal χ.residue
      (ψ.modulus.map (Ideal.Quotient.mk χ.modulus)) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  rw [FiniteConductor.factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨q,hq,hqu⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk χ.modulus) Ideal.Quotient.mk_surjective).mp hu
  let a : O := 1+q
  have ha : Ideal.Quotient.mk χ.modulus a = (u : O ⧸ χ.modulus) := by
    dsimp [a];rw [map_add,map_one,hqu];ring
  have hψa : Ideal.Quotient.mk ψ.modulus a = 1 := by
    simp only [a,map_add,map_one,Ideal.Quotient.eq_zero_iff_mem.mpr hq,add_zero]
  let c := idealGenerator (χ.modulus*ψ.modulus)
  have hc : IsCoprime a c := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [show Ideal.span {c}=χ.modulus*ψ.modulus from span_idealGenerator _]
    apply IsCoprime.mul_right
    · exact (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (ha ▸ u.isUnit)
    · exact (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hψa ▸ isUnit_one)
  obtain ⟨t,htall⟩ := exists_coprime_shift a c (r*goodLambda) hc
    (mul_ne_zero hr goodLambda_prime.ne_zero)
  have ht := htall.of_mul_right_left
  let n := a+t*c
  have hmem : c ∈ χ.modulus*ψ.modulus := by
    rw [← span_idealGenerator (χ.modulus*ψ.modulus)]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hnχ : Ideal.Quotient.mk χ.modulus n = (u : O ⧸ χ.modulus) := by
    dsimp [n];rw [map_add,map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_left hmem),mul_zero,add_zero,ha]
  have hnψ : Ideal.Quotient.mk ψ.modulus n = 1 := by
    dsimp [n];rw [map_add,map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_right hmem),mul_zero,add_zero,hψa]
  have hnχ' : elementCoeff χ' n ≠ 0 := by
    rw [he n,if_pos ht]
    exact MulChar.apply_ne_zero_iff.mpr (hnχ ▸ u.isUnit)
  have hn0 : n ≠ 0 := by
    intro hz
    have hunit : IsUnit goodLambda := (htall.of_mul_right_right).isUnit_of_dvd'
      (by change goodLambda ∣ n; rw [hz]; exact dvd_zero _) (dvd_refl _)
    exact goodLambda_prime.not_isUnit hunit
  have hcop : IsCoprime (Ideal.span {n}) χ'.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hnχ')
  have heq := elementCoeff_eq_of_inducedBy χ' ψ hind n hn0 hcop
  rw [he n,if_pos ht] at heq
  change χ.residue (Ideal.Quotient.mk χ.modulus n) = ψ.residue (Ideal.Quotient.mk ψ.modulus n) at heq
  simpa only [hnχ,hnψ,map_one] using heq

theorem inducedBy_mask (χ χ' ψ : Character) (r : O)
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0)
    (hind : InducedBy χ ψ) : InducedBy χ' ψ := by
  intro I
  by_cases hI : I = 0
  · simp only [hI,map_zero,ite_self]
  by_cases hc : IsCoprime I χ'.modulus
  · have hn' := CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I |>.mpr ⟨hI,hc⟩
    let n := idealGenerator I
    have hn0 : n ≠ 0 := idealGenerator_ne_zero I hI
    have hspan : Ideal.span {n} = I := span_idealGenerator I
    have hval' : elementCoeff χ' n = idealCoeff χ' I := by
      rw [← idealCoeff_span χ' hn0,hspan]
    have hval : elementCoeff χ n = idealCoeff χ I := by
      rw [← idealCoeff_span χ hn0,hspan]
    have hm := he n
    have hcr : IsCoprime n r := by
      by_contra hr
      rw [if_neg hr,hval'] at hm
      exact hn' hm
    rw [if_pos hcr,hval',hval] at hm
    have hn := hm ▸ hn'
    have hcχ := (CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ I).mp hn |>.2
    rw [if_pos hc,hm,hind I,if_pos hcχ]
  · have hz : idealCoeff χ' I = 0 := by
      by_contra hn
      exact hc ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I).mp hn).2
    rw [if_neg hc,hz]

theorem fixed_inducing_mask_iff (χ χ' : Character) (r : O) (hr : r ≠ 0)
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0) (Q : Ideal O) :
    (∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ' ψ) ↔
    (∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ ψ) := by
  constructor
  · rintro ⟨ψ,hprim,hQ,hind⟩
    obtain ⟨ρ,hρ,hmod,hindρ⟩ := exists_primitive_above χ ψ.modulus
      (descent_of_mask χ χ' ψ r hr he hind)
    exact ⟨ρ,hρ,hQ.trans hmod,hindρ⟩
  · rintro ⟨ψ,hprim,hQ,hind⟩
    exact ⟨ψ,hprim,hQ,inducedBy_mask χ χ' ψ r he hind⟩
end SevenEighths.HeckeMaskDescent

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFixedRowMask
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem row_mask_mul (η : Character) (m r A z n : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    rowTwist (elementHom η) (m*r) 1 (A*z) n =
      if IsCoprime n r then rowTwist (elementHom η) m 1 (A*z) n else 0 := by
  by_cases hs : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ _ _ _ _ hs,
      rowTwist_extract_sixth_mask _ _ _ _ _ hs]
    change elementHom η n * (if IsCoprime (m*r) n then (1:ℂ) else 0) * _ = _
    rw [IsCoprime.mul_left_iff]
    by_cases hm : IsCoprime m n <;> by_cases hr : IsCoprime n r <;>
      simp [coprimalityMask,hm,hr,show IsCoprime r n ↔ IsCoprime n r from isCoprime_comm]
  · rw [rowTwist_zero_of_not_supported _ _ _ _ _
        (hmLam.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _)) hs,
      rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hs]
    split_ifs <;> rfl

theorem fixedInducingRow_mul_mask_iff (η : Character) (Q : Ideal O)
    (m r A z : O) (hm : m ≠ 0) (hr : r ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow η Q (m*r) A z ↔ FixedInducingRow η Q m A z := by
  obtain ⟨χ,hχ⟩ := exists_row_character η m 1 (A*z) hm one_ne_zero
    (mul_ne_zero hA hz) hmLam hm2
  obtain ⟨χ',hχ'⟩ := exists_row_character η (m*r) 1 (A*z) (mul_ne_zero hm hr)
    one_ne_zero (mul_ne_zero hA hz) (hmLam.trans (dvd_mul_right _ _))
      (hm2.trans (dvd_mul_right _ _))
  have hmask (n : O) : elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0 := by
    rw [hχ' n,hχ n,row_mask_mul η m r A z n hmLam hm2]
  have transport (ρ : Character) (mask : O)
      (hρ : ∀ n,elementCoeff ρ n=rowTwist (elementHom η) mask 1 (A*z) n) :
      FixedInducingRow η Q mask A z ↔
        ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
          Q ≤ ψ.modulus ∧ InducedBy ρ ψ := by
    constructor
    · rintro ⟨ρ₀,ψ,hprim,hind,hQ,hρ₀⟩
      exact ⟨ψ,hprim,hQ,CenteredMomentHeckeVolume.inducedBy_of_elementCoeff_eq
        ρ₀ ρ ψ (fun n => (hρ n).trans (hρ₀ n).symm) hind⟩
    · rintro ⟨ψ,hprim,hQ,hind⟩
      exact ⟨ρ,ψ,hprim,hind,hQ,hρ⟩
  rw [transport χ' (m*r) hχ',transport χ m hχ]
  exact HeckeMaskDescent.fixed_inducing_mask_iff χ χ' r hr hmask Q
end SevenEighths.CenteredMomentFixedRowMask

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentRestrictedEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion CenteredMomentRowNorm
open CenteredMomentCauchy CenteredMomentSmooth
open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def restrictedEnergy {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (c : α → ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, if keep z then ‖rowPolynomial S a c z‖^2*(W (‖eisEmbedding z‖^2/K)).re else 0

def nonexceptional (η : HeckeFamily.Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (m A₀ z : O) : Prop :=
  z ≠ 0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow
    (CenteredMomentChildRows.childCharacter η χ) Q m A₀ z

end SevenEighths.CenteredMomentRestrictedEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedSource
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedDomain
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentOriginalChildEnergy
local notation "O" => ActualEisensteinCubic.O

def sourceRestrictedEnergy (keep : O → Prop) (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  restrictedEnergy keep Finset.univ (sourceGenerator Q)
    (fun I : supportedColumns Q => c I*f I) W K

variable {ι : Type*} [Fintype ι]
local instance instDecidableEqSumFinOfNatNat_solutions : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentRestrictedSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRectangle
open ActualEisensteinCubic HeckeFamily CenteredMomentHeckeExpansion CenteredMomentRectangle
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentRemainingBox
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def tuplePools (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O)) :
    (ι⊕Fin 2)→Finset (Ideal O) := Sum.elim slots (fun j=>if j=0 then S₁ else S₂)

def tuplePool (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O)) : Finset (Tuple ι) :=
  Fintype.piFinset (tuplePools slots S₁ S₂)

def pack (v : ι→Ideal O) (I J : Ideal O) : Tuple ι :=
  Sum.elim v (fun j=>if j=0 then I else J)

omit [Fintype ι] in
@[simp] theorem pack_slot (v : ι→Ideal O) (I J : Ideal O) (i : ι) :
    pack v I J (Sum.inl i)=v i := rfl
omit [Fintype ι] in
@[simp] theorem pack_left (v : ι→Ideal O) (I J : Ideal O) :
    pack v I J (Sum.inr 0)=I := by simp [pack]
omit [Fintype ι] in
@[simp] theorem pack_right (v : ι→Ideal O) (I J : Ideal O) :
    pack v I J (Sum.inr 1)=J := by simp [pack]

def tuplePoolEquiv (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O)) :
    tuplePool slots S₁ S₂ ≃ ((∀ i,slots i)×S₁×S₂) where
  toFun v := ((fun i=>⟨v.val (Sum.inl i),Fintype.mem_piFinset.mp v.property (Sum.inl i)⟩),
    ⟨v.val (Sum.inr 0),by simpa [tuplePools] using Fintype.mem_piFinset.mp v.property (Sum.inr 0)⟩,
    ⟨v.val (Sum.inr 1),by simpa [tuplePools] using Fintype.mem_piFinset.mp v.property (Sum.inr 1)⟩)
  invFun v := ⟨pack (fun i=>v.1 i) v.2.1 v.2.2,by
    apply Fintype.mem_piFinset.mpr
    intro i
    cases i with
    | inl i => exact (v.1 i).property
    | inr j => fin_cases j <;> simp [pack,tuplePools]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    cases i with
    | inl i => rfl
    | inr j => fin_cases j <;> rfl
  right_inv v := rfl

def PlainCoverage (S : Finset (Ideal O)) (W : ℝ→ℂ) (B : Ideal O) (X Y : ℝ) : Prop :=
  ∀ I, W ((Ideal.absNorm (B*I):ℝ)/X)≠0 ∨ W ((Ideal.absNorm (B*I):ℝ)/Y)≠0 → I∈S

def fullMaskedRectangle (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (R L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) : ℂ :=
  ∑ v : (∀ i,slots i),(∏ i,ν i (v i)*Wslot i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      (if IsCoprime ((∏ i,(v i:Ideal O))*I*J) R then (1:ℂ) else 0)*
      (if L∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
      idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)

theorem plainCoverage_residualPool (S : Finset (Ideal O)) (W : ℝ→ℂ)
    (B C : Ideal O) (hC : C≠0) (X Y : ℝ) (h : PlainCoverage S W B X Y) :
    PlainCoverage (residualPool C hC S) W (B*C) X Y := by
  intro I hi
  apply (mem_residualPool C hC S I).mpr
  apply h (C*I)
  simpa only [mul_assoc] using hi

def plainSupportPool (b X Y : ℝ) : Finset (Ideal O) := idealBall (b*X)∪idealBall (b*Y)

theorem plainSupportPool_coverage (W : ℝ→ℂ) (b X Y : ℝ)
    (hW₀ : W 0=0) (hs : Function.support W⊆Set.Iic b) (hX : 0<X) (hY : 0<Y) :
    PlainCoverage (plainSupportPool b X Y) W 1 X Y := by
  intro I hi
  simp only [one_mul] at hi
  have cover (Q : ℝ) (hQ : 0<Q) (hne : W ((Ideal.absNorm I:ℝ)/Q)≠0) :
      I∈idealBall (b*Q) := by
    apply (mem_idealBall _ _).mpr
    constructor
    · intro hI
      subst I
      apply hne
      simp only [map_zero,Nat.cast_zero,zero_div,hW₀]
    · exact (div_le_iff₀ hQ).mp (hs hne)
  obtain hi|hi := hi
  · exact Finset.mem_union_left _ (cover X hX hi)
  · exact Finset.mem_union_right _ (cover Y hY hi)

end SevenEighths.CenteredMomentSourceRectangle

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonRadialData
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform CenteredMomentCommonRawScale
open CenteredMomentRestrictedSource CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors ConcretePrimeRowBridge CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

structure Input (ι:Type*) [Fintype ι] extends Data ι where
  plain₁ : Finset (Ideal O)
  plain₂ : Finset (Ideal O)
  plain₁_ne : ∀I∈plain₁,I≠0
  plain₂_ne : ∀I∈plain₂,I≠0
  coverage₁ : PlainCoverage plain₁ W₁ 1 X₁ Y₁
  coverage₂ : PlainCoverage plain₂ W₂ 1 X₂ Y₂
  ν_bound : ∀i I,‖ν i I‖≤1
  W_bound : ∀i x,‖W i x‖≤M i
  lower : ℝ
  upper : ℝ
  lower_pos : 0<lower
  lower_le : ∀i,lower≤lo i
  upper_ge : ∀i,hi i≤upper

 def Input.pools (s:Input ι) : (ι⊕Fin 2)→Finset (Ideal O) :=
  Sum.elim s.slots (fun j=>if j=0 then s.plain₁ else s.plain₂)

omit [DecidableEq ι] in
lemma alloc_ne (s:Input ι) (C:Ideal O) (B:actualAllocations s.pools C)
    (j:ι⊕Fin 2) : B.val j≠0 :=
  (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1 j

omit [DecidableEq ι] in
lemma alloc_norm_pos (s:Input ι) (C:Ideal O) (B:actualAllocations s.pools C)
    (j:ι⊕Fin 2) : (0:ℝ)<Ideal.absNorm (B.val j) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B j))

 def commonData (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C) : Data (liveIndices B.val) where
  η:=s.η
  m:=fixedBadMask*idealGenerator (R*C)
  A:=1
  t:=s.t
  slots:=fun i=>s.slots i.val
  prime:=fun i I hI=>s.prime i.val I hI
  ν:=fun i=>s.ν i.val
  W:=fun i=>s.W i.val
  lo:=fun i=>s.lo i.val
  hi:=fun i=>s.hi i.val
  P:=fun i=>s.P i.val
  lo_pos:=fun i=>s.lo_pos i.val
  P_pos:=fun i=>s.P_pos i.val
  support:=fun i=>s.support i.val
  W₁:=s.W₁
  W₂:=s.W₂
  X₁:=s.X₁/Ideal.absNorm (B.val (Sum.inr 0))
  X₂:=s.X₂/Ideal.absNorm (B.val (Sum.inr 1))
  Y₁:=s.Y₁/Ideal.absNorm (B.val (Sum.inr 0))
  Y₂:=s.Y₂/Ideal.absNorm (B.val (Sum.inr 1))
  M:=fun i=>s.M i.val
  M_ge_one:=fun i=>s.M_ge_one i.val
  coefficient_bound:=fun i I hI=>s.coefficient_bound i.val I hI
  b₁:=s.b₁
  b₂:=s.b₂
  support₁:=s.support₁
  support₂:=s.support₂
  X₁_pos:=div_pos s.X₁_pos (alloc_norm_pos s C B _)
  X₂_pos:=div_pos s.X₂_pos (alloc_norm_pos s C B _)
  Y₁_pos:=div_pos s.Y₁_pos (alloc_norm_pos s C B _)
  Y₂_pos:=div_pos s.Y₂_pos (alloc_norm_pos s C B _)
  same_product:=by rw [div_mul_div_comm,div_mul_div_comm,s.same_product]
  rows:=∅
  weight:=fun _=>0
  weight_nonneg:=by simp

end SevenEighths.CenteredMomentCommonRadialData

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyState
open HeckeFamily CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
open CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

structure NaturalState (Z Bmask bΦ:ℝ) where
  character : Character
  fixedModulus : Ideal O
  puncture : Ideal O
  radial : Radial
  rowWidth : ℝ
  characterWidth : ℝ
  base_ge_one : 1≤Z
  row_nonneg : 0≤ rowWidth
  character_nonneg : 0≤ characterWidth
  scale_eq : radial.scale=Z^rowWidth
  modulus_bound : (character.modulus.absNorm:ℝ)≤Z^characterWidth
  puncture_ne_zero : puncture≠0
  puncture_bound : (puncture.absNorm:ℝ)≤Z^Bmask
  radial_support : Function.support (radial.profile:ℝ→ℂ)⊆Set.Iic bΦ
  row_ne_zero : ∀z,radial.keep z→z≠0
  nonexceptional : ∀z,radial.keep z→
    ¬FixedInducingRow character fixedModulus
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator puncture) 1 z

namespace NaturalState
variable {Z Bmask bΦ:ℝ}
def width (s:NaturalState Z Bmask bΦ):ℝ := s.rowWidth+s.characterWidth

def mask (s:NaturalState Z Bmask bΦ):O :=
  fixedBadMask*ConcretePrimeRowBridge.idealGenerator s.puncture

def plainEnergy (s:NaturalState Z Bmask bΦ) {a b:ℝ} (p:Profiles a b)
    (t X₁ X₂:ℝ):ℝ :=
  energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
    X₁ X₂ s.radial.keep s.radial.profile s.radial.scale

end NaturalState

def ZeroBound (Q:Ideal O) (a b bΦ Bmask M ε:ℝ)(degree:ℕ)(S:Finset (ℕ×ℕ))(C Z₀:ℝ):Prop :=
  ∀Z:ℝ,Z₀≤Z→∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→
    s.plainEnergy p t X₁ X₂≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree*
        Z^(s.width+ε)

end SevenEighths.CenteredMomentEnergyState

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstLocalization
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentFirstTailAggregate
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion
local notation "O" => ActualEisensteinCubic.O

def canonicalRetainedTerm (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
      (retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

def canonicalZeroTerm (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*
      (tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
        (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) 0*paperRadialFourier W 0))

def canonicalRetainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalRetainedTerm I J hI hJ E W K Tsec Z ξ

def canonicalZeroPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalZeroTerm I J hI hJ E W K

def retainedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalRetainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

def zeroEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalZeroPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K

end SevenEighths.CenteredMomentFirstLocalization

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer HeckeDetectorRawFiber HeckeDetectorRowwisePolynomial
open HeckeDetectorDyadicProfiles CenteredMomentRetainedEnergy
open CenteredMomentPrimeSlot ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def detectorPositiveRow (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (selected : Finset Slot) (j k : ℕ) (σ t : ℝ) (u : FreeRow) : ℂ :=
  positiveSlotRow η rowMaskElement 1 u.val
    (twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (twistProfile (orientedProfile F.reverse ((logProfile^[k]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (fun s : selected=>primePool M H (F.upper s.val) (U^(F.widths s.val)))
    (fun s : selected=>physicalSlotCoefficient η (F.profile s.val) (U^(F.widths s.val)) (F.external s.val))
    (fun s : selected=>U^(F.widths s.val)) 0 (U^F.m) (U^F.m)

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {Δ : ℝ} {D : Parameters.HighData Δ}

def sourceFixedIdeal (F : ProbeFinalAssembly.SourceData D) : Ideal O :=
  F.modulus⊓Ideal.span {(72:O)}

def sourceExceptional (F : ProbeFinalAssembly.SourceData D) (η : Character) (u : FreeRow) : Prop :=
  FixedInducingRow η (internalQ (sourceFixedIdeal F) η)
    (fixedBadMask*idealGenerator 1) 1 u.val

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentEnergyBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound
local notation "O"=>HeckeFamily.O

def length (Z X:ℝ):ℝ:=Real.logb Z (max 1 X)

def ZeroAt (Q:Ideal O)(a b bΦ Bmask L M ε Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
      (1+‖t‖)^degree*Z^(s.width+ε)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def PositiveAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
    0≤height→(∀i,|v i|≤height)→
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀→s.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε)

end SevenEighths.CenteredMomentEnergyBands

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyBandMonotonicity
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

def widenState {Z B b B' b':ℝ}(s:NaturalState Z B b)(hB:B≤B')(hb:b≤b'):
    NaturalState Z B' b':=
  {s with
    puncture_bound:=s.puncture_bound.trans (Real.rpow_le_rpow_of_exponent_le s.base_ge_one hB)
    radial_support:=fun _x hx=>le_trans (s.radial_support hx) hb}

def widenProfiles {a b a' b':ℝ}(p:Profiles a b)(ha:a'≤a)(hb:b≤b'):Profiles a' b' where
  profile:=p.profile
  support:=fun i _x hx=>⟨ha.trans (p.support i hx).1,(p.support i hx).2.trans hb⟩

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyBandMonotonicity

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationGlobal
local notation "O" => ActualEisensteinCubic.O

def eligiblePairs (rows P : Finset O) (allow : O → O → Prop) : Finset (O × O) :=
  (rows.product P).filter (fun x => allow x.1 x.2)

def outputRow (x : O × O) : O := x.2^6*x.1

def errorEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (h p : O) : ℝ :=
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h‖^2 +
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h‖^2 +
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h‖^2

end SevenEighths.CenteredMomentAmplificationEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourceDomain
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal
open CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

def residualIdeal (p : O) (hp : Prime p) (I : Ideal O) : Ideal O :=
  if hI : Supported I then Ideal.span {primeRemainder p hp (primaryGenerator I)
    (supported_primaryGenerator_ne_zero I hI)} else 0

def valuationColumns (S : Finset (Ideal O)) (p : O) (k : ℕ) : Finset (Ideal O) :=
  (supportedColumns S).filter (fun I => multiplicity p (primaryGenerator I)=k)

def residualColumns (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ) : Finset (Ideal O) :=
  (valuationColumns S p k).image (residualIdeal p hp)

end SevenEighths.CenteredMomentAmplificationSourceDomain

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentFirstAmplificationChoice
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentSectorLocalization CenteredMomentPrimePool
open CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow
open CenteredMomentAmplificationOriginalErrors CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationGlobal
local notation "O" => ActualEisensteinCubic.O

abbrev ballProfile : 𝓢(ℝ,ℂ) := QuadraticInitialBound.sieveCutoff

theorem ballProfile_nonneg (x : ℝ) : 0 ≤ (ballProfile x).re := by
  simpa only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,Complex.ofReal_re]
    using (QuadraticInitialBound.sieveBump.nonneg (x:=x))

def primeTest : ContDiffBump (3/4 : ℝ) where
  rIn := 1/16
  rOut := 1/8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def dyadRows (n : ℤ) : Finset O :=
  (ShortDraftLatticeCount.rowNormBall ⌈dyadicScale n⌉₊).filter
    (fun h => dyadicWeight n (normValue h)≠0)

@[simp] theorem mem_dyadRows (n : ℤ) (h : O) :
    h∈dyadRows n ↔ dyadicWeight n (normValue h)≠0 := by
  constructor
  · exact fun hh => (Finset.mem_filter.mp hh).2
  · intro hh
    refine Finset.mem_filter.mpr ⟨?_,hh⟩
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    have hn := (dyadicWeight_support n hh).2.le.trans (Nat.le_ceil (dyadicScale n))
    unfold normValue at hn
    exact_mod_cast hn

def mainGain (D0 c sigma : ℝ) : ℝ := max (D0-c) 0+2*sigma

def errorRemoval (p : O) (Z : ℝ) (k : ℕ) : ℝ :=
  (k:ℝ)*Real.logb Z (normValue p)

def errorMoving (p : O) (Z : ℝ) (k : ℕ) : ℝ :=
  if k=6 then 0 else Real.logb Z (normValue p)

def errorGain (D0 c sigma Z : ℝ) (p : O) (k : ℕ) : ℝ :=
  max (D0-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma

open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentOriginalChildEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationLiveMask CenteredMomentHeckeExpansion
open ConcretePrimeRowBridge CanonicalRowCompletion RayFourExpansion
open HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentAmplificationActiveFactor

local instance instDecidableEqSumFinOfNatNat_solutions {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

structure OriginalData (ι : Type*) [Fintype ι] where
  S : (ι ⊕ Fin 2) → Finset (Ideal O)
  R : Ideal O
  s : Ideal O
  nu : ι → Ideal O → ℂ
  slot : ι → ℝ → ℂ
  lengths : ι → ℝ
  W₁ : ℝ → ℂ
  W₂ : ℝ → ℂ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  B₁ : Ideal O
  B₂ : Ideal O

namespace OriginalData
variable {ι : Type*} [Fintype ι]

def profile (D : OriginalData ι) : Tuple ι → ℂ :=
  profileCoefficient D.R D.nu D.slot D.lengths D.W₁ D.W₂
    D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂ D.s

def columns (D : OriginalData ι) : Finset (Ideal O) :=
  finiteColumns (Fintype.piFinset D.S)

def beta (D : OriginalData ι) : Ideal O → ℂ :=
  finiteColumnCoefficient (Fintype.piFinset D.S) D.profile

def coefficient (D : OriginalData ι) (η : Character) (m : O) (t T : ℝ)
    : supportedColumns D.columns → ℂ :=
  fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)

def childEnergy (D : OriginalData ι) (τ : RayCharacter → Character)
    (p : O) (n : ℕ) (t T K : ℝ) : ℝ :=
  let C := (Ideal.span {p})^(n+1)
  (16*(n+2:ℝ)*localErrorCost p n) *
    ((∑ χ : RayCharacter,∑ B : actualAllocations D.S C,
      (sourceGaussEnergy
        (finiteColumns (liveBox D.S B (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1))
        (finiteColumnCoefficient
          (liveBox D.S B (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1)
          (maskedLiveProfile B C D.R D.s D.nu D.slot D.lengths D.W₁ D.W₂
            D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂))
        (heightCoeff (τ χ) t) ballProfile K).re) /
      (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)))

end OriginalData

def errorIndex (i : Fin 3) : ℕ := ![0,5,6] i

namespace OriginalData
variable {ι : Type*} [Fintype ι]

def active (D : OriginalData ι) : OriginalData ι :=
  { D with S := fun i => match i with
    | Sum.inl j => (D.S i).filter (fun I => D.slot j ((Ideal.absNorm I:ℝ)/D.lengths j)≠0)
    | Sum.inr _ => D.S i }

end OriginalData

open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily
open CenteredMomentDescentLedger CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentRankinRadical ActualEisensteinCubic

def nominalLog (I J E : Ideal O) (K X Z : ℝ) : ℝ :=
  Real.logb Z (firstNominalScale I J E K X)

end SevenEighths.CenteredMomentFirstAmplificationChoice

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainSource
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentAddedZeroUniform
open CenteredMomentSourceRectangle
open CenteredMomentUncenteredTerminal CenteredMomentHeckeExpansion
open CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentDivisorRowEnergy
open CenteredMomentRetainedEnergy CenteredMomentRectangle
open CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentSecondHeightFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def completePool (slots : ι→Finset (Ideal O)) (b₁ b₂ X₁ X₂ : ℝ) : Finset (Tuple ι) :=
  tuplePool slots (plainSupportPool b₁ X₁ (comparisonScale b₁))
    (plainSupportPool b₂ X₂ (X₁*X₂/comparisonScale b₁))

lemma support_zero (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) : W 0=0 := by
  by_contra hn
  have := (hs hn).1
  linarith

end SevenEighths.CenteredMomentDetectorPlainSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstCommonTransport
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

theorem extracted_support (I J:Ideal O):
    commonSupport (commonPart I J) (commonPart J I)=commonSupport I J:=by
  rw [commonSupport,commonPart_support,commonPart_support,commonSupport_comm J I,Finset.inter_self]

def commonEquiv (I J:Ideal O):CommonIndex I J ≃ CommonIndex (commonPart I J) (commonPart J I) where
  toFun P:=⟨P.val,by rw [extracted_support];exact P.property⟩
  invFun P:=⟨P.val,by rw [←extracted_support I J];exact P.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

@[simp] theorem commonEquiv_val (I J:Ideal O)(P:CommonIndex I J):
    (commonEquiv I J P).val=P.val:=rfl

@[simp] theorem extracted_left (I J:Ideal O)(P:CommonIndex I J):
    leftExponent (commonPart I J) (commonPart J I) (commonEquiv I J P)=leftExponent I J P:=by
  simp only [leftExponent,commonEquiv_val,commonPart_valuation,if_pos P.property]

@[simp] theorem extracted_right (I J:Ideal O)(P:CommonIndex I J):
    rightExponent (commonPart I J) (commonPart J I) (commonEquiv I J P)=rightExponent I J P:=by
  have hp:P.val∈commonSupport J I:=by rw [commonSupport_comm];exact P.property
  simp only [rightExponent,commonEquiv_val,commonPart_valuation,if_pos hp]

def activeEquiv (I J:Ideal O):ActiveIndex I J ≃ ActiveIndex (commonPart I J) (commonPart J I) where
  toFun P:=⟨commonEquiv I J P.val,by
    simpa only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using P.property⟩
  invFun P:=⟨(commonEquiv I J).symm P.val,by
    have hp:=P.property
    have he:(commonEquiv I J) ((commonEquiv I J).symm P.val)=P.val:=(commonEquiv I J).apply_symm_apply _
    rw [←he] at hp
    simpa only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hp⟩
  left_inv P:=by apply Subtype.ext;exact (commonEquiv I J).symm_apply_apply _
  right_inv P:=by apply Subtype.ext;exact (commonEquiv I J).apply_symm_apply _

@[simp] theorem activeEquiv_prime (I J:Ideal O)(P:ActiveIndex I J):
    activePrime (commonPart I J) (commonPart J I) (activeEquiv I J P)=activePrime I J P:=rfl

@[simp] theorem activeEquiv_exponent (I J:Ideal O)(P:ActiveIndex I J):
    activeExponent (commonPart I J) (commonPart J I) (activeEquiv I J P)=activeExponent I J P:=by
  change netExponent (leftExponent _ _ (commonEquiv I J P.val))
    (rightExponent _ _ (commonEquiv I J P.val))=_
  rw [extracted_left,extracted_right]
  rfl

def mappedSubset (I J:Ideal O)(E:Finset (CommonIndex I J)):
    Finset (CommonIndex (commonPart I J) (commonPart J I)):=E.map (commonEquiv I J).toEmbedding

end SevenEighths.CenteredMomentFirstCommonTransport

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonFourierTransport
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstReduced
open CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CenteredMomentFirstLocalization CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentFirstCommonTransport
local notation "O"=>ActualEisensteinCubic.O

def retainedFourierTerm (a b r:O)(ha:a≠0)(hb:b≠0)(hr:r≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let k:=K/normValue e
  (UniqueFactorizationMonoid.moebius E:ℂ)*tripleRow a b r χa χb G e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑'h:O,
      (retainedWeight R (normValue h):ℂ)*tripleFourier a b r ha hb hr χa χb G h*
        EisensteinSchwartzPoisson.paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

def fixedRetainedTerm (C D:Ideal O)(hC:Supported C)(a b:O)
    (ha:Supported (Ideal.span {a}))(hb:Supported (Ideal.span {b}))
    (E:Finset (CommonIndex C D))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  retainedFourierTerm a b (activeConductor C D)
    (supported_element_ne_zero _ ha) (supported_element_ne_zero _ hb) (finitePrimeModulus_ne_zero _)
    (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ (activeFunction C D hC)
    (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E) (∏P∈E,P.val) W K
    (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ)

end SevenEighths.CenteredMomentFirstCommonFourierTransport

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentPrimitive IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

def columns (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O)):Finset (Ideal O):=
  (residualPool D hD (supportedColumns S)).filter (fun I=>IsCoprime C I)

lemma column_supported (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))
    (a:columns C D hD S):Supported (a:Ideal O):=
  residualPool_supported D hD S ⟨a.val,(Finset.mem_filter.mp a.property).1⟩

def element (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):O:=
  CompletedGauss.primaryGenerator a

lemma element_span (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    Ideal.span {element C D hD S a}=a:=primary_span_supported a (column_supported C D hD S a)

lemma element_supported (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    Supported (Ideal.span {element C D hD S a}):=by
  rw [element_span];exact column_supported C D hD S a

def coefficient (η:Character)(m A:O)(t:ℝ)(c:Ideal O→ℂ)(D:Ideal O)
    (I:Ideal O):ℂ:=c (D*I)*CenteredMomentHeckeExpansion.rowWeight η m A 1 t I

def inactiveWeight (C D:Ideal O)(E:Finset (CommonIndex C D)):ℂ:=
  (UniqueFactorizationMonoid.moebius (∏P∈E,P.val):ℂ)

def block (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ):ℂ:=
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
        windows V (k/‖eisEmbedding r‖^2) (‖eisEmbedding h‖^2)
          (‖eisEmbedding na‖^2) (‖eisEmbedding nb‖^2) K₀ H₀ A₀ B₀*
        EisensteinSchwartzPoisson.paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
      else 0

def scalar (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))(K A₀ B₀:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  inactiveWeight C D E * ((k:ℂ)*canonicalNormalizedGauss (activePrime C D)
    (activeCoprime C D) (activeGood C D hC) (activeExponent C D)/
      ((‖eisEmbedding (activeConductor C D)‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondActiveCount
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentCompleteCommon
open CenteredMomentRankinRadical
local notation "O" => ActualEisensteinCubic.O

def commonShell (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) : Finset (Ideal O×Ideal O) :=
  (commonLabels (supportedColumns (activeSource S β)) (supportedColumns (activeSource S β))).filter
    (fun p=>(Ideal.absNorm (commonRadical p.1 p.2):ℝ)≤Y)

def partitionLabels (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) :
    Finset ((Ideal O×Ideal O)×Finset (Ideal O)) :=
  (commonShell S β Y).biUnion (fun p=>(IdealMobiusDivisorSum.primeSupport (commonRadical p.1 p.2)).powerset.image
    (fun U=>(p,U)))

end SevenEighths.CenteredMomentSecondActiveCount

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceState
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyState
open CenteredMomentRadialEligibleEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource
local notation "O"=>HeckeFamily.O

def effectiveRadial (r:Radial):Radial:=
  {r with keep:=fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}

def effectiveState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):NaturalState Z Bmask bΦ:=
  {s with radial:=effectiveRadial s.radial
          row_ne_zero:=fun z hz=>s.row_ne_zero z hz.1
          nonexceptional:=fun z hz=>s.nonexceptional z hz.1}

def comparisonFirst (Z M:ℝ):ℝ:=Z^(M/4)
def comparisonSecond (Z M X₁ X₂:ℝ):ℝ:=X₁*X₂/comparisonFirst Z M

lemma comparison_positive (Z M X₁ X₂:ℝ)(hZ:0<Z)(hX₁:0<X₁)(hX₂:0<X₂):
    0<comparisonFirst Z M ∧ 0<comparisonSecond Z M X₁ X₂:=
  ⟨Real.rpow_pos_of_pos hZ _,div_pos (mul_pos hX₁ hX₂) (Real.rpow_pos_of_pos hZ _)⟩

lemma comparison_same_product (Z M X₁ X₂:ℝ)(hZ:0<Z):
    comparisonFirst Z M*comparisonSecond Z M X₁ X₂=X₁*X₂:=by
  unfold comparisonSecond
  exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos hZ (M/4)).ne'

end SevenEighths.CenteredMomentEnergyReferenceState

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst
open CenteredMomentSecondLocalization
open CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

theorem commonLabels_supported (S : Finset (Ideal O)) (C D : Ideal O)
    (h : (C,D)∈commonLabels (supportedColumns S) (supportedColumns S)) :
    Supported C ∧ Supported D := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
  rcases Prod.mk.inj he with ⟨rfl,rfl⟩
  have hp' := Finset.mem_product.mp hp
  exact ⟨commonPart_supported _ _ (Finset.mem_filter.mp hp'.1).2,
    commonPart_supported _ _ (Finset.mem_filter.mp hp'.2).2⟩

end SevenEighths.CenteredMomentSecondRetainedAggregate

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalSourceShell
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalAllocationShell
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

def profileMass {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Tests)(J:ℕ):ℝ:=
  p.heightWeight s.t^J*q.heightWeight v.t^J*slotControl s*slotControl v*
    Real.sqrt (volume s)*Real.sqrt (volume v)

end SevenEighths.CenteredMomentExceptionalSourceShell

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReflectionSupport
open HeckeFamily Filter CenteredMomentNaturalPrimitive EisensteinSchwartzPoisson
open CenteredMomentReflectionMass CenteredMomentNaturalRowSource
open CenteredMomentReflectionDeletion CenteredMomentReflectionWeightedEnergy
open CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentUniformReflectionApproximation
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
local notation "O" => HeckeFamily.O

def naturalDualScale (χ ψ : Character) (X : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) : ℝ :=
  (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)

end SevenEighths.CenteredMomentEnergyZeroReflectionSupport

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthOriginal
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O

def swapProfiles {a b:ℝ}(p:Profiles a b):Profiles a b where
  profile := ![p.profile 1,p.profile 0]
  support := by
    intro i
    fin_cases i
    · simpa using p.support 1
    · simpa using p.support 0

end SevenEighths.CenteredMomentEnergyZeroGrowthOriginal

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplifiedChildWidth
open ActualEisensteinCubic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CenteredMomentSecondRadicalBudget
open CenteredMomentSecondCanonical CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

theorem span_pos (m:O)(hm:m≠0) : 0<((Ideal.span {m}).absNorm:ℝ) :=
  norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr hm)

def presentationFactor : ℝ :=
  ((Ideal.span {(72:O)}).absNorm:ℝ)*(fixedFactor:ℝ)

theorem presentationFactor_pos : 0<presentationFactor :=
  mul_pos (span_pos 72 (by norm_num)) (by exact_mod_cast fixedFactor_pos)

theorem exists_fixed_width_threshold (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→∀ξ:ℝ,ξ≤σ/4→
      Real.logb Z ((Ideal.span {fixedBadMask}).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)<σ/2 := by
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  let C:ℝ:=((Ideal.span {fixedBadMask}).absNorm:ℝ)*(16*b*Csec*(fixedFactor:ℝ)*presentationFactor)
  have hCp:0<C:=mul_pos (span_pos fixedBadMask fixedBadMask_ne_zero)
    (mul_pos (by positivity : (0:ℝ)<16*b*Csec*fixedFactor) presentationFactor_pos)
  have he:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<σ/4 by linarith))) C
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.1 (he.and (Filter.eventually_gt_atTop (1:ℝ)))
  refine ⟨max 2 Z₀,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ ξ hξ
  obtain ⟨hCZ,hZ1⟩:=hZ₀ Z ((le_max_right _ _).trans hZ)
  have hh:Real.logb Z C≤σ/4:=(Real.logb_le_iff_le_rpow hZ1 hCp).mpr hCZ
  dsimp [C] at hh
  rw [Real.logb_mul (span_pos fixedBadMask fixedBadMask_ne_zero).ne'
    (mul_pos (by positivity : (0:ℝ)<16*b*Csec*fixedFactor) presentationFactor_pos).ne'] at hh
  linarith

def fixedWidthThreshold (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) : ℝ :=
  (exists_fixed_width_threshold b Csec σ hb hCs hσ).choose

end SevenEighths.CenteredMomentAmplifiedChildWidth

end

end OAI
end

section

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell
open CenteredMomentExceptionalMaskedSource UniqueFactorizationMonoid CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

def profileMass {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Profiles lo hi)(J:ℕ):ℝ:=
  p.control R*q.control R*(1+‖s.t‖)^J*(1+‖v.t‖)^J*slotControl s*slotControl v*
    Real.sqrt (volume s)*Real.sqrt (volume v)

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstExceptionalPaidScales
open CanonicalQuadraticSieve CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentSectorLocalization
open CenteredMomentDescentLedger
local notation "O"=>ActualEisensteinCubic.O

structure Branch (Z:ℝ) where
  I:Ideal O
  J:Ideal O
  E:Ideal O
  hI:Supported I
  hJ:Supported J
  hE:E≠0
  H:ℝ
  X:ℝ
  Tsec:ℝ
  Csec:ℝ
  ξ:ℝ
  q:ℝ
  w:ℝ
  wo:ℝ
  ell:ℝ
  σ:ℝ
  kind:ℝ
  hH:0<H
  hX:0<X
  hCsec:1≤Csec
  hξ:0≤ξ
  hsec:Tsec≤Csec*firstNominalScale I J E H X
  n:ℤ
  hn:Retained (frequencyRadius Tsec Z ξ) n
  hq:0≤q
  hw:0≤w
  hwo:0≤wo
  hell:0≤ell
  hσ:0≤σ
  hkind:kind≤2
  hwσ:w≤7*σ/3

end SevenEighths.CenteredMomentFirstExceptionalPaidScales

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstInactiveRadicalMass
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockRadicalHarmonicMass
open CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentCommonRadialData CenteredMomentRankinRadical
open CenteredMomentSupportedCorrelation
open ConcretePrimeRowBridge
local notation "O"=>ActualEisensteinCubic.O

def inactiveWeight (C D:Ideal O)(E:Finset (CommonIndex C D))(a:ℝ):ℝ:=
  ‖(UniqueFactorizationMonoid.moebius (∏P∈E,P.val):ℂ)‖/
    ((Ideal.absNorm (∏P∈E,P.val):ℝ)^a)

end SevenEighths.CenteredMomentFirstInactiveRadicalMass

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedAllowance
open CanonicalQuadraticSieve CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical
open CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentFirstExceptionalPaidScales
local notation "O"=>ActualEisensteinCubic.O

def allowance (C D:Ideal O)(Z:ℝ):ℝ:=
  max (3*Real.logb Z (C.absNorm:ℝ)-5*Real.logb Z (D.absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)) 0/6

def extractedAllowance (I J:Ideal O)(Z:ℝ):ℝ:=
  max (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6

end SevenEighths.CenteredMomentFirstMixedAllowance

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedRightTransport
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentFirstPhysicalSource
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstMixedAllowance
open CenteredMomentFirstScale CenteredMomentDescentLedger
local notation "O" => ActualEisensteinCubic.O

def swapIndex (C D : Ideal O) : CommonIndex C D ≃ CommonIndex D C where
  toFun P := ⟨P.val,by rw [commonSupport_comm];exact P.property⟩
  invFun P := ⟨P.val,by rw [commonSupport_comm];exact P.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma swapIndex_val (C D : Ideal O) (P : CommonIndex C D) :
    (swapIndex C D P).val=P.val := rfl

def swapSubset (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    Finset (CommonIndex D C) := E.map (swapIndex C D).toEmbedding

end SevenEighths.CenteredMomentFirstMixedRightTransport

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sourceConductorConstant (S : Finset (Ideal O)) (η : Character) : ℕ :=
  conductorConstant*(∏P∈S,P).absNorm*(η.modulus.absNorm+1)+conductorConstant*M.absNorm

end SevenEighths.ProbeHighRowFamily

end

end OAI
end


