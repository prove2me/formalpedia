-- Prove2me | Definitions.Def_OAIHecke78B019
-- name    : OAIHecke78B019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T01:50:12.038831+00:00
-- url     : https://prove2.me/theorems/9f0991c7-8faf-4117-b86e-f726039392e0
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 20 of 29
-- statement:
--   Definitions bundle 20 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B017` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Descent.SecondAssignedSum`, `Descent.SecondSectorAssembly`, `Descent.SecondModeCanonical`, `Descent.SecondVaryingLists`, `Descent.SecondDeletedAllModes`, `Inversion.FirstPriorityParents`, `Descent.WholePriorityParents`, `Inversion.PrioritySecondSource`, `Descent.WholePriorityPhysical`, `Descent.WholeRetainedSource`, `Inversion.WholePriorityRetainedSource`, `Descent.GlobalPrioritySource`, `Descent.GlobalParentSource`, `Inversion.FirstGlobalParents`, `Inversion.FirstGlobalCaps`, `Descent.FirstDyadicRadius`, `Descent.FirstOriginalProfileLiveSource`, `Descent.FirstOriginalProfileLiveEnergy`, `Descent.GlobalPriorityAggregate`, `Descent.WholePriorityBranches`, `Descent.GlobalPrincipalMass`, `Descent.GlobalPrincipalMassWeighted`, `Descent.GlobalPriorityZero`, `Descent.GlobalPriorityFullAggregate`, `Descent.OriginalCellPriority`, `Descent.FirstDyadicCell`, `Descent.FirstOriginalProfileLivePartition`, `Descent.GlobalRetainedGates`, `Descent.GlobalRetainedGatesRadius`, `Descent.FirstLabelCellStepSource`, `Descent.FirstLabelCellStepPhysicalGates`, `Descent.FirstLabelCellStep`, `Descent.CanonicalLongKeys`, `Detector.GaussianTailBudget`, `PrincipalMellinGrowth`, `Detector.PrincipalContours`, `PrimeRows.MarkedExclusions`, `Detector.PrincipalPhysical`, `Moments.DetectorDictionaryProfiles`, `Moments.DetectorDictionaryUniformTests`, `Dictionary.InverseUniformFamily`, `Dictionary.InverseUniformTests`, `Hecke.DetectorPhysicalSelection`, `Dictionary.InverseUniformSource`, `Inversion.InitialEnergyCallerAssigned`, `Dictionary.InverseClippedUniform`, `Hecke.DetectorSupportedWitness`, `Moments.DivisorRetained`, `Moments.ActiveDivisorShell`, `Moments.CommonMaskExpansion`, `Moments.UniformDivisorShell`, `Moments.EligibleEnergy`, `Moments.InductionEnergy`, `Moments.RadialEligibleEnergy`, `Moments.CoreFloor`, `Moments.ExceptionalAllocationShell`, `Moments.NaturalFixedRaySourceDetectorProfile`, `Moments.OriginalReflectionApproximation`, `Moments.RadialPointwiseUniform`, `Moments.ReflectionWeightedEnergy`, `Moments.RetainedWeightedSource`, `Moments.SecondSourceSeededPowerDescent`, `Moments.UniformReflectionApproximation`, `PrimeRows.SmallPartition`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B019

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Descent.SecondAssignedSum
  Descent.SecondSectorAssembly
  Descent.SecondModeCanonical
  Descent.SecondVaryingLists
  Descent.SecondDeletedAllModes
  Inversion.FirstPriorityParents
  Descent.WholePriorityParents
  Inversion.PrioritySecondSource
  Descent.WholePriorityPhysical
  Descent.WholeRetainedSource
  Inversion.WholePriorityRetainedSource
  Descent.GlobalPrioritySource
  Descent.GlobalParentSource
  Inversion.FirstGlobalParents
  Inversion.FirstGlobalCaps
  Descent.FirstDyadicRadius
  Descent.FirstOriginalProfileLiveSource
  Descent.FirstOriginalProfileLiveEnergy
  Descent.GlobalPriorityAggregate
  Descent.WholePriorityBranches
  Descent.GlobalPrincipalMass
  Descent.GlobalPrincipalMassWeighted
  Descent.GlobalPriorityZero
  Descent.GlobalPriorityFullAggregate
  Descent.OriginalCellPriority
  Descent.FirstDyadicCell
  Descent.FirstOriginalProfileLivePartition
  Descent.GlobalRetainedGates
  Descent.GlobalRetainedGatesRadius
  Descent.FirstLabelCellStepSource
  Descent.FirstLabelCellStepPhysicalGates
  Descent.FirstLabelCellStep
  Descent.CanonicalLongKeys
  Detector.GaussianTailBudget
  PrincipalMellinGrowth
  Detector.PrincipalContours
  PrimeRows.MarkedExclusions
  Detector.PrincipalPhysical
  Moments.DetectorDictionaryProfiles
  Moments.DetectorDictionaryUniformTests
  Dictionary.InverseUniformFamily
  Dictionary.InverseUniformTests
  Hecke.DetectorPhysicalSelection
  Dictionary.InverseUniformSource
  Inversion.InitialEnergyCallerAssigned
  Dictionary.InverseClippedUniform
  Hecke.DetectorSupportedWitness
  Moments.DivisorRetained
  Moments.ActiveDivisorShell
  Moments.CommonMaskExpansion
  Moments.UniformDivisorShell
  Moments.EligibleEnergy
  Moments.InductionEnergy
  Moments.RadialEligibleEnergy
  Moments.CoreFloor
  Moments.ExceptionalAllocationShell
  Moments.NaturalFixedRaySourceDetectorProfile
  Moments.OriginalReflectionApproximation
  Moments.RadialPointwiseUniform
  Moments.ReflectionWeightedEnergy
  Moments.RetainedWeightedSource
  Moments.SecondSourceSeededPowerDescent
  Moments.UniformReflectionApproximation
  PrimeRows.SmallPartition
-/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def eraseSecondSlots {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : MarkedSecondSource ι Jo 0 where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  second := x.second
  quotient := x.quotient
  oldAssigned := x.oldAssigned
  newAssigned := Fin.elim0

omit [DecidableEq ι] in
@[simp] theorem erase_attachSecondSlots {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo 0) (a : Fin Jn → ι) :
    eraseSecondSlots (attachSecondSlots x a) = x := by
  apply MarkedSecondSource.ext <;> try rfl
  funext i
  exact Fin.elim0 i

def assignedSecondCoefficient {Jo : ℕ} (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card)) : ℂ :=
  star (slotAssignmentWeight J₁ a₁
    (fun i hi => x.newAssigned (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩)))) *
    slotAssignmentWeight J₂ a₂
    (fun i hi => x.newAssigned (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩)))

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance instFintypeUnitsO : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def SecondPairCanonicalAt {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) : Prop :=
∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
      (A₁ A₂ : Finset ι), A₁ ⊆ x.cube.support∪x.firstCommon → A₂ ⊆ x.cube.support∪x.firstCommon →
      ∀ (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
      (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (t : JointLogSeparation.Frequency × (Fin 6 → ℝ)),
      let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2
      let data := actualMarkedSecondProfileData p x Ψ m z A₁ A₂
      secondSeparatedPair p hp hcop hg F data slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t =
      secondOuterPhase h (secondRelativeLog (secondActualNorms p data ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
        ∑ J₁ ∈ slots₁.powerset, ∑ J₂ ∈ slots₂.powerset,
          (star (primeMark J₁ lists₁ a₁ ((A₁∪x.second.sourceCommon)∪x.second.overlap)) *
            primeMark J₂ lists₂ a₂ ((A₂∪x.second.sourceCommon)∪x.second.overlap)) *
          star (secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayMinus Ψ z)
            (actualSecondPuncture m) (slots₁\J₁) lists₁ a₁ (fun _ => childLogTest ω₁ (-h 4)) X₀
            (actualSecondChild p u v x)) *
          secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayPlus Ψ z)
            (actualSecondPuncture m) (slots₂\J₂) lists₂ a₂ (fun _ => childLogTest ω₂ (h 5)) X₀
            (actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}})

def secondSourceSector {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (sector : MarkedSecondSource ι Jo Jn → Eisˣ × Eisˣ) (uv : Eisˣ × Eisˣ) :
    Finset (MarkedSecondSource ι Jo Jn) := source.filter (fun x => sector x = uv)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

local instance instFintypeUnitsO_1_rc7b4eb_1 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
def secondInheritedProfile {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) : SecondProfileData ι :=
  actualMarkedSecondProfileData p x Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z ∅ ∅

def secondModeLeft (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : SecondChild → ℂ :=
  secondCanonicalPolynomial p hp hcop hg pool (fun _ => secondRayMinus Ψ z)
    (actualSecondInheritedPuncture m) slots lists a
    (fun _ => childLogTest ω (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4)) X

def secondModeRight (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (X : ℝ) (t : Frequency × (Fin 6 → ℝ)) (c : SecondChild) : ℂ :=
  secondCanonicalPolynomial p hp hcop hg pool (fun _ => secondRayPlus Ψ z)
    (actualSecondInheritedPuncture m) slots lists a
    (fun _ => childLogTest ω ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) X
    (c.1,c.2.1,-c.2.2)

def secondModeOuter {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2)
    (secondRelativeLog (secondActualNorms p (secondInheritedProfile p x Ψ m z) ∅ ∅) G E V B X)

def secondModeBranch {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  secondModeOuter p x Ψ m z G E V B X t *
    (star (primeMark J₁ lists₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
      primeMark J₂ lists₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
    star (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t (actualSecondChild p u v x)) *
    secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t (actualSecondChild p u v x)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open InverseSecondFibers
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def varyingAssignedGate {Jo : ℕ} (J₁ J₂ : Finset σ)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card)) : Prop :=
  (∀ i hi,x.newAssigned (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))∈L₁ (eraseSecondSlots x) i) ∧
  (∀ i hi,x.newAssigned (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))∈L₂ (eraseSecondSlots x) i)

def varyingAssignedSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι) :=
  (assignedSecondSource source J₁ J₂ base₁ base₂).filter (varyingAssignedGate J₁ J₂ L₁ L₂)

variable (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedAllModesUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondDeletedFullModeSum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  ∑ uv : Eisˣ × Eisˣ,∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
    ∑ x∈secondSourceSector source sector uv,
      actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
        secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
          ω₁ ω₂ G E V B X t

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseFirstPriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic
local notation "O" => ActualEisensteinCubic.O

@[ext] structure Source (ι : Type*) (Jo : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  quotientSupport : Finset ι
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

def extractedSupport (negative : Bool) (x : Source ι Jo) : Finset ι :=
  ((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪x.quotientSupport

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def parent (x : Source ι Jo) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := sourceIdeal p x.quotientSupport
  oldAssigned := x.oldAssigned

def appendParent {Jn : ℕ} (x : SecondParentSource ι Jo)
    (q : Fin Jn→SmoothMobiusCorrection.PrimeIdeal) : SecondParentSource ι (Jo+Jn) where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := Fin.addCases x.oldAssigned q

def forgetAppended {Jn : ℕ} (x : SecondParentSource ι (Jo+Jn)) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := fun i=>x.oldAssigned (Fin.castAdd Jn i)

omit [DecidableEq ι] in
@[simp] theorem forget_append {Jn : ℕ} (x : SecondParentSource ι Jo)
    (q : Fin Jn→SmoothMobiusCorrection.PrimeIdeal) : forgetAppended (appendParent x q)=x := by
  apply SecondParentSource.ext <;> try rfl
  funext i
  simp only [forgetAppended,appendParent,Fin.addCases_left]

def attach (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) : SecondParentSource ι (Jo+(J.card+J.card)) :=
  appendParent (parent p q.1) (fun i=>sourcePrime p (pairedSlotAssignment J J q.2 i))

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem forget_attach (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    forgetAppended (attach p J q)=parent p q.1 := forget_append _ _

def coefficient (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) :
    SecondParentSource ι (Jo+(J.card+J.card))→ℂ :=
  Function.extend (attach p J) (fun q=>w q.1*pairedSlotWeight J J a a q.2) (fun _=>0)

structure SourceValid (x : Source ι Jo) : Prop where
  admissible : x.cube.Admissible
  common_disjoint : Disjoint x.firstCommon x.cube.support
  first_divisor : x.firstDivisor⊆x.firstCommon∪x.cube.support
  old_support : ∀ i,(x.oldAssigned i).val∣
    sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*sourceIdeal p x.quotientSupport

def fixedPoint (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (D : Finset ι) : Source ι Jo :=
  ⟨b,C,E,D,old⟩

variable (hp : ∀ i,p i≠0) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def priorityOuter (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter)
    (core : FirstCoreIndex) (D : Finset ι) : ℝ :=
  (‖RayFourExpansion.crossCoeff r.1 r.2‖*‖selector D‖) *
    ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit negative Ψ m D core‖

end SevenEighths.InverseFirstPriorityParents

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentWholePriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

def wholeExtractedSupport (extra : Source ι Jo→Finset ι)
    (negative : Bool) (x : Source ι Jo) : Finset ι := extra x∪extractedSupport negative x

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def wholeAssignmentSource (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) :
    Finset (Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :=
  (source ×ˢ ((J.pi lists)×ˢ(J.pi lists))).filter
    (fun q=>∀ i,pairedSlotAssignment J J q.2 i∈wholeExtractedSupport extra negative q.1)

def wholeAssignedParents (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) : Finset (SecondParentSource ι (Jo+(J.card+J.card))) :=
  (wholeAssignmentSource extra source negative J lists).image (attach p J)

end SevenEighths.InverseMomentWholePriorityParents

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InversePrioritySecondSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def quotientSupport (y : SecondParentSource ι Jo) : Finset ι :=
  Function.extend (sourceIdeal p) id (fun _=>∅) y.quotient

def residualLists (negative : Bool) (lists : σ→Finset ι)
    (y : SecondParentSource ι Jo) (i : σ) : Finset ι :=
  lists i \ (((if negative then y.cube.rightDivisor else y.cube.leftDivisor)∪y.firstCommon)∪
    quotientSupport p y)

def retainedPool (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) : Finset (MarkedSecondSource ι Jo 0) :=
  attachedSecondFamily parents (fun y=>secondDyadicSector pool (secondVariableCutoff p y (R y))
    residual (label y) j)

variable (hp : ∀ i,p i≠0)
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def parentPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (y : SecondParentSource ι Jo) : ℂ :=
  firstFreshSecondPoisson p hp hg hinj pool (quotientSupport p y) y.cube.support
    (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (primeMark (slots\J) (residualLists p negative lists y) a) ω X
    (∏ i∈y.firstCommon,p i) (secondParentDivisor p y) core t Y

def retainedRow (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ) (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0) : ℂ :=
  actualSecondSignedWeight p hp hcop hg Ψ
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
    actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
      (slots\J) (slots\J) (residualLists p negative lists (secondParentOf x))
      (residualLists p negative lists (secondParentOf x)) a a V V rowMajorant Y X

end SevenEighths.InversePrioritySecondSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentWholePriorityPhysical
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InverseMomentWholePriorityParents InversePrioritySecondSource
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ] [Fintype κ]
variable {Jo : ℕ} (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def fullPhysical (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ)
    (y : SecondParentSource ι Jo) : ℂ :=
  let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
  let ll := fun i=>lists i\extra y.cube
  let H := markedRadial p (slots\J) (residualLists p negative ll y) a ∅ V X
  let K := secondVariableCutoff p y R
  truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K +
    (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ₀ m slots J ll a V X Y ray x) +
    secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K

end SevenEighths.InverseMomentWholePriorityPhysical

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMomentWholeRetainedSource
open ActualEisensteinCubic SecondPassArithmetic InverseMoment InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentWholePriorityParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def deleted (extra : CubeCoordinates ι→Finset ι) (negative : Bool)
    (x : MarkedSecondSource ι Jo 0) : Finset ι :=
  extra x.cube∪(((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪
    quotientSupport p (secondParentOf x))

end SevenEighths.InverseMomentWholeRetainedSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityRetainedSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents InversePrioritySecondSource
open InverseMomentWholePriorityParents InverseMomentWholePriorityPhysical
open InverseWholePriorityValidSource RayFourExpansion InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def unifiedSource (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ) :
    Finset (MarkedSecondSource ι Jo 0) :=
  attachedSecondFamily parents (fun y=>secondExpansionPool pool
    (fun G E=>(secondVariableCutoff p y (R y) G E).erase 0))

def wholeRow (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ) (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0) : ℂ :=
  retainedRow p hp hcop hg pool negative Ψ m slots J (fun i=>lists i\extra x.cube) a V X Y ray x

def coefficientBound : ℝ := 512*(32*512)

variable (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseWholePriorityRetainedSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityRetainedSource
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def globalPriorityOuter (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)(x:Source ι Jo):ℂ:=
  w x*(priorityOuter p hg x.cube negative Ψ m (fun _=>1) ray core x.quotientSupport:ℂ)

def globalPriorityWeight (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)
    (J:Finset σ)(a:σ→ι→ℂ)(x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0):ℂ:=
  coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) (secondParentOf x)

def normalizedGlobalPriorityWeight (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)
    (J:Finset σ)(a:σ→ι→ℂ)(x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0):ℂ:=
  globalPriorityWeight p hg negative Ψ m ray core w J a x/(coefficientBound:ℂ)

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open InverseFirstPriorityParents
variable {ι:Type*} [DecidableEq ι] {Jo:ℕ}
def eraseFirstQuotient (x:Source ι Jo):Source ι Jo:= {x with quotientSupport:=∅}
def fillFirstQuotient (x:Source ι Jo)(D:Finset ι):Source ι Jo:={x with quotientSupport:=D}
omit [DecidableEq ι] in
@[simp] theorem erase_fillFirstQuotient (x:Source ι Jo)(D:Finset ι):
    eraseFirstQuotient (fillFirstQuotient x D)=eraseFirstQuotient x:=rfl
omit [DecidableEq ι] in
@[simp] theorem eraseFirstQuotient_eq (x:Source ι Jo)(hx:x.quotientSupport=∅):
    eraseFirstQuotient x=x:=by cases x;simpa [eraseFirstQuotient] using hx.symm

def globalParentSource (outer:Finset (Source ι Jo))(pool:Finset ι)
    (selector:Source ι Jo→Finset ι→ℂ):Finset (Source ι Jo):=
  outer.biUnion (fun x=>(pool.powerset.filter (fun D=>selector x D≠0)).image (fillFirstQuotient x))

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseFirstGlobalParents
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open FirstCauchyArithmetic RayFourExpansion InverseMoment
open InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InversePrioritySecondSource
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def ofOriginal (k : FirstOriginalOuter ι) : Source ι 0 where
  cube := k.1
  firstCommon := k.2.1
  firstDivisor := k.2.2
  quotientSupport := ∅
  oldAssigned := Fin.elim0

def toOriginal (x : Source ι 0) : FirstOriginalOuter ι :=
  ⟨x.cube,⟨x.firstCommon,x.firstDivisor⟩⟩

omit [DecidableEq ι] in
@[simp] theorem toOriginal_ofOriginal (k : FirstOriginalOuter ι) :
    toOriginal (ofOriginal k)=k := by cases k with | mk b k => cases k; rfl

omit [DecidableEq ι] in
@[simp] theorem toOriginal_fill (x : Source ι 0) (D : Finset ι) :
    toOriginal (fillFirstQuotient x D)=toOriginal x := rfl

def originalOuterSource (pool : Finset ι) (Q : Finset (ι→₀ℕ)) : Finset (Source ι 0) :=
  (firstOriginalOuter pool Q).image ofOriginal

def originalSelector (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (x : Source ι 0) (D : Finset ι) : ℂ := selector (toOriginal x) D

omit [DecidableEq ι] in
@[simp] theorem originalSelector_ofOriginal (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (k : FirstOriginalOuter ι) (D : Finset ι) :
    originalSelector selector (ofOriginal k) D=selector k D := by
  simp only [originalSelector,toOriginal_ofOriginal]

omit [DecidableEq ι] in
@[simp] theorem originalSelector_ofOriginal_fun (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (k : FirstOriginalOuter ι) : originalSelector selector (ofOriginal k)=selector k :=
  funext (originalSelector_ofOriginal selector k)

def originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) : Finset (Source ι 0) :=
  globalParentSource (originalOuterSource pool Q) pool (originalSelector selector)

variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseFirstGlobalParents

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseFirstGlobalCaps
open InverseMoment InverseFirstGlobalParents InverseFirstPriorityParents
open InverseMomentWholePriorityParents InverseMomentFirstChildWindows
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic
open InverseSecondSourceBlocks (dyadIndex dyadScale )
open ConcreteTraceCRT (eisEmbedding)
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def outerNorms (p : ι→O) (x : FirstOriginalOuter ι) : Fin 5→ℝ :=
  ![‖eisEmbedding (aLabel p x.1.support x.1.rightBit)‖^2,
    ‖eisEmbedding (aLabel p x.1.support x.1.leftBit)‖^2,
    primeProductNorm p x.2.1,
    ‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.2.2)‖^2,
    primeProductNorm p (cubeActiveSupport x.1.support
      (fun i=>x.1.leftExponent i+x.1.rightExponent i) x.1.leftBit x.1.rightBit)]

def outerGate (p : ι→O) (k : SourceIndex) (x : FirstOriginalOuter ι) : Prop :=
  ∀i : Fin 5,dyadIndex (outerNorms p x i)=k i.castSucc

def outerCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :=
  (firstOriginalOuter pool Q).filter (outerGate p k)

def parentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ) :=
  (originalParentSource pool Q (fun x=>commonSelector p (selector x) l)).filter
    (fun x=>outerGate p k (toOriginal x))

def originalNorms (p : ι→O) (x : Σ _ : FirstOriginalOuter ι,Ideal O×O) : Fin 6→ℝ :=
  sourceNorms (fun y=>outerNorms p y.1 0) (fun y=>outerNorms p y.1 1)
    (fun y=>outerNorms p y.1 2) (fun y=>outerNorms p y.1 4)
    (fun y=>primeSubsetGenerator (fun i=>Ideal.span {p i}) y.1.2.2)
    (fun y=>y.2.2) x

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

def dyadicExponent (Z : ℝ) (n : ℕ) : ℝ := Real.logb Z (dyadScale n)

def jNorm (p : ι→O) (x : FirstOriginalOuter ι) : ℝ :=
  ‖eisEmbedding (jLabel p x.1.support (fun i=>x.1.leftExponent i+x.1.rightExponent i)
    x.1.leftBit x.1.rightBit)‖^2

def labelParentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l j : ℕ) :=
  (parentCell p pool Q selector k l).filter (fun x=>dyadIndex (jNorm p (toOriginal x))=j)

end SevenEighths.InverseFirstGlobalCaps

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseFirstGlobalCaps
open InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]

def firstDyadicExponent (Z x:ℝ):ℝ:=dyadicExponent Z (dyadIndex x)

def firstDyadicRadius (p:ι→O)(b:CubeCoordinates ι)(C D:Finset ι)
    (Z M r ell V eta tau:ℝ):ℝ:=
  Z^(firstPhysicalHeight M r ell V (firstDyadicExponent Z (primeProductNorm p D))
    (firstDyadicExponent Z (primeProductNorm p C))
    (firstDyadicExponent Z (‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))+12*eta+tau)

def firstDyadicPhysicalCutoff (p:ι→O)(b:CubeCoordinates ι)(C:Finset ι)(I:Ideal O)
    (Z M r ell V eta tau:ℝ)(D:Finset ι):Finset O:=
  childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit I)
    (firstDyadicRadius p b C D Z M r ell V eta tau)

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def refinedOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex)
    (gate : FirstOriginalOuter ι→Prop) : Finset (FirstOriginalOuter ι) :=
  (originalOuterCell p pool Q k).filter gate

def refinedSource (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Y : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop) : Finset (OriginalIndex ι) :=
  (sourceCell (originalNorms p)
    (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k).filter
      (fun x=>gate x.1 ∧ firstOriginalWeight p β cutoff x.1 x.2≠0)

def labelGate (j : ℕ) (x : FirstOriginalOuter ι) : Prop :=
  InverseSecondSourceBlocks.dyadIndex (InverseFirstGlobalCaps.jNorm p x)=j

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def refinedChildEnergy (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l : ℕ)
    (gate : FirstOriginalOuter ι→Prop) (negative : Bool) (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (omega : ℝ→ℂ) (T t Y : ℝ) : ℝ :=
  ∑x∈refinedOuter p pool Q k gate,
    firstCanonicalSecondEnergy p hp hg hinj pool x.1 x.2.1 negative Ψ m (divisorElement p x)
      (mark (if negative then x.1.rightExponent else x.1.leftExponent))
      (commonSelector p (fun _=>1) l) omega T t Y

def refinedCellRows (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (k : SourceIndex) (l : ℕ) (gate : FirstOriginalOuter ι→Prop) (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ) (s : Fin 9→ℝ) : ℂ :=
  firstFamilyPhysicalRows p hg
    (refinedSource p pool Q labels β cutoff Y k gate)
    pool (fun _=>commonSelector p (fun _=>1) l)
    (coefficient p hp hcop hg Ψ m mark true) (coefficient p hp hcop hg Ψ m mark false)
    (weight p hp hcop hg β cutoff Ψ m) W₁ W₂ Φ
    (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p) K
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) s

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
def globalPriorityRetainedAggregate
    (p:ι→Eis)[∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hp:∀i,p i≠0)(hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    {Jo:ℕ}(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))(w:InverseFirstPriorityParents.Source ι Jo→ℂ)
    (negative:Bool)(Ψ:Eis→*ℂ)(m:Eis)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z*
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) (fun _=>R),
        globalPriorityWeight p hg negative Ψ m ray core w J a x*
        wholeRow p hp hcop hg extra pool negative (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a V X Y z x‖

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def priorityZeroParent (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis) (slots assigned:Finset σ)
    (lists:σ→Finset ι) (a:σ→ι→ℂ) (V:𝓢(ℝ,ℂ)) (X Y:ℝ)
    (R:Finset ι→Finset ι→ℝ) (y:SecondParentSource ι Jo):ℂ:=
  truncatedSecondZero p hg pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y)
    (InversePrincipalEnergy.markedRadial p (slots\assigned)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X)
    rowMajorant Y (secondVariableCutoff p y R)

def priorityTailParent (hp:∀i,p i≠0) (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis) (slots assigned:Finset σ)
    (lists:σ→Finset ι) (a:σ→ι→ℂ) (V:𝓢(ℝ,ℂ)) (X Y:ℝ)
    (R:Finset ι→Finset ι→ℝ) (y:SecondParentSource ι Jo):ℂ:=
  secondSourceTail p hp hg hinj pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y)
    (InversePrincipalEnergy.markedRadial p (slots\assigned)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X)
    rowMajorant Y (secondVariableCutoff p y R)

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

abbrev Core (ι : Type*) := CubeCoordinates ι×Finset ι×Finset ι

def core {ι : Type*} {Jo : ℕ} (x : Source ι Jo) : Core ι :=
  (x.cube,x.firstCommon,x.quotientSupport)

def divisorTarget {ι : Type*} [DecidableEq ι] (p : ι→O) (q : Core ι) : Ideal O :=
  sourceIdeal p q.1.support*sourceIdeal p q.2.1*sourceIdeal p q.2.2

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def principalSupport {ι : Type*} [DecidableEq ι] {Jo : ℕ}
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool) (x : Source ι Jo) : Finset ι :=
  (extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪x.quotientSupport

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion FirstCauchyArithmetic
open InverseSecondPrincipalCaller InversePrioritySecondSource InverseFirstPriorityParents InverseMomentWholePriorityParents
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
def globalPriorityZeroAggregate
    (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal](hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityZeroParent p hg extra pool negative
        (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots J lists a V X Y R (parent p x)‖

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion FirstCauchyArithmetic
open InverseSecondPrincipalCaller InversePrioritySecondSource InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal](hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
def globalPriorityOriginalEnergy (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
        a om X t Y ray core (parent p x)).re

def globalPriorityTailAggregate (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) original negative J lists,
      coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
      priorityTailParent p hg hp hinj extra pool negative
        (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
        m slots J lists a V X Y R y‖

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic
open InverseFirstPriorityParents InverseFirstGlobalParents
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]

def originalSubsetSource (outer:Finset (FirstOriginalOuter ι)):Finset (Source ι 0):=
  outer.image ofOriginal

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
variable (p:ι→O)

def firstCellRadius (Z M r ell V eta tau:ℝ)(k:SourceIndex)(j:ℕ):ℝ:=
  Z^(firstPhysicalHeight M r ell V (dyadicExponent Z (k 3))
    (dyadicExponent Z (k 2)) (dyadicExponent Z j)+12*eta+tau)

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

abbrev JointKey := SourceIndex × ℕ × ℕ

def jointKey (x : OriginalIndex ι) (j : FirstCommonIndex ι) : JointKey :=
  (sourceIndex (originalNorms p) x,dyadIndex (primeProductNorm p j.2.1),
    dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))

def liveJointKeys (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) : Finset JointKey :=
  ((S×ˢfirstCommonIndices pool).filter (fun x=>term x.1 x.2≠0)).image
    (fun x=>jointKey p x.1 x.2)

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def retainedSource (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) : Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0) :=
  unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) (fun _=>cutoff)

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open InverseSecondUniformCutoff
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def supportedRetainedSource (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) : Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0) :=
  geometrySource p (retainedSource p extra original negative J lists pool cutoff) b X

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondUniformCutoff
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

abbrev exponent := InverseFirstGlobalCaps.dyadicExponent

def columnA (Z : ℝ) (k : SourceIndex) (negative : Bool) : ℝ :=
  exponent Z (k (if negative then 0 else 1))

def columnScale (Z r : ℝ) (k : SourceIndex) (l : ℕ) (negative : Bool) : ℝ :=
  Z^(r-columnA Z k negative-exponent Z (k 2)-exponent Z l)

def secondCutoff (p : ι→O) (Z M r ell V eta tau window : ℝ) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (G E : Finset ι) : ℝ :=
  uniformSecondRadius p Z (exponent Z (k 3)) eta G E
    (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j) (Z^tau)

def source (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :=
  supportedRetainedSource p (extra negative)
    (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
    negative J lists pool (secondCutoff p Z M r ell V eta tau window k l j negative)
    b (columnScale Z r k l negative)

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondUniformCutoff InversePrioritySecondSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0)

def parentWeight (l : ℕ) (x : Source ι 0) : ℂ :=
  (‖commonSelector p (fun _=>1) l x.quotientSupport‖:ℂ)

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondFibers InverseInitialClippedColumns RayFourExpansion FirstCauchyArithmetic
open InverseWholePriorityRetainedSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def ChildBounds {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (Z M r ell V eta tau window b epschild A : ℝ) (K degree : ℕ) : Prop :=
  ∀(ray : RayCharacter×RayCharacter)(core : FirstCoreIndex)(assigned : Finset σ),assigned⊆slots→
  let S := source p pool Q k l j negative assigned lists Z M r ell V eta tau window b
  let Ψ₀ := firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  (∀z : SecondRayIndex,∀d∈keys p S,∀s : ℝ,∀J₁∈(slots\assigned).powerset,∀γ∈actualSecondTriples p 1 1 (cell p S d),
    normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
      (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
      ((actualCellLabels p S d).filter Squarefree)
      (nonzeroChildFrequencyBall 1 (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d))
      (secondLabelWeight K) (childLogTest ω₁ s)
      (Z^(max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))) Z
      (actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d)≤
      A*Z^(actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d+epschild)*
        (1+‖s‖)^(2*degree)) ∧
  (∀z : SecondRayIndex,∀d∈keys p S,∀s : ℝ,∀J₂∈(slots\assigned).powerset,∀γ∈actualSecondTriples p 1 1 (cell p S d),
    normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
      (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
      ((actualCellLabels p S d).filter Squarefree)
      (nonzeroChildFrequencyBall 1 (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d))
      (secondLabelWeight K) (childLogTest ω₂ s)
      (Z^(max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))) Z
      (actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d)≤
      A*Z^(actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d+epschild)*
        (1+‖s‖)^(2*degree))

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks
open InverseMomentFirstOriginalProfile CompletedHeight
local notation "O"=>ActualEisensteinCubic.O

def actualLongSourceKeys {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Ψ:O→*ℂ)(m mCoef:O)
    (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)(om:ℝ→ℂ)
    (Z M r ell V H₀ ξ Lcap eta tau:ℝ) :=
  let mark:=fun v U=>primeMark slots lists weights (v.support∪U)
  let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>
    firstDyadicRadius p q C D Z M r ell V eta tau
  let W:=fun y=>normTwistedSource om ξ (y/Z^r)
  let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels)
    (fun x=>x.1) (Z^(2*Lcap+15*eta+tau))
  liveJointKeys p source pool (sourceSummand p hp hcop hg
    (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) cutoff Ψ m mark W rowMajorant (Z^M))

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical

def gaussianWeightedMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k R : ℝ) : ℝ := R^k*gaussianJointMoment V hV J R

def gaussianRemoteMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (s Z A : ℝ) (j : ℕ) : ℝ :=
  if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
    ((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)
  else 0

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Complex Set
namespace SevenEighths.PrincipalMellinGrowth
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary

def principalConstant (M : Ideal HeckeFamily.O) : ℝ :=
  (1+HeckeLogarithmicInput.uniformConstant)*(M.absNorm : ℝ)^(3/5 : ℝ)*
    HeckeDeletionBounds.localBound (19/20)^(IdealMobiusDivisorSum.primeSupport M).card

def wAmplitude (M : Ideal HeckeFamily.O) (cw : ℝ) : ℝ := 9*(cw+2)*principalConstant M

end SevenEighths.PrincipalMellinGrowth

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalContours
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

local instance instCountableO_rc7b4eb_1 : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_rc7b4eb_1 : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable
@[fun_prop] lemma measurable_const_cpow {α : Type*} [MeasurableSpace α] (Q : ℝ) (hQ : 0<Q)
    (f : α → ℂ) (hf : Measurable f) : Measurable (fun x => (Q:ℂ)^f x) := by
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact ((differentiable_id.const_cpow (Or.inl hn)).continuous.measurable).comp hf

def zBoxAmplitude (M : Id) (Bz : ℝ) : ℝ :=
  36*max 6 (6*Bz+1)*principalConstant M

def arithmeticMultiplier {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (X Y Z : ℝ) (s w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*(Y:ℂ)^(w-1)*
    HeckeReciprocal.reciprocal (η.excludePrimes S hS) s *
    (globalClosedCorrection η S s w z*slotMultiplier η J T b s w z)*
    LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w

def boxScale (X Y Z a Bs Bz cw : ℝ) : ℝ :=
  scaleBound X (1/2-Bz) (1/2-33/200) * scaleBound Z (a+33/200-1) (Bs+Bz-1) *
    scaleBound Y (19/20-1) (cw-1)

def arithmeticAmplitude {ι : Type*} (S : Finset Id) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (X Y Z a Bs Bz cw C δw δz : ℝ) : ℝ :=
  boxScale X Y Z a Bs Bz cw * C * ((3/2)*slotBound J T b Bs Bz) *
    (zBoxAmplitude (∏P∈S,P) Bz/δz) * (wAmplitude (∏P∈S,P) cw/δw)

def residueArithmetic {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (X Z : ℝ) (s z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*HeckeReciprocal.reciprocal (η.excludePrimes S hS) s *
    (globalClosedCorrection η S s 1 z*slotMultiplier η J T b s 1 z)*
    LFunction (fixedSourcePrincipal S hS) (6*z)

def residueAmplitude {ι : Type*} (S : Finset Id) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ) (X Z a ξ C : ℝ) : ℝ :=
  X^(1/2-ξ)*Z^(a+ξ-1)*C*((3/2)*slotBound J T b a ξ)*
    (zBoxAmplitude (∏P∈S,P) ξ/|6*ξ-1|)

end SevenEighths.ProbePrincipalContours
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

theorem correctionTail_mono {S T : Finset (Ideal O)} (hS : CorrectionTail S) (hst : S⊆T) :
    CorrectionTail T := by
  let inc : {P : PrimeIdeal // P.val∉T}→{P : PrimeIdeal // P.val∉S} :=
    fun P=>⟨P.val,fun h=>P.property (hst h)⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun R : {P : PrimeIdeal // P.val∉S}=>R.val) h)
  constructor
  · intro P hP
    exact hS.norm_four P (fun h=>hP (hst h))
  · apply le_trans _ hS.small
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _=>globalPrimeDefectBound_nonneg P.val)
      (fun _=>le_rfl) (globalPrimeDefectBound_summable.subtype _) hS.summable

theorem markedSourceExclusions (S : Finset (Ideal O)) (hS : SourceExclusions S) (T : Finset PrimeIdeal) :
    SourceExclusions (markExclusions S T) := {
  prime := markExclusions_prime S hS.prime T
  bad := hS.bad.trans Finset.subset_union_left
  tail := correctionTail_mono hS.tail Finset.subset_union_left }

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace SevenEighths.ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds CanonicalQuadraticSieve
open PrincipalMellinResidues ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal HeckeFamily.O

def principalPoolKernel {K : ℕ} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset PrimeIdeal) (b : Fin K→PrimeIdeal→ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) : ℂ :=
  sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s) w z *
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w

end SevenEighths.ProbePrincipalPhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff ComplexConjugate
namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeInverseAmplification HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

lemma logTest_eq_iterate (W : ℝ→ℂ) (n : ℕ) : logTest W n=(logProfile^[n]) W := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [logTest,Function.iterate_succ_apply',ih]

theorem detector_profile_support (reverse : Bool) (n : ℕ) (σ t : ℝ) :
    Function.support (twistProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) σ t)
      ⊆Set.Icc (1/4) (9/4) := by
  apply (oriented_twist_support reverse _ σ t).trans
  rw [←logTest_eq_iterate]
  exact (logTest_support positiveAnnular n).trans positiveAnnular_support

theorem detector_profile_smooth (reverse : Bool) (n : ℕ) (σ t : ℝ) :
    ContDiff ℝ ∞ (twistProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) σ t) := by
  apply twistProfile_smooth _ σ t (1/4) (9/4) (by norm_num)
  · cases reverse <;> simp only [orientedProfile,ite_true]
    · rw [←logTest_eq_iterate]
      exact (logTest_support positiveAnnular n).trans positiveAnnular_support
    · rw [conjugate_profile_support,←logTest_eq_iterate]
      exact (logTest_support positiveAnnular n).trans positiveAnnular_support
  · have hw := logTest_smooth positiveAnnular n (1/4) (9/4) (by norm_num)
      positiveAnnular_support positiveAnnular_smooth
    rw [logTest_eq_iterate] at hw
    cases reverse
    · exact hw
    · exact conjugate_profile_smooth _ hw

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

lemma twistProfile_zero (W : ℝ→ℂ) : twistProfile W 0 0=W := by
  funext x
  simp [twistProfile,HeckeDyadic.shift]

lemma oriented_detector_log_support (reverse : Bool) (n : ℕ) :
    Function.support (orientedProfile reverse ((logProfile^[n]) positiveAnnular))⊆Icc (1/4) (9/4) := by
  simpa only [twistProfile_zero] using detector_profile_support reverse n 0 0

lemma oriented_detector_log_smooth (reverse : Bool) (n : ℕ) :
    ContDiff ℝ ∞ (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) := by
  simpa only [twistProfile_zero] using detector_profile_smooth reverse n 0 0

def detectorSchwartz (reverse : Bool) (n : ℕ) (σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  interpolatedProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) (1/4) (9/4)
    (by norm_num) (oriented_detector_log_support reverse n) (oriented_detector_log_smooth reverse n) σ
      (orientedFrequency reverse t)

lemma detectorSchwartz_apply (reverse : Bool) (n : ℕ) (σ t x : ℝ) :
    detectorSchwartz reverse n σ t x=
      twistProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) σ (orientedFrequency reverse t) x :=
  interpolatedProfile_apply _ _ _ _ _ _ _ _ _

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic JointLogSeparation CenteredMomentDetectorDictionary

def inverseLogSchwartz (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (p : ℝ×ℝ) : 𝓢(ℝ,ℂ) :=
  realInterpolatedLogSchwartz (baseProfile reverse n V W p.2) a b ha
    ((baseProfile_support reverse n V W p.2).trans hs)
    (baseProfile_smooth reverse n V W p.2 a b ha hV hW hs) p

def inverseSchwartz (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  interpolatedProfile (baseProfile reverse n V W R) a b ha
    ((baseProfile_support reverse n V W R).trans hs)
    (baseProfile_smooth reverse n V W R a b ha hV hW hs) σ t

lemma inverseSchwartz_apply (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (R σ t x : ℝ) :
    inverseSchwartz reverse n V W a b ha hV hW hs R σ t x=
      twistProfile (baseProfile reverse n V W R) σ t x :=
  interpolatedProfile_apply _ _ _ _ _ _ _ _ _

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles

def sourceOperator (scaled : Bool) : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ) :=
  if scaled then scaleCLM else ContinuousLinearMap.id ℝ _

def inverseDetectorSchwartz (reverse : Bool) (n : ℕ) (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  inverseSchwartz reverse n cutoff positiveAnnular (1/4) (9/4) (by norm_num)
    (cutoff.smooth ⊤) positiveAnnular_smooth positiveAnnular_support R σ t

lemma inverseDetectorSchwartz_apply (reverse : Bool) (n : ℕ) (R σ t x : ℝ) :
    inverseDetectorSchwartz reverse n R σ t x=
      twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t x :=
  inverseSchwartz_apply _ _ _ _ _ _ _ _ _ _ _ _ _ _

def inverseDetectorTest (scaled reverse : Bool) (n : ℕ) (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  sourceOperator scaled (inverseDetectorSchwartz reverse n R σ t)

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorPhysicalSelection
open HeckeFamily HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

def physical {Row Slot : Type*} (row : Row→O) (W : Slot→ℝ→ℂ)
    (b w : Slot→ℝ) (z : Slot→ℂ) (U : ℝ) (u : Row) (s : Slot) : ℂ :=
  HeckePrimeRow.canonicalPrimeAmplitude M H (row u) (W s) (b s) (U^(w s)) (z s)

def weightedMean {Slot : Type*} (slots : Finset Slot) (w g : Slot→ℝ) : ℝ :=
  (∑ s∈slots,w s*g s)/(∑ s∈slots,w s)

end SevenEighths.HeckeDetectorPhysicalSelection

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial

def inverseSourceSchwartz (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  inverseDetectorTest scaled reverse n (U^r/U^tstar) σ t

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
namespace SevenEighths.InverseInitialEnergyCallerAssigned
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def attach {J : ℕ} (x : Source (ι:=ι) 0) (q : Fin J→ι) : Source (ι:=ι) J where
  common := x.common
  divisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency
  assigned := q

def erase {J : ℕ} (x : Source (ι:=ι) J) : Source (ι:=ι) 0 where
  common := x.common
  divisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency
  assigned := Fin.elim0

omit [DecidableEq ι] in
@[simp] theorem erase_attach {J : ℕ} (x : Source (ι:=ι) 0) (q : Fin J→ι) :
    erase (attach x q) = x := by
  apply Source.ext <;> try rfl
  funext i
  exact Fin.elim0 i

def attachPair (J₁ J₂ : Finset σ)
    (z : Source (ι:=ι) 0 × ((∀ i∈J₁,ι) × (∀ i∈J₂,ι))) :
    Source (ι:=ι) (J₁.card+J₂.card) :=
  attach z.1 (pairedSlotAssignment J₁ J₂ z.2)

def assignedSource (S : Finset (Source (ι:=ι) 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ→Finset ι) : Finset (Source (ι:=ι) (J₁.card+J₂.card)) :=
  ((S ×ˢ ((J₁.pi L₁) ×ˢ (J₂.pi L₂))).filter
    (fun z=>∀ i,pairedSlotAssignment J₁ J₂ z.2 i∈z.1.common∪z.1.overlap)).image
      (attachPair J₁ J₂)

def coefficient (J₁ J₂ : Finset σ) (a₁ a₂ : σ→ι→ℂ)
    (x : Source (ι:=ι) (J₁.card+J₂.card)) : ℂ :=
  star (slotAssignmentWeight J₁ a₁
    (fun i hi=>x.assigned (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩)))) *
    slotAssignmentWeight J₂ a₂
    (fun i hi=>x.assigned (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩)))

end SevenEighths.InverseInitialEnergyCallerAssigned

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseUniform HeckeInverseAmplification
open InverseMoment InverseInitialClippedColumns InverseInitialOverlapFourier
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem source_support (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) :
    Function.support (inverseSourceSchwartz scaled reverse n U tstar r σ t : ℝ→ℂ) ⊆
      Set.Icc (1/4 : ℝ) (9/4) := by
  let W := inverseDetectorSchwartz reverse n (U^r/U^tstar) σ t
  have hw : Function.support (W : ℝ→ℂ) ⊆ Set.Icc (1/4 : ℝ) (9/4) := by
    have he : (W : ℝ→ℂ) = twistProfile
        (baseProfile reverse n HeckeDetectorProfiles.cutoff
          HeckeDetectorDyadicProfiles.positiveAnnular (U^r/U^tstar)) σ t := by
      funext x
      exact inverseDetectorSchwartz_apply _ _ _ _ _ _
    rw [he]
    exact (twistProfile_support _ _ _).trans
      ((baseProfile_support _ _ _ _ _).trans HeckeDetectorDyadicProfiles.positiveAnnular_support)
  have ht : tsupport (W : ℝ→ℂ) ⊆ Set.Icc (1/4 : ℝ) (9/4) :=
    closure_minimal hw isClosed_Icc
  cases scaled
  · exact hw
  · intro x hx
    by_contra hn
    have hz : W x = 0 := by
      by_contra h
      exact hn (hw h)
    have hd : deriv (W : ℝ→ℂ) x = 0 := by
      by_contra h
      exact hn (ht (support_deriv_subset h))
    apply hx
    change scaleCLM W x = 0
    rw [scaleCLM_apply]
    simp [scaleProfile, hz, hd]

theorem exists_reference_window :
    ∃w : 𝓢(ℝ,ℂ), HasCompactSupport (w : ℝ→ℂ) ∧
      tsupport (w : ℝ→ℂ) ⊆ Set.Icc (1/18 : ℝ) (13/4) ∧
      ∀x∈Set.Icc (1/9 : ℝ) (9/4), w x = 1 := by
  obtain ⟨w,hc,hone,hs⟩ := InverseSecondChildWindows.positive_cutoff
    (1/9 : ℝ) (9/4) (by norm_num) (by norm_num)
  refine ⟨w,hc,?_,hone⟩
  convert (preTransparency := .instances) hs using 1
  norm_num

def referenceWindow : 𝓢(ℝ,ℂ) := Classical.choose exists_reference_window

def logSource (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  CubicReflectionKernel.logPullbackCLM (1/4) (9/4)
    (inverseSourceSchwartz scaled reverse n U tstar r σ t)

def familyDensity (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c v : ℝ) : ℂ :=
  density (logSource scaled reverse n U tstar r σ t) (Real.log c) v

end SevenEighths.DetectorDictionaryInverseClippedUniform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorSupportedWitness
open HeckeFamily HeckeDetectorWitnessRows

structure SupportedWitness {Label : Type*} (χ : Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    extends Witness χ U a ε tstar T allowance i where
  product_length_lower : tstar-r-ε≤ m

end SevenEighths.HeckeDetectorSupportedWitness

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentRetainedEnergy CenteredMomentDivisorRowEnergy HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def allocatedPositiveRow (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) : ℂ :=
  retainedPositiveRow η m A z W₁ W₂ (fun i : liveIndices D a => S i)
    (fun i : liveIndices D a => β i) (fun i : liveIndices D a => P i) t
    (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))

end SevenEighths.CenteredMomentDivisorRetained

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentActiveDivisorShell
open HeckeFamily CenteredMomentActiveAllocation CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

structure Source (ι:Type*) [Fintype ι] where
  η : Character
  m : O
  A : O
  t : ℝ
  slots : ι→Finset (Ideal O)
  prime : ∀i,∀I∈slots i,Prime I
  ν : ι→Ideal O→ℂ
  W : ι→ℝ→ℂ
  lo : ι→ℝ
  hi : ι→ℝ
  P : ι→ℝ
  lo_pos : ∀i,0<lo i
  P_pos : ∀i,0<P i
  support : ∀i,Function.support (W i)⊆Set.Icc (lo i) (hi i)
  W₁ : ℝ→ℂ
  W₂ : ℝ→ℂ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Source.active (s:Source ι) (D:Ideal O) : Finset (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :=
  activeAllocations s.η s.m s.A s.t s.slots
    (fun i I=>s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)) D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂

def Source.allowance (s:Source ι) (Z:ℝ) : ℝ :=
  (∑i,logWindow (s.lo i) (s.hi i))/Real.log Z

end SevenEighths.CenteredMomentActiveDivisorShell

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonMaskExpansion
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def naturalSlot (χ : Character) (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) : ℂ :=
  (Real.sqrt P:ℂ)⁻¹ * ∑ I∈pool,idealCoeff χ I*β I

def plainCoefficient (χ : Character) (D : Finset (Ideal O)) : ℂ :=
  (moebius (∏I∈D,I):ℂ)*(idealCoeff χ (∏I∈D,I)/(Real.sqrt (Ideal.absNorm (∏I∈D,I):ℝ):ℂ))

variable {α : Type*} [DecidableEq α]

def signedCoefficient (χ : Character) (R D₁ D₂ : Finset (Ideal O))
    (J : Finset α) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) : ℂ :=
  plainCoefficient χ D₁*plainCoefficient χ D₂*(-1:ℂ)^J.card*
    ∏i∈J,naturalSlot χ (pool i∩R) (β i) (P i)

def slotMass (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) : ℝ :=
  (Real.sqrt P)⁻¹ * ∑I∈pool∩R,‖β I‖

def coefficientMajorant (R D₁ D₂ : Finset (Ideal O)) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) : ℝ :=
  weight (∏I∈D₁,I)*weight (∏I∈D₂,I)*∏i∈J,slotMass R (pool i) (β i) (P i)

def uniformMajorant (R D₁ D₂ : Finset (Ideal O)) (J : Finset α) (b M : α→ℝ) : ℝ :=
  weight (∏I∈D₁,I)*weight (∏I∈D₂,I)*
    ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)

end SevenEighths.CenteredMomentCommonMaskExpansion

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentUniformDivisorShell
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

def ShellBound (ι κ:Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C ε:ℝ) : Prop := ∀(s:Source ι) (v:Source κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((s.allowance Z+v.allowance Z)/2)

end SevenEighths.CenteredMomentUniformDivisorShell

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEligibleEnergy
open HeckeFamily CenteredMomentActiveDivisorShell CenteredMomentActiveAllocation
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorRowEnergy
local notation "O" => ActualEisensteinCubic.O

structure Data (ι:Type*) [Fintype ι] extends Source ι where
  M : ι→ℝ
  M_ge_one : ∀i,1≤M i
  coefficient_bound : ∀i,∀I∈slots i,‖ν i I*W i ((Ideal.absNorm I:ℝ)/P i)‖≤M i
  b₁ : ℝ
  b₂ : ℝ
  support₁ : Function.support W₁⊆Set.Iic b₁
  support₂ : Function.support W₂⊆Set.Iic b₂
  X₁_pos : 0<X₁
  X₂_pos : 0<X₂
  Y₁_pos : 0<Y₁
  Y₂_pos : 0<Y₂
  same_product : Y₁*Y₂=X₁*X₂
  rows : Finset O
  weight : O→ℝ
  weight_nonneg : ∀z∈rows,0≤weight z

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Data.coefficient (s:Data ι) (i:ι) (I:Ideal O) : ℂ :=
  s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)

def Data.energy (s:Data ι) (D:Ideal O) : ℝ :=
  ∑z∈s.rows,s.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂‖^2

def Data.childEnergy (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : ℝ :=
  ∑z∈s.rows,s.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)

def Data.profileFactor (s:Data ι) : ℝ :=
  (2*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2

end SevenEighths.CenteredMomentEligibleEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentInductionEnergy
open HeckeFamily
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def energy (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ) (X₁ X₂:ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) : ℝ :=
  ∑'z:O,if keep z then ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
    (Φ (‖eisEmbedding z‖^2/K)).re else 0

end SevenEighths.CenteredMomentInductionEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentRadialEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRetained
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

structure Radial where
  keep : O→Prop
  profile : 𝓢(ℝ,ℂ)
  scale : ℝ
  scale_pos : 0<scale
  nonneg : ∀z:O,0≤(profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/scale)).re

def Radial.weight (r:Radial) (z:O) : ℝ :=
  if r.keep z then (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re else 0

lemma Radial.weight_nonneg (r:Radial) (z:O) : 0≤ r.weight z := by
  unfold Radial.weight
  split_ifs
  · exact r.nonneg z
  · rfl

def finiteData (s:Data ι) (r:Radial) (S:Finset O) : Data ι :=
  {s with rows:=S,weight:=r.weight,weight_nonneg:=fun z _=>r.weight_nonneg z}

def energy (s:Data ι) (r:Radial) (D:Ideal O) : ℝ :=
  ∑'z:O,r.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    CenteredMomentDivisorRowEnergy.maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂‖^2

def childEnergy (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : ℝ :=
  ∑'z:O,r.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)

end SevenEighths.CenteredMomentRadialEligibleEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCoreFloor
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O

 def zeroRow (η:Character) (m A z:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ):ℂ :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹*(rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)

 def zeroEnergy (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) (r:Radial):ℝ :=
  ∑'z:O,if r.keep z then ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖^2*
    (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0

end SevenEighths.CenteredMomentCoreFloor

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalAllocationShell
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentSlotRatios
open CenteredMomentUniformDivisorShell
local notation "O" => ActualEisensteinCubic.O

def exceptionalWeight {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (s : Source ι) (v : Source κ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ⊕Fin 2))) (Z r : ℝ) : ℝ :=
  Z^(-Real.logb Z (formalReductionFactor D a s.P)-
    Real.logb Z (formalReductionFactor D b v.P)-
    max (r-Real.logb Z (formalReductionFactor D a s.P)) 0)

def ShellBound (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C ε : ℝ) : Prop := ∀(s : Source ι) (v : Source κ) (Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r) ≤
        C*(2*T)^(2*ε)*Z^(v.allowance Z-r)

end SevenEighths.CenteredMomentExceptionalAllocationShell

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles CenteredMomentDetectorDictionary
open CenteredMomentLattice
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma detectorSchwartz_support (reverse : Bool) (n : ℕ) (σ t : ℝ) :
    Function.support (detectorSchwartz reverse n σ t:ℝ→ℂ)⊆Set.Icc (1/4) (9/4) := by
  intro x hx
  change detectorSchwartz reverse n σ t x≠0 at hx
  rw [detectorSchwartz_apply] at hx
  exact detector_profile_support reverse n σ (orientedFrequency reverse t) hx

def detectorNormProfile (reverse : Bool) (n : ℕ) (σ t h : ℝ) : 𝓢(ℝ,ℂ) :=
  normPowerProfile (detectorSchwartz reverse n σ t) (1/4) (9/4) (by norm_num)
    (detectorSchwartz_support reverse n σ t) ((detectorSchwartz reverse n σ t).smooth ⊤) h

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentOriginalReflectionApproximation
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentSectorLocalization CenteredMomentReflectedTruncation
open CenteredMomentReflectedAnnuli CenteredMomentNaturalPrimitive
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

def finiteAnnularColumn (η : Character) (F : ℝ→ℂ) (R Y : ℝ) : ℂ :=
  if hY : 0<Y then ∑n∈retainedAnnuli R Y hY,(Real.sqrt (dyadicScale n):ℂ)*
    HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0

def retainedOriginal (χ ψ : Character) (W : ℝ→ℂ) (X R t : ℝ) : ℂ :=
  let S := redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
    finiteAnnularColumn χ.inverse
      (paperRadialFourier (CompletedHeight.normTwistedSource W t)) R
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val))

end SevenEighths.CenteredMomentOriginalReflectionApproximation

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRadialPointwiseUniform
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentUniformDivisorShell
open CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Bound (ι:Type*) [Fintype ι] [DecidableEq ι] (C ε:ℝ) : Prop :=
  ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
    ∀E Z:ℝ,0≤E → 1<Z → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
    energy s r D≤C*(Ideal.absNorm D:ℝ)^(2*ε)*Z^(s.toSource.allowance Z)*
      (s.profileFactor*E)/(Ideal.absNorm D:ℝ)

end SevenEighths.CenteredMomentRadialPointwiseUniform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentReflectionWeightedEnergy
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentReflectedAnnuli
local notation "O" => HeckeFamily.O

abbrev Index (S : Finset (Ideal O)) := (S.powerset × SmoothIdeal S) × ℤ

def baseIndex (S : Finset (Ideal O)) : Index S :=
  ((⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset _)⟩,unitSmooth S),0)

def signedWeight (η ηi : Character) (S : Finset (Ideal O)) (B : ℕ)
    (a : Index S) : ℂ :=
  coefficient η ηi S a.1.1.val a.1.2 * (annularMass B a.2 : ℂ)

def annularConstant : ℝ := 1 + ∑'n : ℤ,annularMass 2 n

end SevenEighths.CenteredMomentReflectionWeightedEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentRetainedWeightedSource
open HeckeFamily CenteredMomentNaturalPrimitive CenteredMomentReflectionDeletion
open CenteredMomentReflectionMass CenteredMomentReflectionWeightedEnergy
open CenteredMomentOriginalReflectionApproximation
open CenteredMomentReflectedAnnuli CenteredMomentReflectedTruncation
open CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

abbrev sourcePrimes (χ ψ : Character) := redundantSet χ.modulus ψ.modulus

def dualScale (χ ψ : Character) (X : ℝ)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) : ℝ :=
  (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D.val,P):ℝ)/(X*norm H.val)

lemma dualScale_pos (χ ψ : Character) (X : ℝ) (hX : 0<X)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) :
    0<dualScale χ ψ X D H := by
  have hD : (∏P∈D.val,P : Ideal O)≠0 := Finset.prod_ne_zero_iff.mpr (fun P hP=>
    (redundantSet_prime χ.modulus ψ.modulus P ((Finset.mem_powerset.mp D.property) hP)).ne_zero)
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hd : 0<(Ideal.absNorm (∏P∈D.val,P):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  exact div_pos (mul_pos hQ hd) (mul_pos hX (CenteredMomentReflectionDeletion.norm_pos H.val))

def retainedColumn (χ ψ : Character) (W : ℝ→ℂ) (X R t : ℝ) (hX : 0<X)
    (B n : ℕ) (P : ℂ) (a : Index (sourcePrimes χ ψ)) : ℂ :=
  if a.2∈retainedAnnuli R (dualScale χ ψ X a.1.1 a.1.2)
      (dualScale_pos χ ψ X hX a.1.1 a.1.2) then
    HeckeDyadic.polynomial χ.inverse false
      (normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale a.2) t)
      (dyadicScale a.2*dualScale χ ψ X a.1.1 a.1.2) 0 0 * P
  else 0

end SevenEighths.CenteredMomentRetainedWeightedSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondSourceSeededPowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentFiniteProfileExceptional
open EisensteinSchwartzPoisson

open CenteredMomentLogDyadic
open MeasureTheory UniqueFactorizationMonoid

open CenteredMomentSecondSourcePowerDescent

local instance instDecidableEqSumFinOfNatNat_solutions_rc7b4eb_1 : DecidableEq (ι⊕Fin 2):=Classical.decEq _
def seededFactors (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo seedNorm : ℝ) (J₁ J₂ : ℕ) (SΦ : Finset (ℕ×ℕ))
    (W : 𝓢(ℝ,ℂ)) : Fin 4→ℝ :=
  let a:=physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo J₁ J₂ SΦ W
  ![a 0,a 1,a 2,a 3/seedNorm]

end SevenEighths.CenteredMomentSecondSourceSeededPowerDescent

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformReflectionApproximation
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentOriginalReflectionApproximation
open CenteredMomentSectorLocalization CenteredMomentNaturalPrimitive
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

def retainedSchwartz (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) : ℂ :=
  let S := redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient ψ ψ.inverse S D I*
    finiteAnnularColumn χ.inverse (paperRadialFourier G) R
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val))

def discardedSchwartz (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) : ℂ :=
  let S := redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient ψ ψ.inverse S D I*
    HeckeDyadic.polynomial χ.inverse false (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier G x)
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0

end SevenEighths.CenteredMomentUniformReflectionApproximation

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

def smallDyadicIndices (L : ℝ) : Finset ℕ :=
  (Finset.range (Nat.find (pow_unbounded_of_one_lt L (by norm_num : (1:ℝ)<2)))).filter (fun n=>(2:ℝ)^n≤L)

@[simp] lemma mem_smallDyadicIndices {L : ℝ} {n : ℕ} : n∈smallDyadicIndices L ↔ (2:ℝ)^n≤L := by
  simp only [smallDyadicIndices,Finset.mem_filter,Finset.mem_range]
  constructor
  · exact And.right
  · intro hn
    refine ⟨?_,hn⟩
    by_contra h
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (not_lt.mp h)
    exact not_lt_of_ge (hp.trans hn) (Nat.find_spec (pow_unbounded_of_one_lt L (by norm_num : (1:ℝ)<2)))

def smallDyadicRows (L : ℝ) (n : ℕ) : Finset FreeRow := (dyadicRows 1 n).filter (fun u=>rowNorm u<L)

@[simp] lemma mem_smallDyadicRows {L : ℝ} {n : ℕ} {u : FreeRow} :
    u∈smallDyadicRows L n ↔ u∈dyadicRows 1 n ∧ rowNorm u<L := Finset.mem_filter

end SevenEighths.ProbeHighRowFamily

end

end OAI
end


