-- Prove2me | Definitions.Def_OAIHecke78B012
-- name    : OAIHecke78B012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T23:46:39.864366+00:00
-- url     : https://prove2.me/theorems/1159f792-7d48-43cb-a4a9-e7e6072707a3
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 13 of 29
-- statement:
--   Definitions bundle 13 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B009` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Descent.InitializationEnergy`, `Inversion.SecondFibers`, `Descent.SecondEnergy`, `Descent.SecondFreshAssembly`, `Descent.TripleMass`, `Descent.SecondCauchy`, `Inversion.InitialArithmetic`, `Descent.SecondSourceTuples`, `Descent.CubeSource`, `Descent.SecondSourceEncoding`, `Descent.ActualSecondEnergy`, `Descent.SecondCanonicalChild`, `Descent.SecondPuncture`, `Descent.SecondPhysicalRows`, `Inversion.SecondChildWindows`, `Descent.SecondSourceAttachment`, `Descent.SecondParentAssembly`, `Descent.SecondVariableCutoff`, `Inversion.SecondSourceBlocks`, `Descent.SecondCellPhysical`, `Descent.SecondCellParameters`, `Descent.PrioritySourceBudget`, `Descent.SecondAdmissible`, `Descent.ActualChildState`, `Descent.ActualChildStateLabels`, `Descent.ActualChildStateRadius`, `Descent.FirstChildWindowsCells`, `Descent.FirstOriginalProfileCells`, `Descent.FirstOriginalProfileScales`, `Descent.GlobalRetainedGatesGeometry`, `Inversion.InitialQuotientGeometry`, `Inversion.InitialEnergyCallerCanonical`, `Inversion.InitialEnergyCallerOpposite`, `Inversion.InitialRayAttachment`, `Inversion.InitialPhysicalMeasure`, `Inversion.InitialEnergyCallerModes`, `Inversion.InitialEnergyCallerSource`, `Inversion.InitialEnergyCallerAllocation`, `Inversion.InitialEnergyCallerUnits`, `Inversion.InitialEnergyCallerSourceMask`, `Inversion.InitialEnergyCallerWindows`, `Inversion.InitialHighFrequencyTailSource`, `Inversion.InitialHighFrequencyTailCoefficient`, `Inversion.InitialPhysicalReassembly`, `Inversion.InitialPhysicalLimit`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B009

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B012

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Descent.InitializationEnergy
  Inversion.SecondFibers
  Descent.SecondEnergy
  Descent.SecondFreshAssembly
  Descent.TripleMass
  Descent.SecondCauchy
  Inversion.InitialArithmetic
  Descent.SecondSourceTuples
  Descent.CubeSource
  Descent.SecondSourceEncoding
  Descent.ActualSecondEnergy
  Descent.SecondCanonicalChild
  Descent.SecondPuncture
  Descent.SecondPhysicalRows
  Inversion.SecondChildWindows
  Descent.SecondSourceAttachment
  Descent.SecondParentAssembly
  Descent.SecondVariableCutoff
  Inversion.SecondSourceBlocks
  Descent.SecondCellPhysical
  Descent.SecondCellParameters
  Descent.PrioritySourceBudget
  Descent.SecondAdmissible
  Descent.ActualChildState
  Descent.ActualChildStateLabels
  Descent.ActualChildStateRadius
  Descent.FirstChildWindowsCells
  Descent.FirstOriginalProfileCells
  Descent.FirstOriginalProfileScales
  Descent.GlobalRetainedGatesGeometry
  Inversion.InitialQuotientGeometry
  Inversion.InitialEnergyCallerCanonical
  Inversion.InitialEnergyCallerOpposite
  Inversion.InitialRayAttachment
  Inversion.InitialPhysicalMeasure
  Inversion.InitialEnergyCallerModes
  Inversion.InitialEnergyCallerSource
  Inversion.InitialEnergyCallerAllocation
  Inversion.InitialEnergyCallerUnits
  Inversion.InitialEnergyCallerSourceMask
  Inversion.InitialEnergyCallerWindows
  Inversion.InitialHighFrequencyTailSource
  Inversion.InitialHighFrequencyTailCoefficient
  Inversion.InitialPhysicalReassembly
  Inversion.InitialPhysicalLimit
-/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalQuadraticSieve SevenEighths.InverseInitialFibers
open IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

abbrev InitialChild := Ideal Eis × Ideal Eis × Eis

def initialChild {J : ℕ} (x : InitialTuple J) : InitialChild :=
  (idealQuotient x.divisor x.common, x.divisor * x.residual,
    primaryGenerator x.divisor * x.frequency)

structure InitialSourceValid {J : ℕ} (x : InitialTuple J) : Prop where
  common_ne_zero : x.common ≠ 0
  residual_ne_zero : x.residual ≠ 0
  divisor_good : primaryGenerator x.divisor ≠ 0
  divisor_dvd : x.divisor ∣ x.common
  assigned_dvd : ∀ i, (x.assigned i).val ∣ x.common * x.residual

def initialQuotientSet {J : ℕ} (source : Finset (InitialTuple J)) : Finset (Ideal Eis) :=
  source.image (fun x => (initialChild x).1)

def initialDivisorWeight (J : ℕ) (c : InitialChild) : ℝ :=
  ((idealDivisors c.2.1).card : ℝ) ^ (J + 1) * ((idealDivisors c.1).card : ℝ) ^ J

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseSecondFibers

open ActualEisensteinCubic
open CompletedGauss (primaryGenerator primaryGenerator_mul)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open scoped BigOperators Classical
noncomputable section

@[ext] structure OuterTriple where
  q0 : Ideal O
  quotient : Ideal O
  residual : Ideal O

@[ext] structure SecondTuple (Jo Jn : ℕ) where
  outer : OuterTriple
  core : Fin 8 → Ideal O
  commonResidual : Ideal O
  cubeResidual : Ideal O
  secondCube : Ideal O
  extractedCommon : Ideal O
  frequency : O
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal
  newAssigned : Fin Jn → SmoothMobiusCorrection.PrimeIdeal

structure Valid {Jo Jn : ℕ} (x : SecondTuple Jo Jn)
    (γ : OuterTriple) (f : Ideal O) (k : O) : Prop where
  outer_eq : x.outer = γ
  label : x.core 0 * x.core 1 * x.core 2 * x.commonResidual = f
  j_split : x.core 3 * x.cubeResidual = x.core 0
  b_split : x.core 4 * x.secondCube = γ.q0^2 * x.cubeResidual^2 * x.core 3
  a1 : x.core 5 ∣ (x.core 4 * x.secondCube).radical
  a2 : x.core 6 ∣ (x.core 4 * x.secondCube).radical
  d : x.core 7 ∣ x.core 1 * (x.core 4 * x.secondCube).radical
  extracted_eq : x.core 2 * γ.residual = x.extractedCommon
  generator_d : primaryGenerator (x.core 7) ≠ 0
  generator_d2 : primaryGenerator (x.core 2) ≠ 0
  row_eq : primaryGenerator (x.core 7) * primaryGenerator (x.core 2) * x.frequency = k
  old_dvd : ∀ i, (x.oldAssigned i).val ∣ γ.q0 * f * γ.quotient
  new_dvd : ∀ i, (x.newAssigned i).val ∣ f * γ.residual

def originalSource {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) : Finset (SecondTuple Jo Jn) :=
  source.filter fun x => (∀ i, x.oldAssigned i ∈ oldLists i) ∧
    (∀ i, x.newAssigned i ∈ newLists i) ∧ keep x

end
end SevenEighths.InverseSecondFibers

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss SevenEighths.InverseSecondFibers IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

abbrev SecondChild := OuterTriple × Ideal Eis × Eis

def secondChild {Jo Jn : ℕ} (x : SecondTuple Jo Jn) : SecondChild :=
  (x.outer, x.core 0 * x.core 1 * x.core 2 * x.commonResidual,
    primaryGenerator (x.core 7) * primaryGenerator (x.core 2) * x.frequency)

def secondDivisorWeight (K : ℕ) (c : SecondChild) : ℝ :=
  ((idealDivisors c.2.1).card : ℝ) ^ (9 + 4*K) *
    ((idealDivisors c.1.q0).card : ℝ) ^ (5 + 2*K) *
    ((idealDivisors c.1.quotient).card : ℝ) ^ (2*K) *
    ((idealDivisors c.1.residual).card : ℝ) ^ (2*K)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondSeparatedPair (F : Finset ι) (x : SecondProfileData ι)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (v : Frequency × (Fin 6 → ℝ)) : ℂ :=
  let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope v.1 v.2
  secondOuterPhase h
    (secondRelativeLog (secondActualNorms p x ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
  star (canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedLeft x.rayLeft
    x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
    slots₁ lists₁ a₁ (childLogTest ω₁ (-h 4)) (primeProductNorm p x.overlap*X₀)) *
  canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedRight x.rayRight
    x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor (-x.frequency)
    slots₂ lists₂ a₂ (childLogTest ω₂ (h 5)) (primeProductNorm p x.overlap*X₀)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open SevenEighths.InverseSecondFibers IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def tripleDivisorWeight (K : ℕ) (γ : OuterTriple) : ℝ :=
  ((idealDivisors γ.q0).card : ℝ)^(5+2*K) *
    ((idealDivisors γ.quotient).card : ℝ)^(2*K) *
    ((idealDivisors γ.residual).card : ℝ)^(2*K)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open SevenEighths.InverseSecondFibers IdealMobiusDivisorSum CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondLabelEnergy (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (F : SecondChild → ℂ) (γ : OuterTriple) : ℝ :=
  ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(9+4*K) *
    ∑ k ∈ rows, ‖F (γ,f,k)‖^2

def secondCanonicalPolynomial {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : OuterTriple → Eis →* ℂ) (puncture : OuterTriple → Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) : ℂ :=
  finiteCanonicalMarkedRow p hp hcop hg pool (Ψ c.1) (puncture c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a (W c.1) X

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open MixedCrossSeparation (columnCoefficient)
open SevenEighths.InverseMoment SevenEighths.InverseInitialFibers
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, λ₀∉Ideal.span {p i})

def initialColumn (Ψ : O →* ℂ) (j C d h : O)
    (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * Ψ (∏ i∈S,p i) *
    rowCoprimeMask (fun i=>Ideal.span {p i}) S (j*C) *
    star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S d) *
    finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S h * H S

def sourceIdeal (S : Finset ι) : Ideal O := Ideal.span {∏ i∈S,p i}

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_gen (hpr : ∀ i,λ₀^2∣p i-1) (S : Finset ι) :
    primaryGenerator (sourceIdeal p S)=∏ i∈S,p i := by
  apply primaryGenerator_span _ (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    have he : p i*(∏ j∈S,p j)-1=(p i-1)*(∏ j∈S,p j)+((∏ j∈S,p j)-1) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left (hpr i) _) ih

def sourcePrime (i : ι) : SmoothMobiusCorrection.PrimeIdeal :=
  ⟨Ideal.span {p i},Ideal.prime_of_isPrime (NeZero.ne _) inferInstance⟩

def sourceTuple {J : ℕ} (G E V : Finset ι) (h : O) (assigned : Fin J→ι) : InitialTuple J :=
  ⟨sourceIdeal p G,sourceIdeal p E,sourceIdeal p V,h,fun i=>sourcePrime p (assigned i)⟩

@[ext] structure Source (J : ℕ) where
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : O
  assigned : Fin J→ι

def toTuple {J : ℕ} (x : Source (ι:=ι) J) : InitialTuple J :=
  sourceTuple p x.common x.divisor x.overlap x.frequency x.assigned

def sectorSource {J : ℕ} (u : Oˣ) (x : Source (ι:=ι) J) : Source (ι:=ι) J :=
  {x with frequency := (u : O)^5*x.frequency}

end SevenEighths.InverseInitialArithmetic

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourcePrime )
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

@[ext] structure SecondOriginalSource (ι : Type*) (Jo Jn : ℕ) where
  q0 : Ideal Eis
  quotient : Ideal Eis
  J : Ideal Eis
  C : Ideal Eis
  s : Ideal Eis
  b1 : Ideal Eis
  A1 : Ideal Eis
  A2 : Ideal Eis
  dK : Ideal Eis
  J2 : Ideal Eis
  b2 : Ideal Eis
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : Eis
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal
  newAssigned : Fin Jn → ι

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def originalSecondTuple {Jo Jn : ℕ} (u v : Eisˣ) (x : SecondOriginalSource ι Jo Jn) : SecondTuple Jo Jn where
  outer := ⟨x.q0,x.quotient,sourceIdeal p (x.common \ x.divisor)⟩
  core := ![x.J,x.C,sourceIdeal p x.divisor,x.s,x.b1,x.A1,x.A2,x.dK]
  commonResidual := sourceIdeal p x.overlap
  cubeResidual := x.J2
  secondCube := x.b2
  extractedCommon := sourceIdeal p x.common
  frequency := secondUnitFrequency u v x.frequency
  oldAssigned := x.oldAssigned
  newAssigned := fun i => sourcePrime p (x.newAssigned i)

structure SecondOriginalValid {Jo Jn : ℕ} (x : SecondOriginalSource ι Jo Jn) : Prop where
  j_split : x.s*x.J2 = x.J
  b_split : x.b1*x.b2 = x.q0^2*x.J2^2*x.s
  a1 : x.A1 ∣ (x.b1*x.b2).radical
  a2 : x.A2 ∣ (x.b1*x.b2).radical
  first_divisor : x.dK ∣ x.C*(x.b1*x.b2).radical
  first_generator : primaryGenerator x.dK ≠ 0
  second_subset : x.divisor ⊆ x.common
  old_support : ∀ i, (x.oldAssigned i).val ∣ x.q0*x.J*x.C*x.quotient
  new_support : ∀ i, x.newAssigned i ∈ x.common ∪ x.overlap

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
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourcePrime )
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def cubeSecondSource {Jo Jn : ℕ} (B C D G E V : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι) :
    SecondOriginalSource ι Jo Jn where
  q0 := Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  quotient := t
  J := Ideal.span {jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  C := sourceIdeal p C
  s := Ideal.span {squarefreeLabel p B (fun i => v₁ i+v₂ i)}
  b1 := Ideal.span {primeProduct p B v₁}
  A1 := Ideal.span {aLabel p B ε₁}
  A2 := Ideal.span {aLabel p B ε₂}
  dK := sourceIdeal p D
  J2 := Ideal.span {j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  b2 := Ideal.span {primeProduct p B v₂}
  common := G
  divisor := E
  overlap := V
  frequency := k
  oldAssigned := oldAssigned
  newAssigned := newAssigned

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
open InverseInitialArithmetic (sourceIdeal )
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

@[ext] structure MarkedSecondSource (ι : Type*) (Jo Jn : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  second : SecondExpansionData ι
  quotient : Ideal Eis
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal
  newAssigned : Fin Jn → ι

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def markedSecondOriginal {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : SecondOriginalSource ι Jo Jn :=
  cubeSecondSource p x.cube.support x.firstCommon x.firstDivisor
    x.second.sourceCommon x.second.divisor x.second.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
    x.quotient x.second.frequency x.oldAssigned x.newAssigned

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers IdealMobiusDivisorSum
open InverseInitialArithmetic (sourceIdeal )
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def actualSecondChild {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) : SecondChild :=
  secondChild (originalSecondTuple p u v (markedSecondOriginal p x))

def actualSecondTriples {Jo Jn : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo Jn)) : Finset OuterTriple :=
  source.image (fun x => (actualSecondChild p u v x).1)

structure ActualSecondSourceConditions {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) : Prop where
  admissible : ∀ x ∈ source, x.cube.Admissible
  common_disjoint : ∀ x ∈ source, Disjoint x.firstCommon x.cube.support
  first_divisor : ∀ x ∈ source, x.firstDivisor ⊆ x.firstCommon∪x.cube.support
  second_divisor : ∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon
  old_support : ∀ x ∈ source, ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient
  new_support : ∀ x ∈ source, ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap
  quotient_nonzero : ∀ x ∈ source, x.quotient ≠ 0

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
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hp

def actualSecondPuncture (m : Eis) (γ : OuterTriple) : Eis :=
  (m*primaryGenerator γ.q0)*primaryGenerator γ.residual

def actualSecondRawLabel {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Eis :=
  ((∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
    primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor * ∏ i ∈ x.second.overlap,p i

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen )
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def actualSecondRadicalPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  ConcretePrimeRowBridge.idealGenerator (Ideal.span {actualSecondPuncture m γ}).radical

def actualSecondInheritedPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  actualSecondPuncture (m*ConcretePrimeRowBridge.idealGenerator γ.quotient) γ

def actualSecondInheritedRadicalPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  actualSecondRadicalPuncture (m*ConcretePrimeRowBridge.idealGenerator γ.quotient) γ

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def actualSecondMultiplier {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Eis :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor *
    primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseSecondChildWindows
open InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
local notation "O" => ActualEisensteinCubic.O

theorem positive_cutoff (a b : ℝ) (ha : 0<a) (_hab : a≤b) :
    ∃ w : 𝓢(ℝ,ℂ), HasCompactSupport (w : ℝ→ℂ) ∧
      (∀ x∈Set.Icc a b,w x=1) ∧ tsupport (w : ℝ→ℂ)⊆Set.Icc (a/2) (b+1) := by
  have hKU : Set.Icc a b⊆Set.Ioo (a/2) (b+1) := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hKU
  let v : ℝ→ℂ := fun x => (f x:ℂ)
  have hv : ContDiff ℝ ∞ v := Complex.ofRealCLM.contDiff.comp (by simpa using hf)
  have hvs : Function.support v⊆Set.Icc (a/2) (b+1) := by
    intro x hx
    have hh : x∈Function.support f := by simpa [v,Function.mem_support] using hx
    rw [hs] at hh
    exact ⟨hh.1.le,hh.2.le⟩
  have hvc := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hvs
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,closure_minimal hvs isClosed_Icc⟩
  intro x hx
  change (f x:ℂ)=1
  rw [(hone x).mp hx]
  rfl

def outerIndex (i : Fin 4) : Fin 6 := i.castLE (by decide)

def actualOuterRatios {ι : Type*} [DecidableEq ι] (p : ι→O)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (G E V B : ℝ) : Fin 4→ℝ :=
  ![primeProductNorm p x.second.sourceCommon/G,
    ‖ConcreteTraceCRT.eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.second.divisor)‖^2/E,
    primeProductNorm p x.second.overlap/V,‖ConcreteTraceCRT.eisEmbedding x.second.frequency‖^2/B]

end SevenEighths.InverseSecondChildWindows

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

@[ext] structure SecondParentSource (ι : Type*) (Jo : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  quotient : Ideal Eis
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal

def attachSecondExpansion {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) : MarkedSecondSource ι Jo 0 where
  cube := parent.cube
  firstCommon := parent.firstCommon
  firstDivisor := parent.firstDivisor
  second := x
  quotient := parent.quotient
  oldAssigned := parent.oldAssigned
  newAssigned := Fin.elim0

def secondParentOf {Jo : ℕ} (x : MarkedSecondSource ι Jo 0) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := x.oldAssigned

variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondParentLabel {Jo : ℕ} (parent : SecondParentSource ι Jo) : Eis :=
  (∏ i∈parent.firstCommon,p i)*jLabel p parent.cube.support
    (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit

def secondParentDivisor {Jo : ℕ} (parent : SecondParentSource ι Jo) : Eis :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) parent.firstDivisor

def secondParentPuncture {Jo : ℕ} (m : Eis) (parent : SecondParentSource ι Jo) : Eis :=
  (m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*
    b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit*secondParentDivisor p parent

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] in
@[simp] theorem secondParentOf_attach {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) : secondParentOf (attachSecondExpansion parent x) = parent := rfl

def attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι)) :
    Finset (MarkedSecondSource ι Jo 0) :=
  parents.biUnion (fun parent => (source parent).image (attachSecondExpansion parent))

variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondVariableCutoff {Jo : ℕ} (parent : SecondParentSource ι Jo) (R : Finset ι → Finset ι → ℝ)
    (G E : Finset ι) : Finset Eis :=
  childFrequencyBall (secondParentDivisor p parent*primeSubsetGenerator (fun i => Ideal.span {p i}) E) (R G E)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseSecondSourceBlocks
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseMoment
open InverseSecondFibers
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]

abbrev BlockIndex := Fin 4 → ℕ

def outerNorms (p : ι → O) {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Fin 4 → ℝ :=
  ![primeProductNorm p x.second.sourceCommon, primeProductNorm p x.second.divisor,
    primeProductNorm p x.second.overlap, ‖eisEmbedding x.second.frequency‖^2]

def dyadIndex (r : ℝ) : ℕ := ⌊Real.logb 2 r⌋₊
def dyadScale (n : ℕ) : ℝ := 2^n

def index (p : ι → O) {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : BlockIndex :=
  fun i => dyadIndex (outerNorms p x i)

def keys (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) : Finset BlockIndex :=
  source.image (index p)

def cell (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : Finset (MarkedSecondSource ι Jo Jn) := source.filter (fun x => index p x = d)

omit [DecidableEq ι] in
@[simp] theorem mem_cell (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) :
    x ∈ cell p source d ↔ x ∈ source ∧ index p x = d := Finset.mem_filter

def scales (d : BlockIndex) : Fin 4 → ℝ := fun i => dyadScale (d i)

def capBox (A : Fin 4 → ℝ) (Z : ℝ) : Finset BlockIndex :=
  Fintype.piFinset (fun i => Finset.range (dyadIndex (Z^(A i))+1))

def capConstant (A : Fin 4 → ℝ) : ℝ := (∑ i,A i)/Real.log 2

omit [DecidableEq ι] in
@[simp] theorem keys_empty (p : ι → O) (Jo Jn : ℕ) :
    keys p (∅ : Finset (MarkedSecondSource ι Jo Jn)) = ∅ := by simp [keys]

omit [DecidableEq ι] in
@[simp] theorem cell_empty (p : ι → O) (Jo Jn : ℕ) (d : BlockIndex) :
    cell p (∅ : Finset (MarkedSecondSource ι Jo Jn)) d = ∅ := by simp [cell]

end SevenEighths.InverseSecondSourceBlocks

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller
open FourierBridge CompletedHeight SecondPassIntegration
local notation "O" => ActualEisensteinCubic.O

def secondCellColumnExponent (Z X:ℝ) (d:BlockIndex):ℝ :=
  Real.logb Z (X/(scales d 0*scales d 2))

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseInitialArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def secondCellExponent (Z:ℝ) (d:BlockIndex) (i:Fin 4):ℝ:=Real.logb Z (scales d i)

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
local notation "O"=>ActualEisensteinCubic.O

def priorityCellScalar (Z Y L X ell Ractive j t eta eps epsmass B:ℝ) (ray:ℂ) (d:BlockIndex):ℝ :=
  (Real.exp (6*L)*‖(Y:ℂ)*ray*((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
    Z^((secondCount ell Ractive j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)*(1+epsmass))*
    Z^(2*(max 0 (secondCellColumnExponent Z X d)+
      (secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta))+eps)

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def actualSecondPunctureWidth (Z : ℝ) (m : Eis) (γ : OuterTriple) : ℝ :=
  Real.logb Z (‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def actualCellLabelExponent (Z B j eta : ℝ) (d : BlockIndex) : ℝ :=
  secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta

def actualCellTotalExponent (Z X B j eta : ℝ) (d : BlockIndex) : ℝ :=
  max 0 (secondCellColumnExponent Z X d)+actualCellLabelExponent Z B j eta d

def actualCellClipping (Z X : ℝ) (d : BlockIndex) : ℝ :=
  max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d

variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

end SevenEighths.InverseMoment
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def actualCellLabels {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : Finset (Ideal O) :=
  (cell p source d).image (fun x=>(actualSecondChild p 1 1 x).2.1)

end SevenEighths.InverseMoment
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def actualCellRowExponent (Z M ell A t V j eta : ℝ) (d : BlockIndex) : ℝ :=
  childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta

def actualCellRowRadius (Z M ell A t V j eta : ℝ) (d : BlockIndex) : ℝ :=
  Z^(actualCellRowExponent Z M ell A t V j eta d)

end SevenEighths.InverseMoment
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstChildWindows
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels
open InverseSecondSourceBlocks (dyadIndex dyadScale )
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

abbrev SourceIndex := Fin 6→ℕ

def sourceNorms {κ : Type*} (A₁ A₂ C R : κ→ℝ) (d h : κ→O) (x : κ) : Fin 6→ℝ :=
  ![A₁ x,A₂ x,C x,‖eisEmbedding (d x)‖^2,R x,‖eisEmbedding (h x)‖^2]

def sourceIndex {κ : Type*} (q : κ→Fin 6→ℝ) (x : κ) : SourceIndex := fun i=>dyadIndex (q x i)
def sourceCell {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ) (k : SourceIndex) :=
  S.filter (fun x=>sourceIndex q x=k)

def commonSelector {ι : Type*} [DecidableEq ι] (p : ι→O) (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι) : ℂ :=
  if dyadIndex (primeProductNorm p D)=l then selector D else 0

def rawScales (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) : Fin 9→ℝ :=
  ![dyadScale (k 0),dyadScale (k 1),dyadScale (k 2),dyadScale (k 3),dyadScale (k 4),
    dyadScale l,dyadScale (k 5),T₁,T₂]

end SevenEighths.InverseMomentFirstChildWindows
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

def originalNorms (x : OriginalIndex ι) : Fin 6→ℝ :=
  sourceNorms (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p)
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) x

def originalOuterCell (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :
    Finset (FirstOriginalOuter ι) :=
  (firstOriginalOuter pool Q).filter (fun x=>∀i:Fin 5,
    dyadIndex (originalNorms p ⟨x,(1,1)⟩ i.castSucc)=k i.castSucc)

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment InverseMomentFirstChildWindows InverseSecondSourceBlocks

def physicalScales (X : ℝ) (k : SourceIndex) (l : ℕ) : Fin 9→ℝ :=
  rawScales k l (X/(dyadScale (k 0)*dyadScale (k 2)*dyadScale l))
    (X/(dyadScale (k 1)*dyadScale (k 2)*dyadScale l))

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment
open InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
def geometrySource {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    Finset (MarkedSecondSource ι Jo Jn) :=
  source.filter (fun x=>primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X)

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic IdealMobiusDivisorSum CompletedGauss CanonicalQuadraticSieve
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
namespace SevenEighths.InverseInitialQuotientGeometry

local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)

def sourceWeight {J : ℕ} (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (Z B θ : ℝ) (x : Source (ι:=ι) J) : ℂ :=
  A x * ψC ((Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Z^B) *
    ψd ((Ideal.absNorm (sourceIdeal p x.divisor) : ℝ)/Z^θ)

def retained {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ) (Z B θ : ℝ) : Finset (Source (ι:=ι) J) :=
  S.filter (fun x => sourceWeight p A ψC ψd Z B θ x ≠ 0)

def quotientSet {J : ℕ} (S : Finset (Source (ι:=ι) J)) : Finset (Ideal Eis) :=
  S.image (fun x => sourceIdeal p (x.common\x.divisor))

variable (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def normalizedMass (J : ℕ) (T : Finset (Ideal Eis)) (H : ℝ) : ℝ :=
  H⁻¹ * ∑ t ∈ T, ((idealDivisors t).card : ℝ)^J

def assignedCenter {σ : Type*} (slots : Finset σ) (z : σ → ℝ) : ℝ := ∑ i ∈ slots, z i

def assignedElement {σ : Type*} (slots : Finset σ) (q : σ → Eis) : Eis := ∏ i ∈ slots, q i

end SevenEighths.InverseInitialQuotientGeometry

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
namespace SevenEighths.InverseInitialEnergyCallerCanonical
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def child (pool : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (c : InitialChild) : ℂ :=
  finiteCanonicalMarkedRow p hp hcop hg pool Ψ (j*primaryGenerator c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a W X

end SevenEighths.InverseInitialEnergyCallerCanonical

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
open SevenEighths.InverseInitialEnergyCallerCanonical
namespace SevenEighths.InverseInitialEnergyCallerOpposite
local notation "Eis" => ActualEisensteinCubic.O

def negativeChild (c : InitialChild) : InitialChild := (c.1,c.2.1,-c.2.2)

variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseInitialEnergyCallerOpposite

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseInitialRayAttachment
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open FirstCauchyArithmetic SecondPassArithmetic ConcreteTraceCRT EisensteinSchwartzPoisson
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialArithmetic InverseInitialProfile
local notation "O" => ActualEisensteinCubic.O

def elementCharacter (η : Ideal O →* ℂ) : O →* ℂ where
  toFun x := η (Ideal.span {x})
  map_one' := by rw [Ideal.span_singleton_one, ←Ideal.one_eq_top, map_one]
  map_mul' x y := by rw [←Ideal.span_singleton_mul_span_singleton,map_mul]

theorem poolPrimary_primary (F : Finset (Ideal O)) (hF : ∀ I ∈ F,Admissible I)
    (i : primePool F) : goodLambda^2 ∣ poolPrimary F i-1 :=
  (primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2

section RayModes
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})
open FirstPassCubeLabels (primeProductNorm )

def initialTest (σ : Finset ι → ℂ) (V : ℝ → ℂ) (Z D : ℝ) (A : Finset ι) : ℂ :=
  σ A*V (primeProductNorm p A/Z^D)

def initialBeta (Ψ : O →* ℂ) (j : O) (G : Finset ι) : ℂ :=
  (‖Ψ (∏ i ∈ G,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) G j‖^2 : ℝ)

def initialPhysicalMode (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) (G U T E : Finset ι) (h : O) : ℂ :=
  initialBeta p Ψ j G * (moebius (sourceIdeal p E) : ℂ) *
    (∑ ρ : SecondRayIndex,secondRayCoefficient ρ *
      star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i ∈ G,p i)
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) h (fun A => σ (G∪A)) U) *
      initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i ∈ G,p i)
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) (-h) (fun A => σ (G∪A)) T) *
    physicalKernel (fun x => star (V x)) V Φ Z D m
      (physicalCoordinates (sourceIdeal p G) (sourceIdeal p E) 1
        (sourceIdeal p U) (sourceIdeal p T) h)

end RayModes

end SevenEighths.InverseInitialRayAttachment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

namespace SevenEighths.InverseInitialPhysicalMeasure
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialRayAttachment
open InverseInitialKernelBridge InverseInitialProfile InverseInitialClippedColumns
open MeasureTheory FourierBridge JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

@[ext] structure Point (ι : Type*) where
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  left : Finset ι
  right : Finset ι
  frequency : O

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})

def divisor (x : Point ι) : O := primeSubsetGenerator (fun i=>Ideal.span {p i}) x.divisor

def quotient (x : Point ι) : O := primaryGenerator (sourceIdeal p (x.common\x.divisor))

def coordinates (x : Point ι) : Fin 6 → ℝ :=
  physicalCoordinates (sourceIdeal p x.common) (sourceIdeal p x.divisor)
    (sourceIdeal p x.overlap) (sourceIdeal p x.left) (sourceIdeal p x.right) x.frequency

structure Valid (x : Point ι) : Prop where
  divisor_subset : x.divisor⊆x.common
  overlap_left : Disjoint x.overlap x.left
  overlap_right : Disjoint x.overlap x.right
  frequency_nonzero : x.frequency≠0

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem divisor_span (x : Point ι) : Ideal.span {divisor p x}=sourceIdeal p x.divisor := by
  simpa only [divisor,sourceIdeal,FiniteGaussPhase.span_finset_prod] using
    pairDivisor_span (fun i=>Ideal.span {p i}) x.divisor

include hp in
def unitSector (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) : Oˣ :=
  Classical.choose (generator_eq_unit_primary (sourceIdeal p x.divisor) (divisor p x)
    (divisor_span p x) (by rw [sourceIdeal_gen p hp hpr]; exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

def outerCoefficient (Ψ : O →* ℂ) (j : O) (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  initialBeta p Ψ j x.common * (UniqueFactorizationMonoid.moebius (sourceIdeal p x.divisor):ℂ) *
    supportMobius (fun i=>Ideal.span {p i}) x.overlap * secondRayCoefficient ρ *
    star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i∈x.common,p i)
      (divisor p x) x.frequency (fun _=>1) x.overlap) *
    initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i∈x.common,p i)
      (divisor p x) (-x.frequency) (fun _=>1) x.overlap

def canonicalColumn (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ) (x : Point ι) (h : O)
    (H : Finset ι→ℂ) (N : Finset ι) : ℂ :=
  secondChildColumn p hp hcop hg Ψ (j*quotient p x)
    (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
    (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h))
    (fun A=>σ (x.common∪(x.overlap∪A))*H A) N

def physicalTerm (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  (initialBeta p Ψ j x.common * (UniqueFactorizationMonoid.moebius (sourceIdeal p x.divisor):ℂ) *
    supportMobius (fun i=>Ideal.span {p i}) x.overlap * secondRayCoefficient ρ) *
  star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) x.frequency (fun A=>σ (x.common∪A)) (x.overlap∪x.left)) *
  initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) (-x.frequency) (fun A=>σ (x.common∪A)) (x.overlap∪x.right) *
  physicalKernel W₁ W₂ Φ Z D m
    (physicalCoordinates (sourceIdeal p x.common) (sourceIdeal p x.divisor) 1
      (sourceIdeal p (x.overlap∪x.left)) (sourceIdeal p (x.overlap∪x.right)) x.frequency)

def barePair (hpr : ∀ i,goodLambda^2∣p i-1) (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι→ℂ) (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  outerCoefficient p hp hcop hg Ψ j x ρ *
    star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j σ x x.frequency (fun _=>1) x.left) *
    canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j σ x (-x.frequency) (fun _=>1) x.right

def columnRatio (N : Finset ι) (Z D B v : ℝ) : ℝ :=
  (Ideal.absNorm (sourceIdeal p N):ℝ)/Z^(columnCenter D B v)

def canonicalPairMode (hpr : ∀ i,goodLambda^2∣p i-1) (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι→ℂ) (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (x : Point ι) (ρ : SecondRayIndex) (z : Frequency × (Fin 6→ℝ)) : ℂ :=
  let height :=  profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
  outerCoefficient p hp hcop hg Ψ j x ρ *
    secondOuterPhase height (relativeLog (coordinates p x) Z D B v θ H) *
    star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j σ x x.frequency
      (fun A=>childLogTest ω₁ (-height 4) (columnRatio p A Z D B v)) x.left) *
    canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j σ x (-x.frequency)
      (fun A=>childLogTest ω₂ (height 5) (columnRatio p A Z D B v)) x.right

def physicalBlock (source : Finset (Point ι)) (w : Point ι→ℂ)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) : ℂ :=
  ∑ x∈source,∑ ρ : SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ

def canonicalBlock (hpr : ∀ i,goodLambda^2∣p i-1)
    (source : Finset (Point ι)) (w : Point ι→ℂ) (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ) (z : Frequency × (Fin 6→ℝ)) : ℂ :=
  ∑ x∈source,∑ ρ : SecondRayIndex,w x*canonicalPairMode p hp hcop hg hpr Ψ j σ ω₁ ω₂ Z D B v θ H x ρ z

def BlockSupport (source : Finset (Point ι)) (W₁ W₂ ω₁ ω₂ : ℝ→ℂ)
    (V : Fin 6→ℝ→ℂ) (Z D B v θ H c₁ c₂ θ₁ θ₂ : ℝ) : Prop :=
  (∀ x∈source,clippedSource W₁ c₁ θ₁
    (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
      relativeNorm (coordinates p x) Z D B v θ H 4)≠0 → star (ω₁ (columnRatio p x.left Z D B v))=1) ∧
  (∀ x∈source,clippedSource W₂ c₂ θ₂
    (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
      relativeNorm (coordinates p x) Z D B v θ H 5)≠0 → ω₂ (columnRatio p x.right Z D B v)=1) ∧
  (∀ x∈source,star (ω₁ (columnRatio p x.left Z D B v))≠0 →
    ω₂ (columnRatio p x.right Z D B v)≠0 → ∀ i,V i (relativeLog (coordinates p x) Z D B v θ H i)=1)

open InverseInitialOverlap InverseInitialPoissonBridge CanonicalQuadraticSieve

end SevenEighths.InverseInitialPhysicalMeasure

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialPhysicalMeasure SevenEighths.InverseInitialKernelBridge
open SevenEighths.InverseInitialProfile
namespace SevenEighths.InverseInitialEnergyCallerModes
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def sourcePoint (x : Source (ι:=ι) 0) (N M : Finset ι) : Point ι where
  common := x.common
  divisor := x.divisor
  overlap := x.overlap
  left := N
  right := M
  frequency := x.frequency

def markedModeColumn (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis) (x : Source (ι:=ι) 0)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (Z D B v : ℝ) : ℂ :=
  ∑ J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
    finiteCanonicalMarkedRow p hp hcop hg F Ψ
      (j*quotient p (sourcePoint x ∅ ∅))
      (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
      (primaryGenerator (sourceIdeal p x.divisor)*
        ((unitSector p hp hpr (sourcePoint x ∅ ∅):Eis)^5*h))
      (slots\J) lists a W (Z^(columnCenter D B v))

end SevenEighths.InverseInitialEnergyCallerModes

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open SevenEighths.InverseMoment SevenEighths.InverseInitialProfile
open SevenEighths.InverseInitialArithmetic SevenEighths.InverseInitialPhysicalMeasure
open SevenEighths.InverseInitialEnergyCallerModes
namespace SevenEighths.InverseInitialEnergyCallerSource
variable {ι : Type*} [DecidableEq ι]

def erasePoint (x : Point ι) : Source (ι:=ι) 0 where
  common := x.common
  divisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency
  assigned := Fin.elim0

omit [DecidableEq ι] in
@[simp] theorem erase_sourcePoint (x : Source (ι:=ι) 0) (N M : Finset ι) :
    erasePoint (sourcePoint x N M)=x := by
  apply Source.ext <;> try rfl
  funext i
  exact Fin.elim0 i

def rectangle (F : Finset ι) (x : Source (ι:=ι) 0) : Finset (Point ι) :=
  ((F\x.overlap).powerset ×ˢ (F\x.overlap).powerset).image
    (fun q=>sourcePoint x q.1 q.2)

def pointSource (F : Finset ι) (S : Finset (Source (ι:=ι) 0)) : Finset (Point ι) :=
  S.biUnion (rectangle F)

variable {σ : Type*} [DecidableEq σ]
  (p : ι→ActualEisensteinCubic.O) (hp : ∀ i,p i≠0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def rowMode (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (j : ActualEisensteinCubic.O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (x : Source (ι:=ι) 0) (ρ : SecondRayIndex)
    (z : JointLogSeparation.Frequency × (Fin 6→ℝ)) : ℂ :=
  let height := profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
  (outerCoefficient p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ *
    secondOuterPhase height (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H)) *
  (star (markedModeColumn p hp hcop hg hpr F (secondRayMinus Ψ ρ) j x.frequency x
      slots lists a (childLogTest ω₁ (-height 4)) Z D B v) *
    markedModeColumn p hp hcop hg hpr F (secondRayPlus Ψ ρ) j (-x.frequency) x
      slots lists a (childLogTest ω₂ (height 5)) Z D B v)

end SevenEighths.InverseInitialEnergyCallerSource

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerAllocation
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def modeCoefficient (Ψ:Eis→*ℂ)(j:Eis)(Z D B v θ H:ℝ)
    (x:Source (ι:=ι) 0)(ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) : ℂ :=
  outerCoefficient p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ *
    secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2)
      (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H)

def allocatedMode (u:Eisˣ)(pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)
    (slots J₁ J₂:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (x:Source (ι:=ι) 0)(ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) : ℂ :=
  let height := profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
  modeCoefficient p hp hcop hg Ψ j Z D B v θ H x ρ z *
    (star (primeMark J₁ lists a (x.common∪x.overlap))*primeMark J₂ lists a (x.common∪x.overlap))*
    (star (child p hp hcop hg pool (secondRayMinus Ψ ρ) j (slots\J₁) lists a
      (childLogTest ω₁ (-height 4)) (Z^(columnCenter D B v))
      (initialChild (toTuple p (sectorSource u x))))*
      child p hp hcop hg pool (secondRayPlus Ψ ρ) j (slots\J₂) lists a
      (childLogTest ω₂ (height 5)) (Z^(columnCenter D B v))
      (negativeChild (initialChild (toTuple p (sectorSource u x)))))

end SevenEighths.InverseInitialEnergyCallerAllocation

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerUnits
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation
open InverseInitialQuotientGeometry InverseInitialClippedColumns
local notation "Eis"=>ActualEisensteinCubic.O
local instance initialEnergyUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def sourceSector (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>unitSector p hp hpr (sourcePoint x ∅ ∅)=u)

end SevenEighths.InverseInitialEnergyCallerUnits

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerSourceMask
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialProfile ConcreteTraceCRT
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def coprimeSource (S:Finset (Source (ι:=ι) 0)) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common))

def childLabels (S:Finset (Source (ι:=ι) 0)) : Finset (Ideal Eis) :=
  (coprimeSource p S).image (fun x=>sourceIdeal p x.divisor*sourceIdeal p x.overlap)

end SevenEighths.InverseInitialEnergyCallerSourceMask

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerWindows
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerSourceMask
open InverseInitialProfile InverseInitialClippedColumns InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def sourceRelative (x:Source (ι:=ι) 0)(Z D B v θ H:ℝ) : Fin 6→ℝ :=
  relativeNorm (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H

def windowSource (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)
    (Z D B v θ H:ℝ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>outerCutoff ψ (sourceRelative p x Z D B v θ H)≠0)

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseInitialEnergyCallerWindows

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialPhysicalMeasure
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def sourceKey (x : Point ι) : Fin 5→Finset ι :=
  ![x.common,x.divisor,x.overlap,x.left,x.right]

def sourcePoint (k : Fin 5→Finset ι) (h : O) : Point ι :=
  ⟨k 0,k 1,k 2,k 3,k 4,h⟩

def sourceKeys (S : Finset (Point ι)) : Finset (Fin 5→Finset ι) := S.image sourceKey

def sourceFrequencies (S : Finset (Point ι)) (k : Fin 5→Finset ι) : Finset O :=
  (S.filter (fun x=>sourceKey x=k)).image Point.frequency

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialProfile InverseInitialKernelBridge InverseInitialRayAttachment
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def originalCoefficient (Ψ : O→*ℂ) (j : O) (mark : Finset ι→ℂ)
    (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  (initialBeta p Ψ j x.common * (UniqueFactorizationMonoid.moebius (sourceIdeal p x.divisor):ℂ) *
    supportMobius (fun i=>Ideal.span {p i}) x.overlap * secondRayCoefficient ρ) *
  star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) x.frequency (fun A=>mark (x.common∪A)) (x.overlap∪x.left)) *
  initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) (-x.frequency) (fun A=>mark (x.common∪A)) (x.overlap∪x.right)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialPhysicalReassembly
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def sourceCodes (pool:Finset ι)(T:Finset O):
    Finset (Σ _G:Finset ι,Σ _E:Finset ι,Finset ι×O):=
  pool.powerset.sigma (fun G=>G.powerset.sigma (fun _E=>(pool\G).powerset×ˢT))

def sourceOfCode (x:Σ _G:Finset ι,Σ _E:Finset ι,Finset ι×O):Source (ι:=ι) 0 where
  common:=x.1
  divisor:=x.2.1
  overlap:=x.2.2.1
  frequency:=x.2.2.2
  assigned:=Fin.elim0

def finiteSource (pool:Finset ι)(T:Finset O):Finset (Source (ι:=ι) 0):=
  (sourceCodes pool T).image sourceOfCode

end SevenEighths.InverseInitialPhysicalReassembly

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialPhysicalLimit
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialPhysicalReassembly
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def physicalFrequency (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(h:O):ℂ:=
  ∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
    if Disjoint U T then ∑E∈G.powerset,
      initialPhysicalMode p hp hcop hg Ψ j marks W Φ Z D m G U T E h else 0

end SevenEighths.InverseInitialPhysicalLimit

end

end OAI
end


