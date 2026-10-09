-- Prove2me | Definitions.Def_OAIHecke78B026
-- name    : OAIHecke78B026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T02:23:09.847182+00:00
-- url     : https://prove2.me/theorems/0dbebe0b-979f-4dd5-938a-7bef30004d16
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 27 of 29
-- statement:
--   Definitions bundle 27 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B025` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Reflection.MarkedActiveSets`, `Reflection.ActiveDictionary`, `Reflection.OriginalDictionary`, `Reflection.OriginalChosen`, `Reflection.TupleMembers`, `Reflection.DyadSelection`, `Reflection.DyadReassembly`, `Reflection.DyadCompletionEnergy`, `Reflection.MemberChoiceTransport`, `Reflection.OriginalSlotSupport`, `Reflection.OriginalChoiceControl`, `Reflection.OriginalChoicePhysical`, `Detector.LowRay`, `Detector.LowRayAmplitude`, `Detector.LowSeparated`, `Detector.LowGaussEnergy`, `Detector.LowGramProfile`, `Detector.LowGramFixedCoefficient`, `Detector.GramJointFixed`, `Detector.GramJoint`, `Detector.GramJointMean`, `Detector.GramShell`, `Detector.GramCanonical`, `Detector.GramClassification`, `Detector.GramCanonicalBlock`, `Detector.GramCanonicalSource`, `Detector.GramNonzeroFrequency`, `Detector.LowGramDiagonal`, `Detector.GramCommonEnergy`, `Detector.GramTruncation`, `Detector.LowCompensation`, `Detector.LowSelectedSum`, `Moments.CommonRadialSource`, `Energy.WidthRanges`, `Energy.WidthInduction`, `Energy.CappedWidthInduction`, `Detector.FinalAssemblyCertifiedBands`, `Energy.ChildState`, `Energy.AllocatedClipped`, `Energy.CanonicalLiveBound`, `Moments.FirstAmplifiedPaidAdmission`, `Energy.CanonicalErrorPaid`, `Moments.FirstReferenceSource`, `Energy.NaturalLowSourceBound`, `Energy.ReferenceChildProfiles`, `Energy.ReferenceLowBands`, `Energy.ReferenceSource`, `Energy.PositiveHighSource`, `Energy.PositiveHighSourceBound`, `Energy.PositiveLowBandSource`, `Energy.ZeroBalancedDictionary`, `Energy.ZeroGrowthPhysicalReindex`, `Energy.ZeroGrowthSource`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B026

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Reflection.MarkedActiveSets
  Reflection.ActiveDictionary
  Reflection.OriginalDictionary
  Reflection.OriginalChosen
  Reflection.TupleMembers
  Reflection.DyadSelection
  Reflection.DyadReassembly
  Reflection.DyadCompletionEnergy
  Reflection.MemberChoiceTransport
  Reflection.OriginalSlotSupport
  Reflection.OriginalChoiceControl
  Reflection.OriginalChoicePhysical
  Detector.LowRay
  Detector.LowRayAmplitude
  Detector.LowSeparated
  Detector.LowGaussEnergy
  Detector.LowGramProfile
  Detector.LowGramFixedCoefficient
  Detector.GramJointFixed
  Detector.GramJoint
  Detector.GramJointMean
  Detector.GramShell
  Detector.GramCanonical
  Detector.GramClassification
  Detector.GramCanonicalBlock
  Detector.GramCanonicalSource
  Detector.GramNonzeroFrequency
  Detector.LowGramDiagonal
  Detector.GramCommonEnergy
  Detector.GramTruncation
  Detector.LowCompensation
  Detector.LowSelectedSum
  Moments.CommonRadialSource
  Energy.WidthRanges
  Energy.WidthInduction
  Energy.CappedWidthInduction
  Detector.FinalAssemblyCertifiedBands
  Energy.ChildState
  Energy.AllocatedClipped
  Energy.CanonicalLiveBound
  Moments.FirstAmplifiedPaidAdmission
  Energy.CanonicalErrorPaid
  Moments.FirstReferenceSource
  Energy.NaturalLowSourceBound
  Energy.ReferenceChildProfiles
  Energy.ReferenceLowBands
  Energy.ReferenceSource
  Energy.PositiveHighSource
  Energy.PositiveHighSourceBound
  Energy.PositiveLowBandSource
  Energy.ZeroBalancedDictionary
  Energy.ZeroGrowthPhysicalReindex
  Energy.ZeroGrowthSource
-/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CanonicalRowCompletion
noncomputable section
variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype σ]

def joinedFiberEquiv (e : α⊕β≃γ) : α⊕(β⊕σ)≃γ⊕σ :=
  (Equiv.sumAssoc α β σ).symm.trans (Equiv.sumCongr e (Equiv.refl σ))

def markedActiveSet (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) : Finset (γ⊕σ) :=
  residualActivePrimes (joinedFiberEquiv (σ:=σ) e) ∪
    (B.disjSum T).image (fun x => joinedFiberEquiv e (Sum.inr x))

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CanonicalRowCompletion
noncomputable section
variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype σ]

def disjSumIndexEquiv (B : Finset β) (T : Finset σ) : B⊕T≃B.disjSum T where
  toFun x := match x with
    | Sum.inl b => ⟨Sum.inl b.val,by simp⟩
    | Sum.inr t => ⟨Sum.inr t.val,by simp⟩
  invFun x := match x with
    | ⟨Sum.inl b,hb⟩ => Sum.inl ⟨b,by simpa using hb⟩
    | ⟨Sum.inr t,ht⟩ => Sum.inr ⟨t,by simpa using ht⟩
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨x,hx⟩; cases x <;> rfl

omit [Fintype β] [Fintype σ] in
lemma complete_marked_set (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) :
    completeActiveSet (joinedFiberEquiv e) (B.disjSum T)=markedActiveSet e B T := by
  ext x
  simp only [completeActiveSet,markedActiveSet,Finset.mem_union,Finset.mem_image]

def markedActiveEquiv (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) :
    B⊕(α⊕T)≃markedActiveSet e B T :=
  (((((Equiv.sumAssoc B α T).symm.trans
    (Equiv.sumCongr (Equiv.sumComm B α) (Equiv.refl T))).trans (Equiv.sumAssoc α B T)).trans
    (Equiv.sumCongr (Equiv.refl α) (disjSumIndexEquiv B T))).trans
    (selectedActiveEquiv (joinedFiberEquiv e) (B.disjSum T))).trans
    (Equiv.subtypeEquivRight (fun x => by rw [complete_marked_set e B T]))

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

def poolPrimeFamily (R Q Q₀ : Ideal Eis) : PrimeFamily (FreeReflection.pool R Q Q₀) where
  ideal P := P.val
  maximal P := FreeReflection.pool_maximal R Q Q₀ P
  good P := FreeReflection.pool_good R Q Q₀ P

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

lemma original_active_family_ideal (S : PrimeFamily σ)
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    (((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).restrict
      (markedActiveSet E B T)).ideal (markedActiveEquiv E B T x)=
    (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).ideal x := by
  cases x with
  | inl b =>
    change (E (Sum.inr b.val)).val.val=b.val.val
    exact D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b.val)
  | inr x => cases x with
    | inl a =>
      change (E (Sum.inl a)).val.val=a.val
      exact D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
    | inr t => rfl

lemma original_active_family_generator (S : PrimeFamily σ)
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    (((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).restrict
      (markedActiveSet E B T)).generator (markedActiveEquiv E B T x)=
    (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator x :=
  congrArg primaryPrime (original_active_family_ideal D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T x)

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
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ) (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "PS" => PrimeFamily.restrict (PrimeFamily.sum (freePrimeFamily D.movingIdeal Q₀ D.movingSupported) S) (markedActiveSet E B T)
local notation "PF" => PrimeFamily.reflected (PrimeFamily.restrict (poolPrimeFamily R (Ideal.span (Set.singleton m)*F) Q₀) B) K hK (S.restrict T)
local notation "EA" => markedActiveEquiv E B T

def originalChosenControlled {N a c : Eis} {mode : Bool}
    (C : ControlledStratumArithmetic (PF).generator N a c mode) :
    ControlledStratumArithmetic (PS).generator N a c mode :=
  pullbackControlled EA
    (funext (original_active_family_generator D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T)) C

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
variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable (tuples : Finset (σ→Ideal Eis))
    (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)

def memberTupleFamily (p : tuples) : PrimeFamily σ where
  ideal := p.val
  maximal := hmax p.val p.property
  good := hgood p.val p.property

lemma tuplePrimeFamily_at_member (hne : tuples.Nonempty)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))) (p : tuples) :
    tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val)=memberTupleFamily tuples hmax hgood p := by
  apply PrimeFamily.eq_of_ideal_eq
  exact tuplePrimeFamily_at_product tuples hne hmax hgood hinj p.val p.property

variable {N a c : Eis} {mode : Bool}
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (hne : tuples.Nonempty)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (D : ∀ P : tuples.image slotTupleProduct,IsCoprime K P.val→
      ControlledStratumArithmetic (F.reflected K hK (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode)

def memberTupleControlled (p : tuples) (hp : IsCoprime K (slotTupleProduct p.val)) :
    ControlledStratumArithmetic (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator N a c mode :=
  castControlled (congrArg (fun S => (F.reflected K hK S).generator)
    (tuplePrimeFamily_at_member tuples hmax hgood hne hinj p))
    (D ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp)

def memberTupleRow
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : φ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) : ℂ :=
    ∑ p : tuples,if hp:IsCoprime K (slotTupleProduct p.val) then
      r K*aw p.val*mixedReflectedValue (memberTupleControlled tuples hmax hgood F K hK hne hinj D p hp) s
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_good
        (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X else 0

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
variable {φ σ : Type*} [Fintype φ] [Fintype σ] [DecidableEq σ] {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i) (Hrow Hslot : ℝ)

omit [DecidableEq σ] in
lemma activeTupleDyad_subset (i : Fin (columnDyadicLength Hslot+1)) : activeTupleDyad tuples Hslot i⊆tuples :=
  Finset.filter_subset _ _

lemma divisorDyadicBin_subset (i : Fin (columnDyadicLength Hrow+1)) : divisorDyadicBin rows Hrow i⊆rows :=
  Finset.filter_subset _ _

variable (C : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
    ∀ K : divisorDyadicBin rows Hrow i,∀ p : activeTupleDyad tuples Hslot j,
      IsCoprime K.val (slotTupleProduct p.val)→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
        (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator N a c mode)

def dyadicTupleControlled (K : rows) (p : tuples) (hp : IsCoprime K.val (slotTupleProduct p.val)) :
    ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
      (memberTupleFamily tuples hmax hgood p)).generator N a c mode :=
  C (divisorDyadicLabel Hrow K.val) (divisorDyadicLabel Hslot (slotTupleProduct p.val))
    ⟨K.val,Finset.mem_filter.mpr ⟨K.property,rfl⟩⟩ ⟨p.val,Finset.mem_filter.mpr ⟨p.property,rfl⟩⟩ hp

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

variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i) (Hrow Hslot : ℝ)
variable (C : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
    ∀ K : divisorDyadicBin rows Hrow i,∀ p : activeTupleDyad tuples Hslot j,
      IsCoprime K.val (slotTupleProduct p.val)→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
        (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator N a c mode)
variable (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : φ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ)

def dyadicPhysicalTerm (K : rows) (p : tuples) : ℂ :=
  if hp:IsCoprime K.val (slotTupleProduct p.val) then
    r K.val*aw p.val*mixedReflectedValue
      (dyadicTupleControlled G rows hrows tuples hmax hgood Hrow Hslot C K p hp) s
      (G.reflected K.val (hrows K.val K.property) (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
      (G.reflected K.val (hrows K.val K.property) (memberTupleFamily tuples hmax hgood p)).generator_good
      (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X else 0

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
variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i) (Hrow Hslot : ℝ)

abbrev CellCompletion (i : Fin (columnDyadicLength Hrow+1)) (j : Fin (columnDyadicLength Hslot+1)) :=
    ∀ K : divisorDyadicBin rows Hrow i,∀ p : activeTupleDyad tuples Hslot j,
      IsCoprime K.val (slotTupleProduct p.val)→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
        (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator N a c mode

variable (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : φ→ℕ) (W : ℝ→ℂ) (X : ℝ)

def cellPhysicalTerm (i : Fin (columnDyadicLength Hrow+1)) (j : Fin (columnDyadicLength Hslot+1))
    (D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j)
    (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ)
    (K : divisorDyadicBin rows Hrow i) (p : activeTupleDyad tuples Hslot j) : ℂ :=
    if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*mixedReflectedValue (D K p hp) s
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X else 0

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
variable (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

abbrev originalTupleMax : ∀ p∈fixedSlotTupleSet L F,∀ i,(p i).IsMaximal :=
  fun p hp i => hmax i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i)
abbrev originalTupleGood : ∀ p∈fixedSlotTupleSet L F,∀ i,ConcretePrimeRowBridge.goodLambda∉p i :=
  fun p hp i => hgood i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i)

variable {N a c : Eis} {mode : Bool} (G : PrimeFamily τ) (K : Ideal Eis) (hK : Admissible K)
variable (D : ∀ p : fixedSlotTupleSet L F,IsCoprime K (slotTupleProduct p.val)→
    ControlledStratumArithmetic (G.reflected K hK
      (memberTupleFamily (fixedSlotTupleSet L F) (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator N a c mode)

def memberChoiceControlled (p : supportedSlotChoices L F K) :
    ControlledStratumArithmetic (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator N a c mode :=
  D ((supportedSlotTupleEquiv L F K) p).val ((supportedSlotTupleEquiv L F K) p).property

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
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

abbrev originalSlotChoices :=
  {p : ∀ i,L i // ∀ P : FreePrimeIndex D.movingIdeal Q₀,∀ i,(p i).val≠P.val.val}

def originalSlotSupportEquiv :
    originalSlotChoices D Q₀ L ≃ supportedSlotChoices L ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) where
  toFun p := ⟨p.val,(original_slot_mask_iff D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    (slotChoiceFamily L hmax hgood p.val)).mp p.property⟩
  invFun p := ⟨p.val,(original_slot_mask_iff D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    (slotChoiceFamily L hmax hgood p.val)).mpr p.property⟩
  left_inv _p := rfl
  right_inv _p := rfl

def originalSlotSplit (T : Finset σ) : originalSlotChoices D Q₀ L ≃
    supportedSlotChoices (fun i : {i // i∉T} => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) ×
      supportedSlotChoices (fun i : T => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) :=
  (originalSlotSupportEquiv D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood).trans
    (supportedSlotSplit L T ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)))

lemma originalSlotSplit_symm_val (T : Finset σ)
    (b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)))
    (a : supportedSlotChoices (fun i : T => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F))) :
    ((originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a)).val=
      (slotChoiceSplit L T).symm (a.val,b.val) := rfl

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
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

lemma originalSplit_active_family (T : Finset σ) (p : originalSlotChoices D Q₀ L) :
    (slotChoiceFamily L hmax hgood p.val).restrict T=
      slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val)
        ((originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).2.val) := by
  let e := originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T
  calc
    _ = (slotChoiceFamily L hmax hgood (e.symm (e p)).val).restrict T :=
      congrArg (fun q : originalSlotChoices D Q₀ L => (slotChoiceFamily L hmax hgood q.val).restrict T) (e.symm_apply_apply p).symm
    _ = _ := by
      rw [originalSlotSplit_symm_val,slotChoiceFamily_active]

variable {τ : Type*} [Fintype τ] (Frozen : PrimeFamily τ) {N a c : Eis} {mode : Bool}
variable (T : Finset σ)
    (C : ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ∀ p : supportedSlotChoices (fun i : T => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
        (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator N a c mode)

def originalSplitControlled (p : originalSlotChoices D Q₀ L) :
    ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
      (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
      ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator N a c mode :=
  castControlled (congrArg (fun S => (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
    (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) S).generator)
    (originalSplit_active_family D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).symm)
    (C (originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).1
      (originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).2)

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
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

variable {τ : Type*} [Fintype τ] (Frozen : PrimeFamily τ) {N a c : Eis} {mode : Bool}
variable (T : Finset σ)
    (C : ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ∀ p : supportedSlotChoices (fun i : T => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
        (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator N a c mode)

def originalSplitPhysical
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ)
    (q : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
      ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) ×
      supportedSlotChoices (fun i : T => L i.val)
      ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F))) : ℂ :=
  mixedReflectedValue (C q.1 q.2) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open RayFourExpansion CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev PhysicalRayElement := {s : O // Supported (Ideal.span {s})}

def physicalRay (s : O) : RayRing := Ideal.Quotient.mk (Ideal.span {(4:O)}) s

def physicalRayRepresentative (σ : RayRing) : PhysicalRayElement :=
  if h : ∃s : PhysicalRayElement,physicalRay s.val=σ then Classical.choose h
  else ⟨1,by
    simp [Supported,Ideal.span_singleton_one,←Ideal.one_eq_top]
    change (1:Id)≠0
    exact one_ne_zero⟩

def physicalRayRowMonoid (η : HeckeFamily.Character) (C : CalibrationData)
    (σ : RayRing) (m : O) : O→*ℂ :=
  rowCoefficient η C.Xi (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m

def physicalIdealRay (s : {I : Id // Supported I}) : RayRing := physicalRay (primaryGenerator s.val)

def physicalRayPeriodicBase (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (χ : RayCharacter) : O→*ℂ :=
  lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS) (physicalRayRepresentative σ).val
      (physicalRayRepresentative σ).property χ

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowRayAmplitude (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (σ : RayRing) (m : O) (v : ℝ) : ℂ :=
  ∑'s : {I : Id // Supported I},if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowSeparatedIntegrand (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (B : RayRing→O→ℂ) (v : ℝ) : ℂ :=
  mellin W0 ((v:ℂ)*Complex.I)*
    ∑'m : O,Ω (elementNorm m/lowPhysicalScale C X Y)*C.residueMonoid m*
      ((elementNorm m/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
        ∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ m

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGaussColumn (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) : ℂ :=
  if physicalIdealRay s=σ then
    (Y:ℂ)⁻¹*W1 ((Ideal.absNorm s.val:ℝ)/Y)*lowArithmeticCoefficient C s*
      (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)
  else 0

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramCoefficient (C : CalibrationData) (σ : RayRing)
    (s : {I : Id // Supported I}) : ℂ :=
  if physicalIdealRay s=σ then lowArithmeticCoefficient C s else 0

def lowGramProfile (W1 : ℝ→ℂ) (v r : ℝ) : ℂ :=
  W1 r*(r:ℂ)^(-1+(v:ℂ)*Complex.I)

def lowGramScale (Y : ℝ) : ℂ := (Y:ℂ)⁻¹*(Real.sqrt Y:ℂ)⁻¹

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gramFixedModulus (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : Id :=
  (Ideal.span {(calibrationForSet S hS).generator}*
    calibrationRowModulus (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS))*
      Ideal.span {(4:O)}

def gramCoefficientExtension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) : ℂ :=
  if physicalRay n=σ then (calibrationForSet S hS).tau⁻¹*
    gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS) n
  else 0

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def primaryCoefficient (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) : ℂ :=
  if λ₀^2∣n-1 then gramCoefficientExtension S hS σ n else 0

def jointFixedModulus (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : Id :=
  gramFixedModulus S hS*Ideal.span {λ₀^2}*Ideal.span {(72:O)}

def jointFixed (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ : O) : ℂ :=
  primaryCoefficient S hS σ (C*n₁)*star (primaryCoefficient S hS σ (C*n₂))*
    numeratorBadTwist u a b r hr n₁*star (numeratorBadTwist (-u) a b r hr n₂)*
      sexticReciprocityPhase n₁ n₂

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

def jointExtension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ) (n₁ n₂ : O) : ℂ :=
  jointFixed S hS σ C u a b r hr n₁ n₂*
    (idealRowHom n₁ (Ideal.span {r})*star (idealRowHom n₂ (Ideal.span {r})))*
      globalExtension P hg c n₁ n₂ k

def jointPeriod (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (P : ι→Id) (r : O) : Id :=
  jointFixedModulus S hS*(∏i,P i)*Ideal.span {r}

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge CenteredMomentCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

def jointRemainder (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J : Id) (n₁ n₂ : O) : ℂ :=
  jointFixed S hS σ C u a b r hr n₁ n₂*
    (idealRowHom n₁ J*star (idealRowHom n₂ (Ideal.span {r})))*globalExtension P hg c n₁ n₂ k

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical EisensteinSchwartzPoisson

def shellProfile (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ) : ℂ :=
  lowGramProfile W v x*star (lowGramProfile W v y)*paperRadialFourier U (T/(x*y))

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

abbrev GramFrequency := {k : O // k≠0}
abbrev GramPrime (C : SupportedIdeal) := {P : Id // P∈IdealMobiusDivisorSum.primeSupport C.val}
def gramPrime (C : SupportedIdeal) (P : GramPrime C) : Id := P.val
instance gramPrimeMaximal (C : SupportedIdeal) (P : GramPrime C) : (gramPrime C P).IsMaximal :=
  (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal (support_prime P.property).ne_zero

def gramExponent (C : SupportedIdeal) (P : GramPrime C) : ℕ := (normalizedFactors C.val).count P.val
lemma gramPrime_good (C : SupportedIdeal) (P : GramPrime C) : λ₀∉gramPrime C P :=
  (supported_factors_good C.val C.property P.val (Multiset.mem_toFinset.mp P.property)).2.1
lemma gramPrime_product (C : SupportedIdeal) : C.val=∏P : GramPrime C,gramPrime C P^gramExponent C P := by
  calc
    C.val=(normalizedFactors C.val).prod := (Ideal.prod_normalizedFactors_eq_self C.property.1).symm
    _=∏P∈IdealMobiusDivisorSum.primeSupport C.val,P^(normalizedFactors C.val).count P := Finset.prod_multiset_count _
    _=_ := (Finset.prod_coe_sort _ _).symm

instance gramPrimePowerFinite (C : SupportedIdeal) (P : GramPrime C) :
    Finite (O⧸gramPrime C P^gramExponent C P) :=
  Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ (support_prime P.property).ne_zero)
instance gramPrimePowerFintype (C : SupportedIdeal) (P : GramPrime C) :
    Fintype (O⧸gramPrime C P^gramExponent C P) := Fintype.ofFinite _
instance gramProductFinite (C : SupportedIdeal) : Finite (O⧸∏P : GramPrime C,gramPrime C P^gramExponent C P) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  rw [←gramPrime_product C]
  exact C.property.1
instance gramProductFintype (C : SupportedIdeal) : Fintype (O⧸∏P : GramPrime C,gramPrime C P^gramExponent C P) := Fintype.ofFinite _

structure GramNumeratorData (k : GramFrequency) where
  unit : Oˣ
  lambdaExponent : ℕ
  twoExponent : ℕ
  good : O
  supported : Supported (Ideal.span {good})
  primary : λ₀^2∣good-1
  factor : k.val=unit.val*λ₀^lambdaExponent*(2:O)^twoExponent*good

lemma gramNumeratorData_nonempty (k : GramFrequency) : Nonempty (GramNumeratorData k) := by
  obtain ⟨u,a,b,r,hr,hpr,hf⟩ := exists_supported_numerator_factorization k.val k.property
  exact ⟨⟨u,a,b,r,hr,hpr,hf⟩⟩
def gramNumeratorData (k : GramFrequency) : GramNumeratorData k := Classical.choice (gramNumeratorData_nonempty k)

def canonicalJoint (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (n m : O) : ℂ :=
  let f:=gramNumeratorData k
  jointExtension S hS σ (primaryGenerator C.val) k.val f.unit f.lambdaExponent f.twoExponent
    f.good f.supported (gramPrime C) (gramPrime_good C) (gramExponent C) n m

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def exceptionalModulus (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) : Id :=
  jointFixedModulus S hS*C.val

def ExceptionalFrequency (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) (k : GramFrequency) : Prop :=
  ∀p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C),valuation (Ideal.span {k.val}) p%6=0

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def canonicalLatticeBlock (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (d : O) (W : ℝ→ℂ) (U : SchwartzMap ℝ ℂ)
    (v T N : ℝ) : ℂ :=
  ∑'m : O×O,canonicalJoint S hS σ C k (d*m.1) (d*m.2)*
    shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def originalCommonBlock (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) : ℂ :=
  let N:=commonResidualScale C Y
  let hN:=commonResidualScale_pos C Y hY
  let F:=lowGaussColumns W hW N hN
  (∑I∈F,∑J∈F,if IsCoprime I.val J.val then
      (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
      star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y))*
      actualCorrelation (primaryGenerator (supportedIdealProduct C I).val)
        (primaryGenerator (supportedIdealProduct C J).val)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C I).property)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C J).property)
        (primaryGenerator C.val*k.val)*
      paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator C.val*k.val)‖^2/
        ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2)
      else 0)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def gramFrequencyNeg : GramFrequency≃GramFrequency where
  toFun k:=⟨-k.val,neg_ne_zero.mpr k.property⟩
  invFun k:=⟨-k.val,neg_ne_zero.mpr k.property⟩
  left_inv k:=Subtype.ext (neg_neg k.val)
  right_inv k:=Subtype.ext (neg_neg k.val)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSecondDiagonal EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramZeroMode (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) : ℂ :=
  (Q:ℂ)*paperRadialFourier U 0*
    secondZeroEnergy (lowGaussColumns W1 hW1 Y hY) (fun s=>primaryGenerator s.val)
      (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property) (lowGaussColumn C W1 Y σ v)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT RayFourExpansion
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def originalPairWeight (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (W : ℝ→ℂ) (Y v : ℝ) (I J : SupportedIdeal) : ℂ :=
  (lowGramCoefficient (calibrationForSet S hS) σ I*lowGramProfile W v ((Ideal.absNorm I.val:ℝ)/Y))*
    star (lowGramCoefficient (calibrationForSet S hS) σ J*lowGramProfile W v ((Ideal.absNorm J.val:ℝ)/Y))

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def sourceTruncation (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (E : Finset GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) : ℂ :=
  ((Q/Y^3:ℝ):ℂ)*∑C∈F,∑k∈E,originalCommonBlock S hS σ C k W hW Y Q hY U v

def sourceCanonicalSum (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (E : SupportedIdeal→Finset GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) : ℂ :=
  ((Q/Y^3:ℝ):ℂ)*∑C∈F,∑D∈sourceDivisorUnion F W hW Y hY,sourceMobiusWeight W hW Y hY C D*
    ∑k∈E C,canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
      ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/((Y^2/Q)/gramIdealNorm C)) (Y/(gramIdealNorm C*gramIdealNorm D))

def exceptionalFrequencies (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (E : Finset GramFrequency) (C : SupportedIdeal) : Finset GramFrequency :=
  E.filter (ExceptionalFrequency S hS C)
def nonexceptionalFrequencies (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (E : Finset GramFrequency) (C : SupportedIdeal) : Finset GramFrequency :=
  E.filter (fun k=>¬ExceptionalFrequency S hS C k)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted CanonicalRowCompletion RayFourExpansion ProbeRow CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowMarkedInverseRow (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (D : Id) (T t : ℝ) (σ : RayRing) (m : O) : ℂ :=
  ∑χ : RayCharacter,correctionCoeff χ*
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator 1 m)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
      (fun A=>if D∣A then (1:ℂ) else 0)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowSelectedInverseRow {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (m : O) : ℂ :=
  ∑k∈F,c k*lowMarkedInverseRow η S hS (D k) T t σ m

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonRadialSource
open CenteredMomentCommonRadialData CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform CenteredMomentCommonRawScale
open CenteredMomentRestrictedSource CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors ConcretePrimeRowBridge CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance instDecidableEqSumFinOfNatNat_solutions : DecidableEq (ι⊕Fin 2) := Classical.decEq _

 def sourceEnergy (s:Input ι) (r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O) : ℝ :=
  let Q:=finiteColumns (Fintype.piFinset s.pools)
  let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  sourceRestrictedEnergy r.keep (residualPool C hC.1 Q)
    (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
    (heightCoeff s.η s.t) r.profile r.scale/(s.X₁*s.X₂*∏i,s.P i)

 def commonCost (s:Input ι) (C:Ideal O) : ℝ :=
  ((actualAllocations s.pools C).card:ℝ)*
    (((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)/(Ideal.absNorm C:ℝ))

end SevenEighths.CenteredMomentCommonRadialSource

end

end OAI
end

section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyProfiles CenteredMomentEnergyWidthSchedule

def step (M B L:ℝ):ℝ:=4*(L+M+B+4)
def range (M B L:ℝ):ℕ→ℝ
  | 0=>max 1 L
  | n+1=>step M B (range M B L n)
def sourceCap (M B L:ℝ)(n:ℕ):ℝ:=10*(range M B L n+M+B+1)
def finalSourceCap (M B L ε:ℝ):ℝ:=sourceCap M B L (count M ε)
def fineMesh (M B L κ ε:ℝ):ℝ:=mesh M (finalSourceCap M B L ε) κ ε

end SevenEighths.CenteredMomentEnergyWidthRanges

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyWidthInduction
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O

def remaining (M ε:ℝ)(k:ℕ):ℕ:=count M ε-k
def lowerAt (a b M ε:ℝ)(k:ℕ):ℝ:=CenteredMomentEnergyProfiles.lower a b (remaining M ε k)
def lengthAt (M B L ε:ℝ)(k:ℕ):ℝ:=range M B L (remaining M ε k)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

local instance instFiniteQuotientOIdeal_solutions_r44b9c8_1 : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
def CertifiedBand (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)(k:ℕ):Prop:=
  ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
    internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k)
        (width Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z degree S Czero ∧
      PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k) (fineMesh Mcap Bmask L κ ε) lo hi
        (width Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q degree S Cpositive

end SevenEighths.CenteredMomentEnergyWidthInduction

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedWidthInduction
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt )

def bandWidth (M B ε:ℝ)(k:ℕ):ℝ:=min M (width M B ε k)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

local instance instFiniteQuotientOIdeal_solutions_r44b9c8_2 : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
def CertifiedBand (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)(k:ℕ):Prop:=
  ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
    internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k)
        (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z degree S Czero ∧
      PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k) (fineMesh Mcap Bmask L κ ε) lo hi
        (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q degree S Cpositive

end SevenEighths.CenteredMomentEnergyCappedWidthInduction

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.ProbeFinalAssemblyCertifiedBands
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open ProbeFinalAssembly ProbeHighRowFamily Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthSchedule CenteredMomentDetectorPlainMomentParameters
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O

def detectorMesh (Δ t:ℝ):ℝ:=fineMesh 2 0 1 (3/4+2*Δ) (t/4)

def DetectorCertifiedBands:Prop:=
  ∀_hβ:(7/8:ℝ)<HeckeZeroSupremum.beta,
  ∀D:HighData (HeckeZeroSupremum.beta-7/8),
    (∀j,D.ell j≤detectorMesh (HeckeZeroSupremum.beta-7/8) D.t/200)→
  ∀F:SourceData D,∀bΦ:ℝ,0<bΦ→
    CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (kappaPlain D) (stageError D)
      (count 2 (stageError D))

end SevenEighths.ProbeFinalAssemblyCertifiedBands

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyChildState
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentEnergyState CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondDyadicRowSupport CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O

lemma ball_support : Function.support (ballProfile:ℝ→ℂ)⊆Set.Iic (2:ℝ):=by
  intro x hx
  by_cases h:0≤x
  · exact (CenteredMomentAmplifiedRetainedRadius.ballProfile_support_upper x h hx).le
  · exact (lt_of_not_ge h).le.trans (by norm_num)

lemma canonical_mask_nonexceptional (τ:Character)(Q R:Ideal O)(hR:R≠0)
    (n:Fin 4→ℤ)(z:O)(hz:(canonicalRadial τ Q n).keep z):
    ¬CenteredExceptionalProfile.FixedInducingRow τ Q
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z:=by
  intro hh
  exact hz.2 ((CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff τ Q
    fixedBadMask (ConcretePrimeRowBridge.idealGenerator R) 1 z fixedBadMask_ne_zero
    (ConcretePrimeRowBridge.idealGenerator_ne_zero R hR) one_ne_zero hz.1
    (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hh)

def canonicalState (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)
    (hn:1≤dyadicScale (n 1)):NaturalState Z Bmask 2 where
  character:=τ
  fixedModulus:=Q
  puncture:=R
  radial:=canonicalRadial τ Q n
  rowWidth:=Real.logb Z (dyadicScale (n 1))
  characterWidth:=Real.logb Z (τ.modulus.absNorm:ℝ)
  base_ge_one:=hZ.le
  row_nonneg:=Real.logb_nonneg hZ hn
  character_nonneg:=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))
  scale_eq:=(Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos _)).symm
  modulus_bound:=by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (show 0<(τ.modulus.absNorm:ℝ) by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))]
  puncture_ne_zero:=hR
  puncture_bound:=hRN
  radial_support:=ball_support
  row_ne_zero:=fun _ hz=>hz.1
  nonexceptional:=canonical_mask_nonexceptional τ Q R hR n

end SevenEighths.CenteredMomentEnergyChildState

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyAllocatedClipped
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

def pair (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    {a b:ℝ}(ha:0<a)(p:Profiles a b)(v X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    Profiles (a/max 1 b) b :=
  retainedPair a b ha p ![rawScale D alloc X₁ 0,rawScale D alloc X₂ 1]
    (by intro i;fin_cases i;exact rawScale_pos D alloc X₁ hX₁ 0;exact rawScale_pos D alloc X₂ hX₂ 1) v

def scale (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (X:ℝ)(j:Fin 2)(F:Finset (Ideal O)):ℝ:=
  clippedScale (rawScale D alloc X j)/((∏I∈F,I).absNorm:ℝ)

variable (M:Ideal O)[NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyAllocatedClipped

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalLiveBound
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

def LiveChild (η:Character)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α):Prop:=
  ∃z:O,r.keep z ∧ (r.profile (‖eisEmbedding z‖^2/r.scale)).re≠0 ∧
    child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J≠0

open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyCanonicalLiveBound

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceLiveColumn
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedChildCapacity

local instance instDecidableEq_solutions_r44b9c8_1 {κ:Type*}:DecidableEq κ:=Classical.decEq _
def sourceReserve {α:Type*}[Fintype α] (s:Input ι)(childInput:Input α)
    (C D:Ideal O)(Z delta reserve cost a:ℝ):ℝ :=
  max (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
    min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
    Real.logb Z fixedPresentationCost-Real.logb Z cost+
    Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
    (Fintype.card α:ℝ)*Real.logb Z (max 1 childInput.upper)) 0

end SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorPaid
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][instα:DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentEnergyCanonicalMainPaid CenteredMomentEnergyCanonicalNestedReference
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open CenteredMomentEnergyActiveChildRestoration

def castAllocation (s t:Input α)(h:s=t)(C:Ideal O)
    (B:actualAllocations s.pools C):actualAllocations t.pools C:=
  ⟨B.val,by rw [←h];exact B.property⟩

def castDivisorAllocation (s t:Input α)(h:s=t)(C:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))):
    Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices (castAllocation s t h C B).val⊕Fin 2)):=alloc

def restoreDivisorAllocation (s:Input α)(C:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))):
    Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices (restoreAllocation s C B).val⊕Fin 2)):=alloc

end SevenEighths.CenteredMomentEnergyCanonicalErrorPaid

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstReferenceSource
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstRetainedNorm
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstSourceReduction
open CenteredMomentFirstInactiveRadicalMass CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondRetainedAggregate CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentExceptionalAmplitudePair CenteredMomentRankinRadical
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance instDecidableEqSumFinOfNatNat_solutions : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev SourceBlocks (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):=
  Blocks (effectiveScale p.val.1 p.val.2 E K) (localRadius s R seed K Z ξ p E)
    (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)

def originalBlock (s:Input ι)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):ℂ:=
  block s.η (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    p.val.1 p.val.2
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).1
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).2 E
    (retainedRows (localRadius s R seed K Z ξ p E) 1) W (fun _=>logAnnulus)
    K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))

def radicalWeight (s:Input ι)(R seed:Ideal O)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
    ((commonRadical p.val.1 p.val.2).absNorm:ℝ)

end SevenEighths.CenteredMomentFirstReferenceSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalLowSourceBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroComparison
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentAmplificationChildInput CenteredMomentInductionEnergy
open CenteredMomentEnergyBands CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource HeckeDyadic HeckePrimeAnnular
local notation "O" => HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

section Source
variable (Q:Ideal O)[NeZero Q]
variable (H:Subgroup (O⧸Q)ˣ)(hH:RayOrthogonality.globalUnits Q≤H)
variable (η₀:Character)(θ:ι→RayQuotient.Characters Q H)
variable (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:ι→ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(state:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

local instance instDecidableEqSumFinOfNatNat_solutions_r44b9c8_1 : DecidableEq (ι⊕Fin 2):=
  CenteredMomentEnergyOriginalSource.energyOriginalSourceDecidableSum
def sourceInput : Input ι :=
  input Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
    state p ha t X₁ X₂ X₁ X₂ hX₁ hX₂ hX₁ hX₂ rfl

def zeroSourceInput : Input ι :=
  zeroInput (sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂)
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 0))
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 1))
end Source

end SevenEighths.CenteredMomentEnergyNaturalLowSourceBound

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceChildProfiles
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyProfiles
open CenteredMomentAllocatedNaturalRadial CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentFiniteProfileExceptional
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentLattice CenteredMomentRetainedProfile
local notation "O"=>HeckeFamily.O

def reflectionProfiles {a b:ℝ}(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v t:ℝ):Profiles a b:=
  independentProfiles ha (derivativeChoice (annulusSeed a b hlo hhi).profile j)
    (derivativeChoice W k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hs k) (-2*Real.pi*v) t

end SevenEighths.CenteredMomentEnergyReferenceChildProfiles

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

def ZeroLowAt (Q:Ideal O)(a b bΦ Bmask L M ε Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂≤5*s.width/6→
    s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
      (1+‖t‖)^degree*Z^(s.width+ε)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def PositiveLowAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
    0≤height→(∀i,|v i|≤height)→
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀→s.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
    length Z X₁+length Z X₂+(∑i,w i)≤5*s.width/6→
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε)

end SevenEighths.CenteredMomentEnergyReferenceLowBands

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceSource
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

def signedCommonSource {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(z:O):ℂ:=
  let χ:=naturalCharacter s.character z
  let R:=CompletedGauss.primeSupport s.puncture
  ∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈(Finset.univ:Finset α).powerset,
    signedCoefficient χ R D₁ D₂ J pool (fun i=>heightCoefficient (β i) t) P *
      (polynomial χ false W₁ (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
       polynomial χ false W₂ (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
       ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i))

end SevenEighths.CenteredMomentEnergyReferenceSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSource
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance instDecidableEqSumFinOfNatNat_solutions_r44b9c8_2 : DecidableEq (α⊕Fin 2):=Classical.decEq _
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

def balancedInput:Input α:=
  CenteredMomentEnergyNaturalInputMatches.input M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
    hX₁ hX₂
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

local notation "balancedSource"=>balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

end SevenEighths.CenteredMomentEnergyPositiveHighSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSourceBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance instDecidableEqSumFinOfNatNat_solutions_r44b9c8_3 {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyPositiveHighSource (balancedInput)
open CenteredMomentEnergyPositiveHighBound CenteredMomentEnergyBandMonotonicity
def PhysicalHighAt (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (a b bΦ Bmask L Lslot rho Mcap κ ξ e Z:ℝ)(ha:0<a)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(η₀:Character)(Q:Ideal O)
    (S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ freq:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→∀hσlo:∀i,lo≤σ i,∀hσhi:∀i,σ i≤hi,
    0≤height→(∀i,|freq i|≤height)→
  ∀state:NaturalState Z Bmask bΦ,state.fixedModulus=internalQ Q η₀→ rho≤ state.width→state.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ state.width→
    5*state.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
    let inp:=balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂;
    (Z^(state.width/4)≤ inp.X₁ ∧ Z^(state.width/4)≤ inp.X₂ ∧
      Z^(state.width/4)≤ inp.Y₁ ∧ Z^(state.width/4)≤ inp.Y₂)→
    physicalMass inp state.puncture 1 fixedBadMask 1 (Ψ T) state.radial.scale Z ξ/volume inp≤
      C*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e)

def PositiveHighAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi rho Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
    0≤height→(∀i,|v i|≤height)→
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀→ rho≤ s.width→s.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
    5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε)

end SevenEighths.CenteredMomentEnergyPositiveHighSourceBound

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveLowBandSource
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance instDecidableEqSumFinOfNatNat_solutions_r44b9c8_4 {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def PhysicalLowAt (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (a b bΦ Bmask L Lslot rho Mcap κ ξ e Z:ℝ)(ha:0<a)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(η₀:Character)(Q:Ideal O)
    (S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ freq:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→∀hσlo:∀i,lo≤σ i,∀hσhi:∀i,σ i≤hi,
    0≤height→(∀i,|freq i|≤height)→
  ∀state:NaturalState Z Bmask bΦ,state.fixedModulus=internalQ Q η₀→ rho≤ state.width→state.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ state.width→
    length Z X₁+length Z X₂+(∑i,w i)≤5*state.width/6→
    physicalMass (zeroSourceInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂)
      state.puncture 1 fixedBadMask 1 (Ψ T) state.radial.scale Z ξ /
      volume (sourceInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂)≤
      C*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e)

end SevenEighths.CenteredMomentEnergyPositiveLowBandSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroBalancedDictionary
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyNaturalInputMatches
open CenteredMomentAmplificationChildInput CenteredMomentFirstSourceReduction
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
local notation "zeroInput"=>CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂

variable (η₀:Character)(θ:Fin 0→RayQuotient.Characters M H)(w σ freq:Fin 0→ℝ)
def positiveEmptyInput : Input (Fin 0):=
  CenteredMomentEnergyPositiveHighSource.balancedInput M H hH η₀ θ
  (fun _=>0) continuous_const 1 1 0 0 (by norm_num)
  (by simp [Function.support]) w σ freq (fun i=>Fin.elim0 i)
  s p ha t X₁ X₂ hX₁ hX₂

local notation "positiveInput"=>positiveEmptyInput M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq

end SevenEighths.CenteredMomentEnergyZeroBalancedDictionary

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalReindex
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentSourceInputReindex
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstSourceReduction
open CenteredMomentFirstRetainedNorm CenteredMomentAmplificationChildInput
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α β:Type*}[Fintype α][Fintype β]
local instance instDecidableEq_solutions_r44b9c8_2 {κ:Type*}:DecidableEq κ:=Classical.decEq _
local instance instDecidableEqSumFinOfNatNat_solutions_r44b9c8_5 : DecidableEq (α⊕Fin 2):=Classical.decEq _
local instance instDecidableEqSumFinOfNatNat_solutions_1 : DecidableEq (β⊕Fin 2):=Classical.decEq _

def emptyEquiv (α:Type*)[Fintype α]:Fin 0≃(∅:Finset α):=Equiv.equivOfIsEmpty _ _

variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

def emptyBalanced (α:Type*)[Fintype α]:Input (∅:Finset α):=
  reindex (emptyEquiv α)
    (CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂)

end SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalReindex

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthSource
open HeckeFamily QuadraticInitialBound CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentFirstSourceReduction CenteredMomentEnergyBandMonotonicity
open CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O

local instance instDecidableEqSumFinOfNatNat_solutions_r44b9c8_6 : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _
def PhysicalGrowthAt (Q:Ideal O)(a b bΦ Bmask L rho Mcap ξ e Z:ℝ)(ha:0<a)
    (Ψ:𝓢(ℝ,ℂ))(S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→ rho≤ s.width→s.width≤Mcap→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→5*s.width/6≤length Z X₁+length Z X₂→
    let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
    (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
      Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂)→
    physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)≤
      C*(p.control S)^2*(1+|t|)^J*Z^(max s.width (length Z X₁+length Z X₂)+e)

end SevenEighths.CenteredMomentEnergyZeroGrowthSource

end

end OAI
end


