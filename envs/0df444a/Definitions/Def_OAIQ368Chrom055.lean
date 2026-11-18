-- Prove2me | Definitions.Def_OAIQ368Chrom055
-- name    : OAIQ368Chrom055
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T20:08:38.323209+00:00
-- url     : https://prove2.me/theorems/de9a9909-8ebd-453a-8b26-fe4eb4dfb899
-- title:
--   Definitions bundle OAIQ368Chrom055 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 39 definitions and 25 theorems. The definitions and types are `OAI.ElementaryPositivity.EnergyLaurent.finiteSupportCutoff`, `OAI.ElementaryPositivity.EnergyLaurent.supportRestrictedSeries`, `OAI.ElementaryPositivity.SignedMultiplicity.countSumDimensionEquiv`, `OAI.ElementaryPositivity.SignedMultiplicity.countSupportEquiv`, `OAI.ElementaryPositivity.SignedMultiplicity.dimensionReindex`, `OAI.ElementaryPositivity.SignedMultiplicity.dimensionSupportEquiv`, `OAI.ElementaryPositivity.SignedMultiplicity.embedCount`, `OAI.ElementaryPositivity.SignedMultiplicity.restrictCount`, `OAI.ElementaryPositivity.UnitSelections.Strict`, `OAI.ElementaryPositivity.UnitSelections.Weak`, `OAI.ElementaryPositivity.UnitSelections.deleteZeroEquiv`, `OAI.ElementaryPositivity.UnitSelections.finiteStartEquiv`, `OAI.ElementaryPositivity.UnitSelections.finiteStartSeries`, `OAI.ElementaryPositivity.UnitSelections.finiteStringProducts`, `OAI.ElementaryPositivity.UnitSelections.indexedUnitSeries`, `OAI.ElementaryPositivity.UnitSelections.noneEmbedding`, `OAI.ElementaryPositivity.UnitSelections.oneStringDimensionEquiv`, `OAI.ElementaryPositivity.UnitSelections.oneStringEquiv`, `OAI.ElementaryPositivity.UnitSelections.prependZero`, `OAI.ElementaryPositivity.UnitSelections.shiftOne`, `OAI.ElementaryPositivity.UnitSelections.someEmbedding`, `OAI.ElementaryPositivity.UnitSelections.staircaseEquiv`, `OAI.ElementaryPositivity.UnitSelections.startEmbedding`, `OAI.ElementaryPositivity.UnitSelections.startSupport`, `OAI.ElementaryPositivity.UnitSelections.strictEnergy`, `OAI.ElementaryPositivity.UnitSelections.strictSeries`, `OAI.ElementaryPositivity.UnitSelections.strictUnitEquiv`, `OAI.ElementaryPositivity.UnitSelections.stringLiteralUnit`, `OAI.ElementaryPositivity.UnitSelections.stringReindex`, `OAI.ElementaryPositivity.UnitSelections.stringSumCounts`, `OAI.ElementaryPositivity.UnitSelections.stringSumEven`, `OAI.ElementaryPositivity.UnitSelections.stringWallDatum`, `OAI.ElementaryPositivity.UnitSelections.subtractOneEquiv`, `OAI.ElementaryPositivity.UnitSelections.unitSigmaFibre`, `OAI.ElementaryPositivity.UnitSelections.weakEnergy`, `OAI.ElementaryPositivity.UnitSelections.weakSeries`, `OAI.ElementaryPositivity.UnitSelections.weakSplit`, `OAI.ElementaryPositivity.UnitSelections.weakUnitEquivSame`, `OAI.ElementaryPositivity.WeightedTorusSeries.instAddCommMonoidTorusLaurentSeriesRat`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_CompleteUnit`, `Chromatic_GradedAlgebra_EnergyLaurentFinite`, `Chromatic_GradedAlgebra_EnergyLaurentSeries`, `Chromatic_GradedAlgebra_EnergyLimit`, `Chromatic_GradedAlgebra_UnitSelectionLaurent`, `Chromatic_QuantumTorus_IndexedUnit`, `Chromatic_QuantumTorus_StringLiteralClosure`, `Chromatic_QuantumTorus_StringSumProduct`, `Chromatic_QuantumTorus_StringSumPush`, `Chromatic_QuantumTorus_WeakStrictUnitSelections`, `Chromatic_QuantumTorus_WeakUnitRecursion`, `Chromatic_Walls_CountEmbedding`, `Chromatic_Walls_CountSumDimension`, `Chromatic_Walls_StringRay`, `Chromatic_Walls_StringRootClosure`, `Chromatic_Walls_WeightedCompletion`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom054` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.ElementaryPositivity.RawShuffle.finiteInput_zero_rootClosure` and `OAI.ElementaryPositivity.RawShuffle.literalInput_primitiveFactor`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom054

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_EnergyLaurentSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.SlopeArithmetic.instFiniteHNComposition _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.EnergyLaurent
open scoped LaurentSeries
noncomputable section
variable {A B : Type*}

lemma admissible_sum {e : A → ℤ} {f : B → ℤ} (he : Admissible e) (hf : Admissible f) :
    Admissible (Sum.elim e f) := by
  constructor
  · obtain ⟨K,hK⟩:=he.1
    obtain ⟨L,hL⟩:=hf.1
    refine ⟨max K L,?_⟩
    rintro (a|b)
    · exact (hK a).trans (le_max_left _ _)
    · exact (hL b).trans (le_max_right _ _)
  · intro E
    let : Finite {a // e a=E}:=he.2 E
    let : Finite {b // f b=E}:=hf.2 E
    let q : {x // Sum.elim e f x=E} ≃ ({a // e a=E} ⊕ {b // f b=E}) := Equiv.subtypeSum
    exact Finite.of_equiv _ q.symm

end
end ElementaryPositivity.EnergyLaurent
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_WeakStrictUnitSelections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
noncomputable section
abbrev Weak (n : ℕ) := {f : Fin n → ℕ // Monotone f}
abbrev Strict (n : ℕ) := {f : Fin n → ℕ // StrictMono f}

lemma strict_index_le {n : ℕ} (g : Strict n) (i : Fin n) : i.val≤g.val i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have h:=g.property (Fin.castSucc_lt_succ (i:=i))
      change i.val≤g.val i.castSucc at ih
      change i.val+1≤g.val i.succ
      omega

def staircaseEquiv (n : ℕ) : Weak n ≃ Strict n where
  toFun f:=⟨fun i=>f.val i+i.val,by
    intro i j hij
    have h:=f.property hij.le
    have hi : i.val<j.val:=hij
    dsimp only
    omega⟩
  invFun g:=⟨fun i=>g.val i-i.val,by
    cases n with
    | zero => intro i; exact Fin.elim0 i
    | succ n =>
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      have h:=g.property (Fin.castSucc_lt_succ (i:=i))
      have hb:=strict_index_le g i.castSucc
      change g.val i.castSucc-i.val≤g.val i.succ-(i.val+1)
      omega⟩
  left_inv f:=by ext i; simp
  right_inv g:=by
    apply Subtype.ext
    funext i
    change g.val i-i.val+i.val=g.val i
    exact Nat.sub_add_cancel (strict_index_le g i)

end
end ElementaryPositivity.UnitSelections
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_WeakUnitRecursion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
noncomputable section

def prependZero (n : ℕ) (f : Weak n) : Weak (n+1) :=
  ⟨Fin.cons 0 f.val,by
    intro i j
    refine Fin.cases (fun _=>Nat.zero_le _) (fun i=>?_) i
    refine Fin.cases ?_ (fun j hij=>f.property (Fin.succ_le_succ_iff.mp hij)) j
    intro hij
    simp at hij⟩

def deleteZeroEquiv (n : ℕ) : {f : Weak (n+1) // f.val 0=0} ≃ Weak n where
  toFun f:=⟨fun i=>f.val.val i.succ,fun _ _ h=>f.val.property (Fin.succ_le_succ_iff.mpr h)⟩
  invFun f:=⟨prependZero n f,rfl⟩
  left_inv f:=by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun i=>rfl) i
    exact f.property.symm
  right_inv f:=rfl

lemma weak_first_le (n : ℕ) (f : Weak (n+1)) (i : Fin (n+1)) : f.val 0≤f.val i :=
  f.property (Fin.zero_le i)

def shiftOne (n : ℕ) (f : Weak n) : Weak n :=
  ⟨fun i=>f.val i+1,fun _ _ h=>Nat.add_le_add_right (f.property h) 1⟩

def subtractOneEquiv (n : ℕ) : {f : Weak (n+1) // f.val 0≠0} ≃ Weak (n+1) where
  toFun f:=⟨fun i=>f.val.val i-1,fun _ _ h=>Nat.sub_le_sub_right (f.val.property h) 1⟩
  invFun f:=⟨shiftOne (n+1) f,by simp [shiftOne]⟩
  left_inv f:=by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change f.val.val i-1+1=f.val.val i
    have h:=weak_first_le n f.val i
    have h0:=f.property
    omega
  right_inv f:=by
    apply Subtype.ext
    funext i
    change f.val i+1-1=f.val i
    omega

def weakSplit (n : ℕ) : Weak (n+1) ≃ Weak n ⊕ Weak (n+1) :=
  (Equiv.sumCompl (fun f : Weak (n+1)=>f.val 0=0)).symm.trans
    (Equiv.sumCongr (deleteZeroEquiv n) (subtractOneEquiv n))

end
end ElementaryPositivity.UnitSelections
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_UnitSelectionLaurent
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing _root_.OAI.ElementaryPositivity.SlopeArithmetic.instFiniteHNComposition _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFinite _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open EnergyLaurent
open scoped LaurentSeries
noncomputable section

def weakEnergy (n : ℕ) (k : ℤ) (f : Weak n) : ℤ := (n:ℤ)*k-2*weight f.val

lemma weakAdmissible (n : ℕ) (k : ℤ) : Admissible (weakEnergy n k) := by
  constructor
  · refine ⟨n*k,?_⟩
    intro f
    have hh : 0≤weight f.val:=Finset.sum_nonneg (fun i _=>Int.natCast_nonneg _)
    unfold weakEnergy
    linarith
  · intro E
    let U:=((n:ℤ)*k-E).toNat
    let F : {f : Weak n // weakEnergy n k f=E} → (Fin n → Fin (U+1)) := fun f i=>
      ⟨f.val.val i,by
        have hi : (f.val.val i:ℤ)≤weight f.val.val :=
          Finset.single_le_sum (fun j _=>Int.natCast_nonneg (f.val.val j)) (Finset.mem_univ i)
        have hn : 0≤weight f.val.val :=
          Finset.sum_nonneg (fun j _=>Int.natCast_nonneg (f.val.val j))
        have he:=f.property
        unfold weakEnergy at he
        dsimp only [U]
        omega⟩
    apply Finite.of_injective F
    intro f g h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i)

def weakSeries (n : ℕ) (k : ℤ) : LaurentSeries ℚ := series (weakEnergy n k) (weakAdmissible n k)

end
end ElementaryPositivity.UnitSelections
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_CompleteUnit
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open EnergyLaurent WallUnits PowerSeries
open scoped LaurentSeries
noncomputable section

def strictEnergy (n : ℕ) (k : ℤ) (f : Strict n) : ℤ := (n:ℤ)*k-2*weight f.val

lemma strictAdmissible (n : ℕ) (k : ℤ) : Admissible (strictEnergy n k) := by
  constructor
  · refine ⟨n*k,?_⟩
    intro f
    have hh : 0≤weight f.val:=Finset.sum_nonneg (fun i _=>Int.natCast_nonneg _)
    unfold strictEnergy
    linarith
  · intro E
    let : Finite {f : Weak n // weakEnergy n k f=E}:=(weakAdmissible n k).2 E
    let F : {f : Strict n // strictEnergy n k f=E} → {f : Weak n // weakEnergy n k f=E} := fun f=>
      ⟨⟨f.val.val,f.val.property.monotone⟩,f.property⟩
    exact Finite.of_injective F (fun f g h=>Subtype.ext (Subtype.ext
      (congrArg (fun z : {f : Weak n // weakEnergy n k f=E}=>z.val.val) h)))

def strictSeries (n : ℕ) (k : ℤ) : LaurentSeries ℚ := series (strictEnergy n k) (strictAdmissible n k)

end
end ElementaryPositivity.UnitSelections
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_EnergyLaurentFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.EnergyLaurent
noncomputable section
variable {A : Type*} {e : A → ℤ}

lemma admissible_subtype (he : Admissible e) (p : A → Prop) :
    Admissible (fun x : {a // p a}=>e x.val) := by
  refine ⟨?_,?_⟩
  · obtain ⟨K,hK⟩:=he.1
    exact ⟨K,fun x=>hK x.val⟩
  · intro E
    let := he.2 E
    exact Finite.of_injective (fun x : {x : {a // p a} // e x.val=E}=>
      (⟨x.val.val,x.property⟩ : {a // e a=E}))
      (fun x y H=>Subtype.ext (Subtype.ext (congrArg (fun z : {a // e a=E}=>z.val) H)))

end
end ElementaryPositivity.EnergyLaurent

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CountEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SignedMultiplicity
noncomputable section
variable {A B : Type*} (e : A ↪ B) (even : B → Prop)

def embedCount (f : CountSelection (fun a=>even (e a))) : CountSelection even :=
  ⟨f.val.embDomain e,by
    intro b hb
    by_cases H : b∈Set.range e
    · obtain ⟨a,rfl⟩:=H
      rw [Finsupp.embDomain_apply_self]
      exact f.property a hb
    · rw [Finsupp.embDomain_of_notMem_range _ _ _ H]
      exact Nat.zero_le _⟩

lemma embedCount_support (f : CountSelection (fun a=>even (e a))) :
    ↑(embedCount e even f).val.support ⊆ Set.range e := by
  intro b hb
  by_contra H
  exact Finsupp.mem_support_iff.mp hb (Finsupp.embDomain_of_notMem_range _ _ _ H)

lemma embedCount_sum {T : Type*} [AddCommMonoid T] (f : CountSelection (fun a=>even (e a)))
    (k : B → T) :
    (embedCount e even f).val.sum (fun b n=>n • k b)=f.val.sum (fun a n=>n • k (e a)) := by
  exact Finsupp.sum_embDomain

def restrictCount (f : CountSelection even) : CountSelection (fun a=>even (e a)) :=
  ⟨f.val.comapDomain e e.injective.injOn,fun a ha=>f.property (e a) ha⟩

def countSupportEquiv : CountSelection (fun a=>even (e a)) ≃
    {f : CountSelection even // ↑f.val.support ⊆ Set.range e} where
  toFun f:=⟨embedCount e even f,embedCount_support e even f⟩
  invFun f:=restrictCount e even f.val
  left_inv f:=by
    apply Subtype.ext
    exact Finsupp.comapDomain_embDomain e f.val
  right_inv f:=by
    apply Subtype.ext
    apply Subtype.ext
    exact Finsupp.embDomain_comapDomain f.property

variable {I : Type*} (dim : B → (I→ℕ))

def dimensionSupportEquiv (d : I→ℕ) :
    DimensionCounts (fun a=>even (e a)) (fun a=>dim (e a)) d ≃
      {f : DimensionCounts even dim d // ↑f.val.val.support ⊆ Set.range e} where
  toFun f:=⟨⟨embedCount e even f.val,by
    change (embedCount e even f.val).val.sum _=d
    rw [embedCount_sum]
    exact f.property⟩,embedCount_support e even f.val⟩
  invFun f:=⟨restrictCount e even f.val.val,by
    have H:=embedCount_sum e even (restrictCount e even f.val.val) dim
    have HE : embedCount e even (restrictCount e even f.val.val)=f.val.val :=
      Subtype.ext (Finsupp.embDomain_comapDomain f.property)
    rw [HE] at H
    exact H.symm.trans f.val.property⟩
  left_inv f:=by
    apply Subtype.ext
    exact (countSupportEquiv e even).symm_apply_apply f.val
  right_inv f:=by
    apply Subtype.ext
    apply Subtype.ext
    exact Subtype.ext (Finsupp.embDomain_comapDomain f.property)

lemma dimensionSupport_energy (k : B → ℤ) (d : I→ℕ)
    (f : DimensionCounts (fun a=>even (e a)) (fun a=>dim (e a)) d) :
    countEnergy even k (dimensionSupportEquiv e even dim d f).val.val=
      countEnergy (fun a=>even (e a)) (fun a=>k (e a)) f.val :=
  embedCount_sum e even f.val k
end
end ElementaryPositivity.SignedMultiplicity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CountSumDimension
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SignedMultiplicity
open RawShuffle EnergyLaurent
noncomputable section
variable {A B I : Type*} [Fintype I] [DecidableEq I]
variable (ea : A → Prop) (eb : B → Prop) (da : A → (I→ℕ)) (db : B → (I→ℕ))
variable (ka : A → ℤ) (kb : B → ℤ)

def countSumDimensionEquiv (d : I→ℕ) :
    DimensionCounts (Sum.elim ea eb) (Sum.elim da db) d ≃
      Σs : DimensionSplit d,DimensionCounts ea da s.left × DimensionCounts eb db s.right :=
  ((countSumEquiv ea eb).subtypeEquiv (fun x=>by
    change countDimension _ _ x=d ↔ _
    rw [countDimension,countSum_sum]
    rfl)).trans (dimensionProduct (countDimension ea da) (countDimension eb db) d).symm

omit [Fintype I] [DecidableEq I] in
lemma countSumDimension_energy (d : I→ℕ)
    (f : DimensionCounts (Sum.elim ea eb) (Sum.elim da db) d) :
    countEnergy (Sum.elim ea eb) (Sum.elim ka kb) f.val=
      countEnergy ea ka (countSumDimensionEquiv ea eb da db d f).2.1.val+
      countEnergy eb kb (countSumDimensionEquiv ea eb da db d f).2.2.val :=
  countSum_sum ea eb f.val (Sum.elim ka kb)

variable (ha : ∀d,Admissible (fun f : DimensionCounts ea da d=>countEnergy ea ka f.val))
variable (hb : ∀d,Admissible (fun f : DimensionCounts eb db d=>countEnergy eb kb f.val))

include ha hb in
lemma countSum_admissible (d : I→ℕ) :
    Admissible (fun f : DimensionCounts (Sum.elim ea eb) (Sum.elim da db) d=>
      countEnergy (Sum.elim ea eb) (Sum.elim ka kb) f.val) := by
  let k (s : DimensionSplit d) (f : DimensionCounts ea da s.left × DimensionCounts eb db s.right) :=
    countEnergy ea ka f.1.val+countEnergy eb kb f.2.val
  exact admissible_injective (admissible_sigma k (fun s=>admissible_prod (ha s.left) (hb s.right)))
    (countSumDimensionEquiv ea eb da db d) (countSumDimensionEquiv ea eb da db d).injective
    (fun f=>(countSumDimension_energy ea eb da db ka kb d f).symm)

end
end ElementaryPositivity.SignedMultiplicity

end
section
namespace ElementaryPositivity.SignedMultiplicity
open EnergyLaurent
noncomputable section
variable {A B I : Type*} (e : A ≃ B) (even : B→Prop) (dim : B→(I→ℕ)) (k : B→ℤ)

def dimensionReindex (d : I→ℕ) : DimensionCounts (fun a=>even (e a)) (fun a=>dim (e a)) d ≃
    DimensionCounts even dim d :=
  (countReindex e _ _ (fun _=>Iff.rfl)).subtypeEquiv (fun f=>by
    change f.val.sum (fun a n=>n • dim (e a))=d ↔ _
    change _ ↔ (countReindex e _ _ (fun _=>Iff.rfl) f).val.sum (fun b n=>n • dim b)=d
    rw [countReindex_sum])

lemma dimensionReindex_energy (d : I→ℕ)
    (f : DimensionCounts (fun a=>even (e a)) (fun a=>dim (e a)) d) :
    countEnergy even k (dimensionReindex e even dim d f).val=
      countEnergy (fun a=>even (e a)) (fun a=>k (e a)) f.val :=
  countReindex_sum e _ _ (fun _=>Iff.rfl) f.val k

end
end ElementaryPositivity.SignedMultiplicity

namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent
noncomputable section
variable {S T I : Type*} (e : S ≃ T) (a : T→ℕ) (dim : T→(I→ℕ)) (k : T→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))

def stringReindex (d : I→ℕ) :
    StringCounts (fun s=>a (e s)) (fun s=>dim (e s)) d ≃ StringCounts a dim d :=
  dimensionReindex (Equiv.prodCongr e (Equiv.refl ℕ)) (fun x=>a x.1≠0) (fun x=>dim x.1) d

lemma stringReindex_energy (d : I→ℕ)
    (f : StringCounts (fun s=>a (e s)) (fun s=>dim (e s)) d) :
    stringEnergy a dim k d (stringReindex e a dim d f)=
      stringEnergy (fun s=>a (e s)) (fun s=>dim (e s)) (fun s=>k (e s)) d f :=
  dimensionReindex_energy (Equiv.prodCongr e (Equiv.refl ℕ))
    (fun x=>a x.1≠0) (fun x=>dim x.1) (fun x=>k x.1-2*(x.2:ℤ)) d f

include he in
lemma stringReindex_admissible (d : I→ℕ) :
    Admissible (stringEnergy (fun s=>a (e s)) (fun s=>dim (e s)) (fun s=>k (e s)) d) :=
  admissible_injective (he d) (stringReindex e a dim d) (stringReindex e a dim d).injective
    (stringReindex_energy e a dim k d)
end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_IndexedUnit
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open EnergyLaurent WallUnits PowerSeries
open scoped LaurentSeries
noncomputable section

def strictUnitEquiv (a n : ℕ) (h : a=0) : Strict n ≃ UnitIndex a n :=
  Equiv.subtypeEquivRight (fun f=>by simp only [ite_eq_left h])

def weakUnitEquivSame (a n : ℕ) (h : a≠0) : Weak n ≃ UnitIndex a n :=
  Equiv.subtypeEquivRight (fun f=>by simp only [ite_eq_right h])

lemma unitAdmissible (a n : ℕ) (k : ℤ) : Admissible (unitEnergy a n k) := by
  by_cases h : a=0
  · exact admissible_equiv (strictAdmissible n k) (strictUnitEquiv a n h) (fun _=>rfl)
  · exact admissible_equiv (weakAdmissible n k) (weakUnitEquivSame a n h) (fun _=>rfl)

def indexedUnitSeries (a n : ℕ) (k : ℤ) : LaurentSeries ℚ :=
  series (unitEnergy a n k) (unitAdmissible a n k)

end
end ElementaryPositivity.UnitSelections
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_EnergyLimit
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.EnergyLaurent
noncomputable section
variable {A T : Type*} (e : A → ℤ) (he : Admissible e)

include he in
lemma finite_above (L : ℤ) : Set.Finite {a | L≤e a} := by
  obtain ⟨K,hK⟩:=he.1
  let B:=Σ z : Set.Icc L K,{a : A // e a=z.val}
  let (z : Set.Icc L K) : Finite {a : A // e a=z.val} := he.2 z.val
  have hs : Finite {a : A // L≤e a} :=
    Finite.of_injective (fun a : {a : A // L≤e a} =>
      (⟨⟨e a.val,a.property,hK a.val⟩,⟨a.val,rfl⟩⟩ : B)) (by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun x : B=>x.2.val) h)
  exact Set.finite_coe_iff.mp hs

variable (s : A → Finset T)

def finiteSupportCutoff [DecidableEq T] (L : ℤ) : Finset T :=
  (finite_above e he L).toFinset.biUnion s

def supportRestrictedSeries (S : Finset T) : LaurentSeries ℚ :=
  series (fun a : {a : A // s a⊆S}=>e a.val)
    (admissible_subtype he (fun a=>s a⊆S))

end
end ElementaryPositivity.EnergyLaurent

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
variable {S I : Type*} (a : S → ℕ) (dim : S → (I→ℕ)) (k : S → ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))

def startSupport (d : I→ℕ) (f : StringCounts a dim d) : Finset S :=
  f.val.val.support.image Prod.fst

def startEmbedding (T : Finset S) : (T×ℕ) ↪ (S×ℕ) :=
  (Function.Embedding.subtype (fun s=>s∈T)).prodMap (Function.Embedding.refl ℕ)

lemma startSupport_iff (T : Finset S) (d : I→ℕ) (f : StringCounts a dim d) :
    (↑f.val.val.support ⊆ Set.range (startEmbedding T)) ↔ startSupport a dim d f⊆T := by
  classical
  constructor
  · intro H s hs
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hs
    obtain ⟨⟨s,j⟩,he⟩:=H hx
    have HE:=congrArg Prod.fst he
    change s.val=x.1 at HE
    exact HE ▸ s.property
  · intro H x hx
    exact ⟨(⟨x.1,H (Finset.mem_image.mpr ⟨x,hx,rfl⟩)⟩,x.2),rfl⟩

def finiteStartEquiv (T : Finset S) (d : I→ℕ) :
    StringCounts (fun s:T=>a s.val) (fun s:T=>dim s.val) d ≃
      {f : StringCounts a dim d // startSupport a dim d f⊆T} :=
  (dimensionSupportEquiv (startEmbedding T) (fun x:S×ℕ=>a x.1≠0) (fun x=>dim x.1) d).trans
    (Equiv.subtypeEquivRight (startSupport_iff a dim T d))

lemma finiteStart_energy (T : Finset S) (d : I→ℕ)
    (f : StringCounts (fun s:T=>a s.val) (fun s:T=>dim s.val) d) :
    stringEnergy a dim k d (finiteStartEquiv a dim T d f).val=
      stringEnergy (fun s:T=>a s.val) (fun s:T=>dim s.val) (fun s:T=>k s.val) d f :=
  dimensionSupport_energy (startEmbedding T) (fun x:S×ℕ=>a x.1≠0)
    (fun x=>dim x.1) (fun x=>k x.1-2*(x.2:ℤ)) d f

include he in
lemma finiteStart_admissible (T : Finset S) (d : I→ℕ) :
    Admissible (stringEnergy (fun s:T=>a s.val) (fun s:T=>dim s.val) (fun s:T=>k s.val) d) :=
  admissible_injective (admissible_subtype (he d) (fun f=>startSupport a dim d f⊆T))
    (finiteStartEquiv a dim T d) (finiteStartEquiv a dim T d).injective
    (finiteStart_energy a dim k T d)

def finiteStartSeries (T : Finset S) (d : I→ℕ) : LaurentSeries ℚ :=
  stringSeries (fun s:T=>a s.val) (fun s:T=>dim s.val) (fun s:T=>k s.val)
    (finiteStart_admissible a dim k he T) d

end
end ElementaryPositivity.UnitSelections

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent
noncomputable section
variable {S T I : Type*} (a : S→ℕ) (dim : S→(I→ℕ)) (k : S→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))

include he in
lemma stringEmbedding_admissible (e : T ↪ S) (d : I→ℕ) :
    Admissible (stringEnergy (fun s=>a (e s)) (fun s=>dim (e s)) (fun s=>k (e s)) d) := by
  let E:=e.prodMap (Function.Embedding.refl ℕ)
  let F:=dimensionSupportEquiv E (fun x:S×ℕ=>a x.1≠0) (fun x=>dim x.1) d
  exact admissible_injective (he d) (fun f=>(F f).val)
    (fun x y h=>F.injective (Subtype.ext h))
    (dimensionSupport_energy E (fun x:S×ℕ=>a x.1≠0) (fun x=>dim x.1)
      (fun x=>k x.1-2*(x.2:ℤ)) d)

end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_StringSumProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle
noncomputable section
variable {A B I : Type*}
variable (a : A→ℕ) (b : B→ℕ) (da : A→(I→ℕ)) (db : B→(I→ℕ))
variable (ka : A→ℤ) (kb : B→ℤ)

def stringSumEven (x : (A×ℕ)⊕(B×ℕ)) : Prop :=
  Sum.elim (fun y:A×ℕ=>a y.1≠0) (fun y:B×ℕ=>b y.1≠0) x

lemma stringSumEven_iff (x : (A⊕B)×ℕ) :
    Sum.elim a b x.1≠0 ↔ stringSumEven a b (Equiv.sumProdDistrib A B ℕ x) := by
  rcases x with ⟨x,j⟩
  cases x <;> rfl

def stringSumCounts (d : I→ℕ) :
    StringCounts (Sum.elim a b) (Sum.elim da db) d ≃
      DimensionCounts (stringSumEven a b)
        (Sum.elim (fun x:A×ℕ=>da x.1) (fun x:B×ℕ=>db x.1)) d :=
  (countReindex (Equiv.sumProdDistrib A B ℕ) _ _ (stringSumEven_iff a b)).subtypeEquiv (fun f=>by
    change f.val.sum _=d ↔ (countReindex _ _ _ (stringSumEven_iff a b) f).val.sum _=d
    rw [countReindex_sum]
    have H : ∀x:(A⊕B)×ℕ,Sum.elim (fun x:A×ℕ=>da x.1) (fun x:B×ℕ=>db x.1)
        (Equiv.sumProdDistrib A B ℕ x)=Sum.elim da db x.1 := by
      intro x
      rcases x with ⟨x,j⟩
      cases x <;> rfl
    simp_rw [H])

lemma stringSumCounts_energy (d : I→ℕ) (f : StringCounts (Sum.elim a b) (Sum.elim da db) d) :
    countEnergy (stringSumEven a b)
      (Sum.elim (fun x:A×ℕ=>ka x.1-2*(x.2:ℤ)) (fun x:B×ℕ=>kb x.1-2*(x.2:ℤ)))
      (stringSumCounts a b da db d f).val=
      stringEnergy (Sum.elim a b) (Sum.elim da db) (Sum.elim ka kb) d f := by
  change (countReindex _ _ _ (stringSumEven_iff a b) f.val).val.sum _=_
  rw [countReindex_sum]
  dsimp only [stringEnergy,countEnergy]
  apply Finsupp.sum_congr
  intro x hx
  rcases x with ⟨x,j⟩
  cases x <;> rfl

variable [Fintype I] [DecidableEq I]
variable (ha : ∀d,Admissible (stringEnergy a da ka d))
variable (hb : ∀d,Admissible (stringEnergy b db kb d))
include ha hb in
lemma stringSum_admissible (d : I→ℕ) :
    Admissible (stringEnergy (Sum.elim a b) (Sum.elim da db) (Sum.elim ka kb) d) :=
  admissible_injective
    (countSum_admissible (fun x:A×ℕ=>a x.1≠0) (fun x:B×ℕ=>b x.1≠0)
      (fun x=>da x.1) (fun x=>db x.1)
      (fun x=>ka x.1-2*(x.2:ℤ)) (fun x=>kb x.1-2*(x.2:ℤ)) ha hb d)
    (stringSumCounts a b da db d) (stringSumCounts a b da db d).injective
    (stringSumCounts_energy a b da db ka kb d)

end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_StringRay
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle WeightedTorusSeries QuantumTorus WallUnits PowerSeries
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : ℕ) (δ : I→ℕ) (k : ℤ)

def oneStringEquiv : (Σn,UnitIndex a n) ≃ CountSelection (fun _ : PUnit×ℕ=>a≠0) :=
  (unitRowCount a).trans (countReindex (Equiv.punitProd ℕ).symm _ _ (fun _=>Iff.rfl))

omit [Fintype I] [DecidableEq I] in
lemma oneString_dimension (q : Σn,UnitIndex a n) :
    countDimension (fun _ : PUnit×ℕ=>a≠0) (fun _=>δ) (oneStringEquiv a q)=q.1 • δ := by
  dsimp only [countDimension,oneStringEquiv,Equiv.trans_apply]
  rw [countReindex_sum]
  change (unitRowCount a q).val.sum (fun _ n=>n • δ)=_
  rw [Finsupp.sum,←Finset.sum_smul]
  change ((unitRowCount a q).val.sum (fun _ n=>n)) • δ=_
  rw [unitRowCount_sum]

omit [Fintype I] [DecidableEq I] in
lemma nsmul_dimension_injective (hδ : δ≠0) : Function.Injective (fun n:ℕ=>n • δ) := by
  obtain ⟨i,hi⟩:=Function.ne_iff.mp hδ
  intro n m H
  have HE:=congrArg (fun d:I→ℕ=>d i) H
  change n*δ i=m*δ i at HE
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) HE

variable (hδ : δ≠0)

def unitSigmaFibre (n : ℕ) : UnitIndex a n ≃ {q : Σm,UnitIndex a m // q.1=n} where
  toFun f:=⟨⟨n,f⟩,rfl⟩
  invFun q:=q.property ▸ q.val.2
  left_inv f:=rfl
  right_inv q:=by
    rcases q with ⟨⟨m,f⟩,h⟩
    cases h
    rfl

def oneStringDimensionEquiv (n : ℕ) : UnitIndex a n ≃
    StringCounts (fun _:PUnit=>a) (fun _=>δ) (n • δ) :=
  (unitSigmaFibre a n).trans ((oneStringEquiv a).subtypeEquiv (fun q=>by
    change q.1=n ↔ countDimension _ _ (oneStringEquiv a q)=n • δ
    rw [oneString_dimension]
    exact (nsmul_dimension_injective δ hδ).eq_iff.symm))

end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_StringSumPush
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {A I : Type*} [Fintype I] [DecidableEq I]
variable (a : Option A→ℕ) (dim : Option A→(I→ℕ)) (k : Option A→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)

abbrev noneEmbedding : PUnit.{1} ↪ Option A := ⟨fun _=>none,fun _ _ _=>Subsingleton.elim _ _⟩
abbrev someEmbedding : A ↪ Option A := ⟨some,Option.some_injective _⟩

end
end ElementaryPositivity.UnitSelections

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
universe u
variable {S : Type u} {I : Type*} [Fintype I] [DecidableEq I]
variable (a : S→ℕ) (dim : S→(I→ℕ)) (k : S→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D) (h0 : ∀s,dim s≠0)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)

def stringLiteralUnit (s : S) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  weightedRay LaurentRay.vUnit Ω (WeightedTorusSeries.weight w (dim s)) (P (dim s))
    (PowerSeries.map LaurentRay.atInfinity (indexedUnit (a s) (k s)))

end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WeightedCompletion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open QuantumTorus PowerSeries
noncomputable section
variable {I J M ι : Type*} [Fintype I] [DecidableEq I] [Fintype J] [AddCommGroup M]
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
variable (C : (J→ℤ)→+M) (hroot : ∀d,HasRootDegree C (weight w d) (P d))
local instance instRingTorusLaurentSeriesRat_rab7c6d_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance instAddCommMonoidTorusLaurentSeriesRat : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_StringLiteralClosure
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I]
variable (a : S→ℕ) (dim : S→(I→ℕ)) (k : S→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D) (h0 : ∀s,dim s≠0)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)

def finiteStringProducts : Set (PowerSeries (Torus LaurentRay.vUnit Ω)) :=
  {F | ∃l : List S,l.Nodup ∧ F=(l.map (stringLiteralUnit a dim k w Ω P)).prod}

end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_StringRootClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {S I J M : Type*} [Fintype I] [DecidableEq I] [Fintype J] [AddCommGroup M]
variable (a : S→ℕ) (dim : S→(I→ℕ)) (k : S→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D) (h0 : ∀s,dim s≠0)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M) (C : (J→ℤ)→+M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)
variable (V : M→Prop) (hr : ∀s,HasRootDegree C (WeightedTorusSeries.weight w (dim s)) (P (dim s)))
variable (hv : ∀s,V (P (dim s)))

def stringWallDatum (s : S) : WallUnitDatum M :=
  ⟨WeightedTorusSeries.weight w (dim s),P (dim s),a s,k s⟩

end
end ElementaryPositivity.UnitSelections

end

end OAI
end


