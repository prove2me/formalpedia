-- Prove2me | Definitions.Def_OAIQ368Chrom056
-- name    : OAIQ368Chrom056
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T19:59:48.777198+00:00
-- url     : https://prove2.me/theorems/3681deb4-836c-4c98-b8e8-2fcb930ab9cf
-- title:
--   Definitions bundle OAIQ368Chrom056 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 33 definitions and 19 theorems. The definitions and types are `OAI.ElementaryPositivity.EnergyLaurent.finSuccPi`, `OAI.ElementaryPositivity.EnergyLaurent.finitePiReindex`, `OAI.ElementaryPositivity.RawShuffle.HNWord`, `OAI.ElementaryPositivity.RawShuffle.HighHNIndex`, `OAI.ElementaryPositivity.RawShuffle.HighHNWord`, `OAI.ElementaryPositivity.RawShuffle.InputIndexLists`, `OAI.ElementaryPositivity.RawShuffle.UnitIndexList`, `OAI.ElementaryPositivity.RawShuffle.highDecorated`, `OAI.ElementaryPositivity.RawShuffle.highEmpty`, `OAI.ElementaryPositivity.RawShuffle.highEnergy`, `OAI.ElementaryPositivity.RawShuffle.highSeries`, `OAI.ElementaryPositivity.RawShuffle.hnSeries`, `OAI.ElementaryPositivity.RawShuffle.hnWordEquiv`, `OAI.ElementaryPositivity.RawShuffle.inputLinearEnergy`, `OAI.ElementaryPositivity.RawShuffle.inputListEquiv`, `OAI.ElementaryPositivity.RawShuffle.inputReorderingSeries`, `OAI.ElementaryPositivity.RawShuffle.inputTorusEnergy`, `OAI.ElementaryPositivity.RawShuffle.inputUnitEquiv`, `OAI.ElementaryPositivity.RawShuffle.instAddCommMonoidTorusLaurentSeriesRatVUnit`, `OAI.ElementaryPositivity.RawShuffle.listIndexSum`, `OAI.ElementaryPositivity.RawShuffle.lowEmpty`, `OAI.ElementaryPositivity.RawShuffle.lowRowsEquiv`, `OAI.ElementaryPositivity.RawShuffle.lowSeries`, `OAI.ElementaryPositivity.RawShuffle.outputReorderingSeries`, `OAI.ElementaryPositivity.RawShuffle.outputRowsSeries`, `OAI.ElementaryPositivity.RawShuffle.splitHNWord`, `OAI.ElementaryPositivity.RawShuffle.staircaseShift`, `OAI.ElementaryPositivity.RawShuffle.thresholdIndexEquiv`, `OAI.ElementaryPositivity.RawShuffle.weakStrictListEquiv`, `OAI.ElementaryPositivity.RawShuffle.weakUnitListEquiv`, `OAI.ElementaryPositivity.RawShuffle.zeroBlockCoefficient`, `OAI.ElementaryPositivity.ThresholdWords.splitEquiv`, `OAI.ElementaryPositivity.WeightedTorusSeries.instAddCommMonoidTorus_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_GradedAlgebra_CompleteUnit`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/CompleteUnit.lean), [`Chromatic_GradedAlgebra_FintypeEnergyProduct`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/FintypeEnergyProduct.lean), [`Chromatic_GradedAlgebra_HNSeries`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/HNSeries.lean), [`Chromatic_Shuffle_HNSlope`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/HNSlope.lean), [`Chromatic_Shuffle_HNThreshold`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/HNThreshold.lean), [`Chromatic_Shuffle_HNZeroFactor`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/HNZeroFactor.lean), [`Chromatic_Shuffle_HNZeroRows`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/HNZeroRows.lean), [`Chromatic_Shuffle_InputTorusEnergy`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/InputTorusEnergy.lean), [`Chromatic_Shuffle_PrimitiveBlockRows`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/PrimitiveBlockRows.lean), [`Chromatic_Shuffle_PrimitiveUnitRows`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/PrimitiveUnitRows.lean), [`Chromatic_Walls_FiniteReorderingEnergy`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/FiniteReorderingEnergy.lean), [`Chromatic_Walls_ThresholdWords`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/ThresholdWords.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom054` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.ElementaryPositivity.RawShuffle.literalInput_primitiveFactor`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom054

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_CompleteUnit
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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

def finSuccPi (n : ℕ) (A : Fin (n+1) → Type*) :
    (∀i,A i) ≃ A 0 × (∀i:Fin n,A i.succ) where
  toFun f := (f 0,fun i=>f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by funext i; exact Fin.cases rfl (fun _=>rfl) i
  right_inv p := rfl

lemma admissible_fin_pi (n : ℕ) (A : Fin n → Type*) (e : ∀i,A i → ℤ)
    (he : ∀i,Admissible (e i)) : Admissible (fun f : ∀i,A i=>∑i,e i (f i)) := by
  induction n with
  | zero =>
    constructor
    · exact ⟨0,fun _=>by simp⟩
    · intro E; infer_instance
  | succ n ih =>
    have hp:=admissible_prod (he 0) (ih (fun i=>A i.succ) (fun i=>e i.succ) (fun i=>he i.succ))
    exact admissible_equiv hp (finSuccPi n A).symm (fun f=>by
      change (∑i,e i (Fin.cases f.1 f.2 i))=e 0 f.1+∑i,e i.succ (f.2 i)
      rw [Fin.sum_univ_succ]
      rfl)

end
end ElementaryPositivity.EnergyLaurent
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_FintypeEnergyProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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
variable {I : Type*} [Fintype I] (A : I → Type*) (e : ∀i,A i → ℤ)

def finitePiReindex : (∀j:Fin (Fintype.card I),A ((Fintype.equivFin I).symm j)) ≃ (∀i,A i) :=
  Equiv.piCongrLeft A (Fintype.equivFin I).symm

lemma finitePiReindex_energy (f : ∀j:Fin (Fintype.card I),A ((Fintype.equivFin I).symm j)) :
    (∑i,e i (finitePiReindex A f i))=∑j,e ((Fintype.equivFin I).symm j) (f j) := by
  rw [←(Fintype.equivFin I).symm.sum_comp (fun i=>e i (finitePiReindex A f i))]
  simp only [finitePiReindex,Equiv.piCongrLeft_apply_apply]

lemma admissible_pi (he : ∀i,Admissible (e i)) : Admissible (fun f : ∀i,A i=>∑i,e i (f i)) :=
  admissible_equiv (admissible_fin_pi (Fintype.card I) _ _ (fun j=>he ((Fintype.equivFin I).symm j)))
    (finitePiReindex A) (finitePiReindex_energy A e)

end
end ElementaryPositivity.EnergyLaurent
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PrimitiveUnitRows
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
attribute [local instance] Classical.propDecidable

lemma strict_fin_nat_bound {n : ℕ} {f : Fin n → ℕ} (hf : StrictMono f) (i : Fin n) : i.val≤f i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    induction i using Fin.induction with
    | zero => simp
    | succ i ih =>
      have H:=hf (Fin.castSucc_lt_succ (i := i))
      change i.val≤f i.castSucc at ih
      change i.val+1≤f i.succ
      omega

noncomputable def weakStrictListEquiv (n : ℕ) :
    {f : Fin n → ℕ // Monotone f} ≃ {f : Fin n → ℕ // StrictMono f} where
  toFun f := ⟨fun i=>f.val i+i.val,by
    intro i j hij
    have H:=f.property hij.le
    have Hij : i.val<j.val := hij
    dsimp
    omega⟩
  invFun f := ⟨fun i=>f.val i-i.val,by
    cases n with
    | zero => intros i; exact Fin.elim0 i
    | succ n =>
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      have H:=f.property (Fin.castSucc_lt_succ (i := i))
      change f.val i.castSucc-i.val≤f.val i.succ-(i.val+1)
      omega⟩
  left_inv f := by apply Subtype.ext; funext i; dsimp; omega
  right_inv f := by
    apply Subtype.ext; funext i
    have H:=strict_fin_nat_bound f.property i
    dsimp
    omega

abbrev UnitIndexList (elementary : Bool) (n : ℕ) :=
  {f : Fin n → ℕ // if elementary then StrictMono f else Monotone f}
noncomputable def weakUnitListEquiv (elementary : Bool) (n : ℕ) :
    {f : Fin n → ℕ // Monotone f} ≃ UnitIndexList elementary n := by
  cases elementary
  · exact Equiv.refl _
  · exact weakStrictListEquiv n

lemma weakUnitListEquiv_val (elementary : Bool) (n : ℕ)
    (f : {f : Fin n → ℕ // Monotone f}) (i : Fin n) :
    (weakUnitListEquiv elementary n f).val i=f.val i+(if elementary then i.val else 0) := by
  cases elementary <;> rfl

lemma fin_staircase_sum (n : ℕ) :
    2*(∑ j : Fin n,(j.val:ℤ))=(n:ℤ)*((n:ℤ)-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one]
    nlinarith

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (ε : I → Bool) (d : I → ℕ)
abbrev InputIndexLists := ∀ i,UnitIndexList (ε i) (d i)
noncomputable def inputListEquiv : SortedPackExponent d ≃ InputIndexLists ε d :=
  Equiv.piCongrRight (fun i=>weakUnitListEquiv (ε i) (d i))

def listIndexSum (x : InputIndexLists ε d) : ℕ := ∑ i,∑ j,(x i).val j

omit [DecidableEq I] in
lemma inputListIndexSum (x : SortedPackExponent d) :
    2*(listIndexSum ε d (inputListEquiv ε d x):ℤ)=
      2*(sortedPackDegree d x:ℤ)+
        ∑ i,((1:ℤ)-elementaryDiagonal ε i)*(d i:ℤ)*((d i:ℤ)-1) := by
  simp only [listIndexSum,inputListEquiv,Equiv.piCongrRight_apply,Pi.map,weakUnitListEquiv_val,
    sortedPackDegree,Nat.cast_sum,Nat.cast_add,Finset.sum_add_distrib,mul_add]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i hi
  cases h : ε i with
  | false => simp [h,elementaryDiagonal]
  | true => simpa [h,elementaryDiagonal] using fin_staircase_sum (d i)
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_InputTorusEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ)

def staircaseShift (d : I → ℕ) : ℤ :=
  ∑ i,((1:ℤ)-a i i)*(d i:ℤ)*((d i:ℤ)-1)

def inputLinearEnergy (d : I → ℕ) : ℤ := ∑ i,κ i*(d i:ℤ)

omit [DecidableEq I] in
lemma normalization_diagonal (d : I → ℕ) :
    inputShift a κ d-eulerForm a d d=
      inputLinearEnergy κ d-staircaseShift a d+crossInteraction a d := by
  have H : (∑ i,(d i:ℤ)*(κ i+1-a i i))-(∑ i,(d i:ℤ)*(d i:ℤ))=
      (∑ i,κ i*(d i:ℤ))-(∑ i,((1:ℤ)-a i i)*(d i:ℤ)*((d i:ℤ)-1))-
        ∑ i,(a i i:ℤ)*(d i:ℤ)^2 := by
    simp only [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i hi
    ring
  unfold inputShift eulerForm inputLinearEnergy staircaseShift crossInteraction
  linear_combination H

variable (ε : I → Bool) (d : I → ℕ)
def inputTorusEnergy (x : InputIndexLists ε d) : ℤ :=
  inputLinearEnergy κ d-2*(listIndexSum ε d x:ℤ)+crossInteraction a d

omit [DecidableEq I] in
theorem inputListEnergy_normalized (ha : ∀ i,a i i=elementaryDiagonal ε i)
    (x : SortedPackExponent d) :
    inputTorusEnergy a κ ε d (inputListEquiv ε d x)=
      normalizedEnergy a κ d (sortedPackDegree d x) := by
  have H:=inputListIndexSum ε d x
  have Hs : (∑ i,((1:ℤ)-elementaryDiagonal ε i)*(d i:ℤ)*((d i:ℤ)-1))=
      staircaseShift a d := by simp only [staircaseShift,ha]
  rw [Hs] at H
  unfold inputTorusEnergy normalizedEnergy
  rw [normalization_diagonal]
  linear_combination -H
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteReorderingEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
universe u

variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

local instance finiteLaurentSlopeFact_r903ac8_1 (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩
omit [DecidableEq I] in
lemma sortedPackDegree_finite (d : I → ℕ) (k : ℤ) :
    Finite {i : SortedPackExponent d // (sortedPackDegree d i : ℤ)=k} := by
  let := componentS_range_finite d k
  exact ElementaryPositivity.homogeneousBasis_finite (packOrbitBasis d)
    (fun i=>(sortedPackDegree d i:ℤ)) (componentS d) (packOrbitBasis_component d) k

omit [DecidableEq I] in
lemma inputEnergy_admissible (ε : I → Bool)
    (ha : ∀i,a i i=elementaryDiagonal ε i) (d : I → ℕ) :
    EnergyLaurent.Admissible (inputTorusEnergy a κ ε d) := by
  have he (x : InputIndexLists ε d) : inputTorusEnergy a κ ε d x=
      normalizedEnergy a κ d (sortedPackDegree d ((inputListEquiv ε d).symm x)) := by
    simpa using inputListEnergy_normalized a κ ε d ha ((inputListEquiv ε d).symm x)
  constructor
  · refine ⟨inputShift a κ d-eulerForm a d d,fun x=>?_⟩
    rw [he]
    unfold normalizedEnergy
    have H : 0≤(sortedPackDegree d ((inputListEquiv ε d).symm x):ℤ) := by positivity
    omega
  · intro e
    let E : {x : SortedPackExponent d // normalizedEnergy a κ d (sortedPackDegree d x)=e} ≃
        {x : InputIndexLists ε d // inputTorusEnergy a κ ε d x=e} :=
      (inputListEquiv ε d).subtypeEquiv (by intro x; rw [inputListEnergy_normalized a κ ε d ha])
    let := finite_injective_regrade (fun x : SortedPackExponent d=>(sortedPackDegree d x:ℤ))
      (sortedPackDegree_finite d) (normalizedEnergy a κ d) (normalizedEnergy_injective a κ d) e
    exact Finite.of_equiv _ E

noncomputable def inputReorderingSeries (ε : I → Bool)
    (ha : ∀i,a i i=elementaryDiagonal ε i) (d : I → ℕ) : LaurentSeries ℚ :=
  EnergyLaurent.series (inputTorusEnergy a κ ε d) (inputEnergy_admissible a κ ε ha d)

noncomputable def outputReorderingSeries (d : I → ℕ) : LaurentSeries ℚ :=
  EnergyLaurent.series
    (fun x : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val=>
      hnStringEnergy a κ c η hc x.1.val x.2)
    (outputEnergy_admissible a κ c η hc d)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PrimitiveBlockRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic UnitSelections
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.blockRowsFact
def outputRowsSeries (d : I → ℕ) : LaurentSeries ℚ := EnergyLaurent.series _
  (outputRows_admissible a κ c η hc d)

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

local instance decoratedFact_r903ac8_1 (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩
lemma decoratedDimension_append (l r : List (RowBlock a c η hc)) :
    decoratedDimension a c η hc (l++r)=decoratedDimension a c η hc l+decoratedDimension a c η hc r := by
  simp [decoratedDimension]

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ThresholdWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.ThresholdWords
noncomputable section
attribute [local instance] Classical.propDecidable
variable {A : Type*} (P : A → Prop) (μ : A → ℝ)

def splitEquiv (θ : ℝ) : Word P μ ≃ High P μ θ × Low P μ θ where
  toFun l:=(high P μ θ l,low P μ θ l)
  invFun p:=merge P μ θ p.1 p.2
  left_inv l:=merge_high_low P μ θ l
  right_inv p:=by simp

end
end ElementaryPositivity.ThresholdWords

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

abbrev HNWord := ThresholdWords.Word
  (fun b : RowBlock a c η hc=>b.1≠0) (fun b=>slope c η b.1)
abbrev HighHNWord (θ : ℝ) := ThresholdWords.High
  (fun b : RowBlock a c η hc=>b.1≠0) (fun b=>slope c η b.1) θ

def hnWordEquiv (d : I → ℕ) : DecoratedHN a c η hc d ≃
    {w : HNWord a c η hc // decoratedDimension a c η hc w.val=d} where
  toFun l:=⟨⟨l.val,(hnOrdered_map_iff a c η hc l.val).mp l.property.2⟩,l.property.1⟩
  invFun w:=⟨w.val.val,⟨w.property,(hnOrdered_map_iff a c η hc w.val.val).mpr w.val.property⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

abbrev HighHNIndex (θ : ℝ) (d : I → ℕ) :=
  {w : HighHNWord a c η hc θ // decoratedDimension a c η hc w.val.val=d}

def splitHNWord (θ : ℝ) : HNWord a c η hc ≃ HighHNWord a c η hc θ × LowHNWord a c η hc θ :=
  ThresholdWords.splitEquiv _ _ θ

lemma splitHNWord_dimension (θ : ℝ) (w : HNWord a c η hc) :
    decoratedDimension a c η hc (splitHNWord a c η hc θ w).1.val.val+
    decoratedDimension a c η hc (splitHNWord a c η hc θ w).2.val.val=
    decoratedDimension a c η hc w.val := by
  rw [←decoratedDimension_append]
  exact congrArg (decoratedDimension a c η hc)
    (congrArg Subtype.val (ThresholdWords.merge_high_low _ _ θ w))

def thresholdIndexEquiv (θ : ℝ) (d : I → ℕ) : DecoratedHN a c η hc d ≃
    Σ s : DimensionSplit d,HighHNIndex a c η hc θ s.left × LowHNIndex a c η hc θ s.right :=
  (hnWordEquiv a c η hc d).trans
    (((splitHNWord a c η hc θ).subtypeEquiv (fun w=>by rw [splitHNWord_dimension])).trans
      (dimensionProduct (fun w : HighHNWord a c η hc θ=>decoratedDimension a c η hc w.val.val)
        (fun w : LowHNWord a c η hc θ=>decoratedDimension a c η hc w.val.val) d).symm)

end
end ElementaryPositivity.RawShuffle

end
section

namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

abbrev highEnergy (θ : ℝ) (d : I → ℕ) (w : HighHNIndex a c η hc θ d) :=
  decoratedEnergy a κ c η hc w.val.val.val

def highDecorated (θ : ℝ) (d : I → ℕ) (w : HighHNIndex a c η hc θ d) : DecoratedHN a c η hc d :=
  ⟨w.val.val.val,⟨w.property,(hnOrdered_map_iff a c η hc _).mpr w.val.val.property⟩⟩

lemma highEnergy_admissible (θ : ℝ) (d : I → ℕ) : Admissible (highEnergy a κ c η hc θ d) :=
  admissible_injective (decoratedEnergy_admissible a κ c η hc d) (highDecorated a c η hc θ d)
    (fun _ _ H=>Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun z : DecoratedHN a c η hc d=>z.val) H)))) (fun _=>rfl)

def highSeries (θ : ℝ) (d : I → ℕ) : LaurentSeries ℚ :=
  series (highEnergy a κ c η hc θ d) (highEnergy_admissible a κ c η hc θ d)
def lowSeries (θ : ℝ) (d : I → ℕ) : LaurentSeries ℚ :=
  series (lowEnergy a κ c η hc θ d) (lowEnergy_admissible a κ c η hc θ d)
def hnSeries (d : I → ℕ) : LaurentSeries ℚ :=
  series (fun w : DecoratedHN a c η hc d=>decoratedEnergy a κ c η hc w.val)
    (decoratedEnergy_admissible a κ c η hc d)

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNSlope
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

lemma slopeValue_add (θ : ℝ) (d e : I → ℕ) :
    slopeValue c η θ (d+e)=slopeValue c η θ d+slopeValue c η θ e := by
  simp only [slopeValue,mass_add]
  ring
include hc in
lemma slopeValue_nonpos_iff (θ : ℝ) (d : I → ℕ) (hd : d≠0) :
    slopeValue c η θ d≤0 ↔ slope c η d≤θ := by
  rw [slopeValue,sub_nonpos,SlopeArithmetic.slope,div_le_iff₀ (mass_pos c hc d hd)]

variable [DecidableEq I]

def highEmpty (θ : ℝ) : HighHNIndex a c η hc θ 0 :=
  ⟨⟨⟨[],by simp⟩,by simp⟩,rfl⟩
def lowEmpty (θ : ℝ) : LowHNIndex a c η hc θ 0 :=
  ⟨⟨⟨[],by simp⟩,by simp⟩,rfl⟩

lemma decorated_value_nonpos (θ : ℝ) (l : List (RowBlock a c η hc))
    (h : ∀b∈l,slopeValue c η θ b.1≤0) :
    slopeValue c η θ (decoratedDimension a c η hc l)≤0 := by
  induction l with
  | nil=>simp [decoratedDimension]
  | cons b l ih=>
    change slopeValue c η θ (b.1+decoratedDimension a c η hc l)≤0
    rw [slopeValue_add]
    exact add_nonpos (h b (by simp)) (ih (fun e he=>h e (by simp [he])))

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open UnitSelections EnergyLaurent WallUnits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I]
variable (a : I → I → ℕ) (κ : I → ℤ) (ε : I → Bool)

def inputUnitEquiv (d : I → ℕ) : InputIndexLists ε d ≃
    (∀i,UnitIndex (elementaryDiagonal ε i) (d i)) :=
  Equiv.piCongrRight (fun i=>Equiv.subtypeEquivRight (fun f=>by
    cases hi : ε i <;> simp [elementaryDiagonal,hi]))

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HNSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle ElementaryPositivity.QuantumTorus PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]

variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
local instance instAddCommMonoidTorus_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNZeroRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

lemma decorated_zero_each (θ : ℝ) (l : List (RowBlock a c η hc))
    (h : ∀b∈l,slopeValue c η θ b.1≤0)
    (hz : slopeValue c η θ (decoratedDimension a c η hc l)=0) :
    ∀b∈l,slopeValue c η θ b.1=0 := by
  induction l with
  | nil=>simp
  | cons b l ih=>
    have hb:=h b (by simp)
    have ht : ∀e∈l,slopeValue c η θ e.1≤0 := fun e he=>h e (by simp [he])
    have hl:=decorated_value_nonpos a c η hc θ l ht
    change slopeValue c η θ (b.1+decoratedDimension a c η hc l)=0 at hz
    rw [slopeValue_add] at hz
    have hb0 : slopeValue c η θ b.1=0 := by linarith
    have hl0 : slopeValue c η θ (decoratedDimension a c η hc l)=0 := by linarith
    intro e he
    rcases List.mem_cons.mp he with rfl|he
    · exact hb0
    · exact ih ht hl0 e he

lemma lowIndex_singleton (θ : ℝ) (d : I → ℕ) (hd : d≠0)
    (hz : slopeValue c η θ d=0) (x : LowHNIndex a c η hc θ d) :
    ∃r : BlockRows a c η hc d,x.val.val.val=[⟨d,r⟩] := by
  have hval : ∀b∈x.val.val.val,slopeValue c η θ b.1≤0 := fun b hb=>
    (slopeValue_nonpos_iff c η hc θ b.1 (x.val.val.property.1 b hb)).mpr (x.val.property b hb)
  have heach:=decorated_zero_each a c η hc θ x.val.val.val hval (by rw [x.property,hz])
  have hs : ∀b∈x.val.val.val,slope c η b.1=θ := fun b hb=>
    (slopeValue_eq_zero_iff c η hc θ b.1 (x.val.val.property.1 b hb)).mp (heach b hb)
  have hn : x.val.val.val≠[] := by
    intro H
    have hh:=x.property
    rw [H] at hh
    exact hd hh.symm
  obtain ⟨b,l,hl⟩:=List.exists_cons_of_ne_nil hn
  have hnil : l=[] := by
    cases l with
    | nil=>rfl
    | cons e l=>
      have H:=x.val.val.property.2
      rw [hl] at H
      have Hbe := (List.pairwise_cons.mp H).1 e (by simp)
      change slope c η e.1 < slope c η b.1 at Hbe
      rw [hs b (by rw [hl]; simp),hs e (by rw [hl]; simp)] at Hbe
      exact (lt_irrefl θ Hbe).elim
  subst l
  have hb : b.1=d := by
    have H:=x.property
    simpa only [hl,decoratedDimension,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using H
  rcases b with ⟨b,r⟩
  dsimp only at hb
  subst b
  exact ⟨r,hl⟩

def lowRowsEquiv (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ) :
    BlockRows a c η hc d ≃ LowHNIndex a c η hc θ d :=
  Equiv.ofBijective (lowFromRow a c η hc θ d hd hs)
    ⟨lowFromRow_injective a c η hc θ d hd hs,fun x=>by
      obtain ⟨r,hr⟩:=lowIndex_singleton a c η hc θ d hd
        ((slopeValue_eq_zero_iff c η hc θ d hd).mpr hs) x
      exact ⟨r,Subtype.ext (Subtype.ext (Subtype.ext hr.symm))⟩⟩

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNZeroFactor
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent QuantumTorus WeightedTorusSeries WallUnits
open PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

def zeroBlockCoefficient (θ : ℝ) (d : I → ℕ) : LaurentSeries ℚ := by
  classical
  exact if hd : d=0 then 1 else if slopeValue c η θ d=0 then
    series (blockRowsEnergy a κ c η hc d) (blockRowsEnergy_admissible a κ c η hc d hd) else 0

variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid

end
end ElementaryPositivity.RawShuffle

end

end OAI
end


