-- Prove2me | Definitions.Def_OAIQ368Chrom021
-- name    : OAIQ368Chrom021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:10:48.117777+00:00
-- url     : https://prove2.me/theorems/3e768f59-2923-48a9-a0dd-2a6f24491bba
-- title:
--   Definitions bundle OAIQ368Chrom021 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 8 definitions and 12 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separateSeries`, `OAI.ElementaryPositivity.RawShuffle.emptyLeftCut`, `OAI.ElementaryPositivity.RawShuffle.emptyRightCut`, `OAI.ElementaryPositivity.RawShuffle.slopeValue`, `OAI.ElementaryPositivity.RawShuffle.transposeDimensionGrid`, `OAI.ElementaryPositivity.SlopeArithmetic.OnSlopeOrZero`, `OAI.ElementaryPositivity.WeightedTorusSeries.convolution`, `OAI.ElementaryPositivity.WeightedTorusSeries.splitSliceEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_GradedAlgebra_Product`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/Product.lean), [`Chromatic_GradedAlgebra_WeightedTorusSeries`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/WeightedTorusSeries.lean), [`Chromatic_Shuffle_DimensionGrid`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/DimensionGrid.lean), [`Chromatic_Shuffle_HNSlope`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/HNSlope.lean), [`Chromatic_Shuffle_LaurentKernel`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/LaurentKernel.lean), [`Chromatic_Shuffle_Realization`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/Realization.lean), [`Chromatic_Shuffle_ShuffleUnits`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/ShuffleUnits.lean), [`Chromatic_Walls_PolynomialCoeffLinear`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/PolynomialCoeffLinear.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom017` and `OAIQ368Chrom018` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom022`; the proofs of `OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds` and `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom017
import Definitions.Def_OAIQ368Chrom018

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Realization
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

variable [∀ i,Fintype (A i)]

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma valueAt_injective {d : I → ℕ} {s : ∀ i,Finset (A i)} (r : Realization d s) :
    Function.Injective (valueAt r) := by
  intro f g h
  apply Subtype.ext
  apply MvPolynomial.rename_injective (realizationMap r) (realizationMap_injective r)
  exact IsFractionRing.injective (MvPolynomial (Σi,A i) ℚ) _ h

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

def OnSlopeOrZero (c η : I → ℝ) (θ : ℝ) (d : I → ℕ) : Prop :=
  d = 0 ∨ slope c η d = θ

end ElementaryPositivity.SlopeArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_DimensionGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
variable {I : Type*}

open DimensionSplit

def transposeDimensionGrid (d e α β : I → ℕ) :
    RowDimensionGrid d e α β ≃ ColumnDimensionGrid d e α β where
  toFun s := ⟨(ofPair (left s.val.1) (left s.val.2) s.property.1,
      ofPair (right s.val.1) (right s.val.2) s.property.2), by simp⟩
  invFun s := ⟨(ofPair (left s.val.1) (left s.val.2) s.property.1,
      ofPair (right s.val.1) (right s.val.2) s.property.2), by simp⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · apply DimensionSplit.ext
      simp
    · apply DimensionSplit.ext
      simp
  right_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · apply DimensionSplit.ext
      simp
    · apply DimensionSplit.ext
      simp

@[simp] lemma transposeDimensionGrid_first_left (d e α β : I → ℕ)
    (s : RowDimensionGrid d e α β) :
    left (transposeDimensionGrid d e α β s).val.1 = left s.val.1 := rfl

@[simp] lemma transposeDimensionGrid_first_right (d e α β : I → ℕ)
    (s : RowDimensionGrid d e α β) :
    right (transposeDimensionGrid d e α β s).val.1 = left s.val.2 :=
  right_ofPair _ _ s.property.1

@[simp] lemma transposeDimensionGrid_second_left (d e α β : I → ℕ)
    (s : RowDimensionGrid d e α β) :
    left (transposeDimensionGrid d e α β s).val.2 = right s.val.1 := rfl

@[simp] lemma transposeDimensionGrid_second_right (d e α β : I → ℕ)
    (s : RowDimensionGrid d e α β) :
    right (transposeDimensionGrid d e α β s).val.2 = right s.val.2 :=
  right_ofPair _ _ s.property.2

attribute [local instance] Classical.propDecidable

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_WeightedTorusSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceZeroUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]

omit [Fintype I] [DecidableEq I] in
lemma split_heq {d e : I → ℕ} {s : DimensionSplit d} {t : DimensionSplit e}
    (H : d=e) (hs : s.left=t.left) : HEq s t := by
  cases H
  exact heq_of_eq (DimensionSplit.ext hs)

def splitSliceEquiv (n : ℕ) :
    (Σ d : Slice w n,DimensionSplit d.val) ≃
      {p : (I→ℕ)×(I→ℕ) // weight w p.1+weight w p.2=n} where
  toFun x:=⟨(x.2.left,x.2.right),by rw [←map_add,DimensionSplit.left_add_right]; exact x.1.property⟩
  invFun p:=⟨⟨p.val.1+p.val.2,by rw [map_add,p.property]⟩,DimensionSplit.ofPair _ _ rfl⟩
  left_inv x:=by
    apply Sigma.ext (Subtype.ext (DimensionSplit.left_add_right x.2))
    exact split_heq (DimensionSplit.left_add_right x.2) rfl
  right_inv p:=by apply Subtype.ext; simp

variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

def convolution (f g : (I→ℕ) → R) (d : I→ℕ) : R :=
  ∑s : DimensionSplit d,f s.left*g s.right*↑(v^(Ω (P s.left) (P s.right)))

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_LaurentKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
namespace SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def separateSeries (d e : I → ℕ) :
    LaurentSeries (MvPolynomial (CellVars d e) ℚ) →ₗ[ℚ] LaurentSeries (S d ⊗[ℚ] S e) :=
  mapLinear (separateTensor d e)

lemma realize_injective (d e : I → ℕ) :
    Function.Injective (mapRing (R:=S d ⊗[ℚ] S e) (S:=MvPolynomial (CellVars d e) ℚ) (tensorValueAlg d e).toRingHom) :=
  mapRing_injective _ (tensorValue_injective d e)

end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialCoeffLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma eulerForm_add_left (a : I → I → ℕ) (d e f : I → ℕ) :
    eulerForm a (d+e) f=eulerForm a d f+eulerForm a e f := by
  simp only [eulerForm,Pi.add_apply,Nat.cast_add,add_mul,mul_add,Finset.sum_add_distrib]
  ring

omit [DecidableEq I] in
lemma eulerForm_add_right (a : I → I → ℕ) (d e f : I → ℕ) :
    eulerForm a d (e+f)=eulerForm a d e+eulerForm a d f := by
  simp only [eulerForm,Pi.add_apply,Nat.cast_add,mul_add,Finset.sum_add_distrib]
  ring

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ShuffleUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

def emptyLeftCut (s : Pack (A:=A)) : PackConvolution.Cut s :=
  fun i=>⟨(∅,s i),by simp⟩

def emptyRightCut (s : Pack (A:=A)) : PackConvolution.Cut s :=
  fun i=>⟨(s i,∅),by simp⟩

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
lemma eq_emptyLeftCut {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (h : left p=fun _=>∅) : p=emptyLeftCut s := by
  funext i
  apply Subtype.ext
  apply Prod.ext
  · exact congrFun h i
  · have hh := (p i).property.2
    change (p i).val.1 ∪ (p i).val.2=s i at hh
    have hi : (p i).val.1=∅ := congrFun h i
    simpa only [emptyLeftCut,hi,Finset.empty_union] using hh

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
lemma eq_emptyRightCut {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (h : right p=fun _=>∅) : p=emptyRightCut s := by
  funext i
  apply Subtype.ext
  apply Prod.ext
  · have hh := (p i).property.2
    change (p i).val.1 ∪ (p i).val.2=s i at hh
    have hi : (p i).val.2=∅ := congrFun h i
    simpa only [emptyRightCut,hi,Finset.union_empty] using hh
  · exact congrFun h i

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNSlope
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
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
variable {I : Type u} [Fintype I]
variable (a : I → I → ℕ)
  (κ : I → ℤ)
  (c η : I → ℝ)
  (hc : ∀i,0 < c i)

def slopeValue (θ : ℝ) (d : I → ℕ) : ℝ := mass η d-θ*mass c d
@[simp] lemma slopeValue_zero (θ : ℝ) : slopeValue c η θ 0=0 := by simp [slopeValue]

end
end ElementaryPositivity.RawShuffle

end

end OAI
end


