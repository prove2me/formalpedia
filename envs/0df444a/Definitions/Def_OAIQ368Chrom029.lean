-- Prove2me | Definitions.Def_OAIQ368Chrom029
-- name    : OAIQ368Chrom029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:27:20.094595+00:00
-- url     : https://prove2.me/theorems/6be85f65-80d8-4ce2-9088-2eaa1cd3a89a
-- title:
--   Definitions bundle OAIQ368Chrom029 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 8 definitions and 3 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.dimensionColumnLeadingB`, `OAI.ElementaryPositivity.RawShuffle.dimensionLeadingB`, `OAI.ElementaryPositivity.RawShuffle.dimensionRowLeadingB`, `OAI.ElementaryPositivity.RawShuffle.gridLeadingB`, `OAI.ElementaryPositivity.RawShuffle.gridShapeLeadingB`, `OAI.ElementaryPositivity.RawShuffle.slopeColumnEquiv`, `OAI.ElementaryPositivity.RawShuffle.unitalSeparationConstant`, `OAI.ElementaryPositivity.RawShuffle.unitalTensorFiltrationCast`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_CellLeadingSum`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CellLeadingSum.lean), [`Chromatic_Shuffle_DimensionColumnLeading`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/DimensionColumnLeading.lean), [`Chromatic_Shuffle_SignedCoproductGridGrade`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/SignedCoproductGridGrade.lean), [`Chromatic_Shuffle_SignedTensorGradeProduct`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/SignedTensorGradeProduct.lean), [`Chromatic_Shuffle_SlopeGridSum`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/SlopeGridSum.lean), [`Chromatic_Shuffle_UnitalGrade`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/UnitalGrade.lean), [`Chromatic_Shuffle_UnitalGradeAlgebra`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/UnitalGradeAlgebra.lean), [`Chromatic_Walls_Grade`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/Grade.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom027` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom030`; the statement `OAI.ElementaryPositivity.RawShuffle.unitalSeparationConstant_shuffle_leading_all`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom027

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellLeadingSum
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open ElementaryPositivity.PackConvolution HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] clearBTensorB clearBTensorBA Classical.propDecidable

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
noncomputable local instance cellLeadTensorN_r8cb8f7_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) :=
  (clearBTensorB a μ d e).toNonUnitalNonAssocSemiring
noncomputable def gridShapeLeadingB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p))
    (hon : CellsOnSlope c η θ (fun i=>(u i).val) (shapeComplement u)
      (fun i=>(v i).val) (shapeComplement v)) : B a (slope c η) α⊗[ℚ]B a (slope c η) β :=
  castBTensor a (slope c η) ((shape_add_complement u).trans (realization_card R))
    ((shape_add_complement v).trans (realization_card T))
      (cellLeadingB a c η hc θ _ _ _ _ hon f g)

noncomputable def gridLeadingB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization α (left p)) (T : Realization β (right p)) :
    B a (slope c η) α⊗[ℚ]B a (slope c η) β :=
  ∑ u : CutShape (left p),∑ v : CutShape (right p),
    if hon : CellsOnSlope c η θ (fun i=>(u i).val) (shapeComplement u)
      (fun i=>(v i).val) (shapeComplement v)
    then gridShapeLeadingB a c η hc θ f g p R T u v hon else 0

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalGrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
open SeparationInfinity
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def unitalSeparationConstant (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) :
    B a (slope c η) (d+e) →ₗ[ℚ] B a (slope c η) d⊗[ℚ]B a (slope c η) e where
  toFun f := (unitalSeparationSeries a c η hc hs f).coeff 0
  map_add' f g := by rw [map_add,HahnSeries.coeff_add]
  map_smul' r f := by rw [map_smul,HahnSeries.coeff_smul]; rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SignedCoproductGridGrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def dimensionRowLeadingB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    (u : DimensionSplit α) (v : DimensionSplit β) : B a (slope c η) α⊗[ℚ]B a (slope c η) β :=
  if hon : CellsOnSlope c η θ (left u) (right u) (left v) (right v) then
    castBTensor a (slope c η) (left_add_right u) (left_add_right v)
      (cellLeadingB a c η hc θ (left u) (right u) (left v) (right v) hon f g)
  else 0

noncomputable def dimensionLeadingB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e) : B a (slope c η) α⊗[ℚ]B a (slope c η) β :=
  ∑ u : DimensionSplit α,∑ v : DimensionSplit β,dimensionRowLeadingB a c η hc θ f g u v

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_DimensionColumnLeading
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def dimensionColumnLeadingB (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    (s : ColumnDimensionGrid d e α β) : B a (slope c η) α⊗[ℚ]B a (slope c η) β :=
  if hon : CellsOnSlope c η θ (left s.val.1) (left s.val.2)
      (right s.val.1) (right s.val.2) then
    castBTensor a (slope c η) s.property.1 s.property.2
      (cellLeadingB a c η hc θ _ _ _ _ hon f g)
  else 0

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_Grade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma unitalSourceFiltration_zero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (W : ℤ) : unitalSourceFiltration a c η hc θ (0 : I → ℕ) W=
      if W≤0 then ⊤ else ⊥ := by
  unfold unitalSourceFiltration
  exact ite_eq_left (rfl : (0 : I → ℕ)=0)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalGradeAlgebra
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma shuffleBUnit_assoc (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e b : I → ℕ) (hd : OnSlopeOrZero c η θ d)
    (he : OnSlopeOrZero c η θ e) (hb : OnSlopeOrZero c η θ b)
    (f : B a (slope c η) d) (g : B a (slope c η) e) (h : B a (slope c η) b) :
    castB a (slope c η) (add_assoc d e b)
      (shuffleBUnit a c η hc (d+e) b ((hd.add hc he).compatible hb)
        (shuffleBUnit a c η hc d e (hd.compatible he) f g) h)=
    shuffleBUnit a c η hc d (e+b) (hd.compatible (he.add hc hb)) f
      (shuffleBUnit a c η hc e b (he.compatible hb) g h) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    induction g using Submodule.Quotient.induction_on with
    | H g =>
      induction h using Submodule.Quotient.induction_on with
      | H h =>
        change castB a (slope c η) (add_assoc d e b)
          (quotientAlg a (slope c η) ((d+e)+b) (shufflePolynomial a (shufflePolynomial a f g) h))=
          quotientAlg a (slope c η) (d+(e+b)) (shufflePolynomial a f (shufflePolynomial a g h))
        rw [castB_mk,shufflePolynomial_assoc]

lemma unitalFiltrationCast_val (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e : I → ℕ} {U V : ℤ} (h : d=e) (k : U=V)
    (f : unitalSourceFiltration a c η hc θ d U) :
    (unitalFiltrationCast a c η hc θ h k f).val=castB a (slope c η) h f.val := by
  subst e
  subst V
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SignedTensorGradeProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
open DimensionSplit SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def unitalTensorFiltrationCast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e d' e' : I → ℕ} {U V : ℤ}
    (h : d=d') (k : e=e') (w : U=V) :
    unitalSourceTensorFiltration a c η hc θ d e U ≃ₗ[ℚ]
      unitalSourceTensorFiltration a c η hc θ d' e' V := by
  subst d'; subst e'; subst V
  exact LinearEquiv.refl _ _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SlopeGridSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def slopeColumnEquiv (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
    (d e : I → ℕ) :
    (Σ t : SlopeSplit c η hc θ (d+e),
      SlopeColumnGrid c η θ d e (left t.val) (right t.val)) ≃
      SlopeSplit c η hc θ d × SlopeSplit c η hc θ e :=
  Equiv.ofBijective
    (fun z=>(⟨z.2.val.val.1,⟨z.2.property.1,z.2.property.2.2.1⟩⟩,
      ⟨z.2.val.val.2,⟨z.2.property.2.1,z.2.property.2.2.2⟩⟩)) (by
    constructor
    · rintro ⟨t,s⟩ ⟨t',s'⟩ h
      have h₁ : s.val.val.1=s'.val.val.1 := congrArg (fun z=>z.1.val) h
      have h₂ : s.val.val.2=s'.val.val.2 := congrArg (fun z=>z.2.val) h
      have ht : t=t' := by
        apply Subtype.ext
        apply DimensionSplit.ext
        exact s.val.property.1.symm.trans ((congrArg₂ (fun p q=>left p+left q) h₁ h₂).trans s'.val.property.1)
      subst t'
      have hs : s=s' := Subtype.ext (Subtype.ext (Prod.ext h₁ h₂))
      exact congrArg (fun z=>Sigma.mk t z) hs
    · rintro ⟨p,q⟩
      have hsum : (left p.val+left q.val)+(right p.val+right q.val)=d+e := by
        calc
          _=(left p.val+right p.val)+(left q.val+right q.val) := by abel
          _=_ := by rw [left_add_right,left_add_right]
      let t : SlopeSplit c η hc θ (d+e) :=
        ⟨ofPair (left p.val+left q.val) (right p.val+right q.val) hsum,by
          simpa only [left_ofPair,right_ofPair] using
            And.intro (p.property.1.add hc q.property.1) (p.property.2.add hc q.property.2)⟩
      let s : SlopeColumnGrid c η θ d e (left t.val) (right t.val) :=
        ⟨⟨(p.val,q.val),by simp [t]⟩,p.property.1,q.property.1,p.property.2,q.property.2⟩
      exact ⟨⟨t,s⟩,rfl⟩)

end ElementaryPositivity.RawShuffle

end

end OAI
end


