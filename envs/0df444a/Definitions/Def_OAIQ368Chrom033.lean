-- Prove2me | Definitions.Def_OAIQ368Chrom033
-- name    : OAIQ368Chrom033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:23:30.964201+00:00
-- url     : https://prove2.me/theorems/1384bd72-fd7c-4dd8-b880-2aa21870c64d
-- title:
--   Definitions bundle OAIQ368Chrom033 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 53 definitions and 7 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.columnFourAlgebra`, `OAI.ElementaryPositivity.RawShuffle.columnTensorAlgebra`, `OAI.ElementaryPositivity.RawShuffle.columnTensorRing`, `OAI.ElementaryPositivity.RawShuffle.commonTaylorTensor`, `OAI.ElementaryPositivity.RawShuffle.crossingColumnAlg`, `OAI.ElementaryPositivity.RawShuffle.crossingColumnVars`, `OAI.ElementaryPositivity.RawShuffle.firstColumnAlg`, `OAI.ElementaryPositivity.RawShuffle.firstColumnBAlg`, `OAI.ElementaryPositivity.RawShuffle.fourAffine`, `OAI.ElementaryPositivity.RawShuffle.fourClearingUnit`, `OAI.ElementaryPositivity.RawShuffle.fourCrossAffineUnit`, `OAI.ElementaryPositivity.RawShuffle.fourCrossingInverseUnit`, `OAI.ElementaryPositivity.RawShuffle.fourFirstInverseUnit`, `OAI.ElementaryPositivity.RawShuffle.fourForwardDifference`, `OAI.ElementaryPositivity.RawShuffle.fourRelativeRaw`, `OAI.ElementaryPositivity.RawShuffle.fourRelativeTaylor`, `OAI.ElementaryPositivity.RawShuffle.fourRowsInverseUnit`, `OAI.ElementaryPositivity.RawShuffle.fourSecondInverseUnit`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue`, `OAI.ElementaryPositivity.RawShuffle.fourTensorKernelRHS`, `OAI.ElementaryPositivity.RawShuffle.fourTotalInverseUnit`, `OAI.ElementaryPositivity.RawShuffle.kernelFourAlg`, `OAI.ElementaryPositivity.RawShuffle.kernelFourRing`, `OAI.ElementaryPositivity.RawShuffle.kernelTensorAlg`, `OAI.ElementaryPositivity.RawShuffle.kernelTensorRing`, `OAI.ElementaryPositivity.RawShuffle.mappedInverseKernel`, `OAI.ElementaryPositivity.RawShuffle.naturalTaylorFourAlg`, `OAI.ElementaryPositivity.RawShuffle.naturalTaylorFourRing`, `OAI.ElementaryPositivity.RawShuffle.naturalTaylorTensorAlg`, `OAI.ElementaryPositivity.RawShuffle.naturalTaylorTensorRing`, `OAI.ElementaryPositivity.RawShuffle.projectionFourSAlgebra`, `OAI.ElementaryPositivity.RawShuffle.projectionFourSCommRing`, `OAI.ElementaryPositivity.RawShuffle.projectionFourSNonUnitalNonAssocSemiring`, `OAI.ElementaryPositivity.RawShuffle.projectionTensorSAlgebra`, `OAI.ElementaryPositivity.RawShuffle.projectionTensorSCommRing`, `OAI.ElementaryPositivity.RawShuffle.projectionTensorSNonUnitalNonAssocSemiring`, `OAI.ElementaryPositivity.RawShuffle.quotientFourSemiring`, `OAI.ElementaryPositivity.RawShuffle.restrictRows`, `OAI.ElementaryPositivity.RawShuffle.rowSplitEquiv`, `OAI.ElementaryPositivity.RawShuffle.secondColumnAlg` and 13 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_GradedBuilders`, `Chromatic_GradedAlgebra_LaurentRectangularKernel`, `Chromatic_Shuffle_ColumnTaylor`, `Chromatic_Shuffle_CrossKernelExplicit`, `Chromatic_Shuffle_FourAffineKernel`, `Chromatic_Shuffle_FourColumns`, `Chromatic_Shuffle_FourTensorKernel`, `Chromatic_Shuffle_GlobalTensorGradeProduct`, `Chromatic_Shuffle_GridQuotient`, `Chromatic_Shuffle_ShuffleProjection`, `Chromatic_Shuffle_TensorColumnNaturality`, `Chromatic_Shuffle_TensorColumnSeriesFiltration`, `Chromatic_Shuffle_TensorMiddleEnd`, `Chromatic_Shuffle_UnitalGradeAlgebra`, `Chromatic_Walls_DirectSumBilinear`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom034`, `OAIQ368Chrom036` and `OAIQ368Chrom037`; the statements `OAI.ElementaryPositivity.RawShuffle.fourGrid_relativeTaylor_factor`, `OAI.ElementaryPositivity.RawShuffle.fourGrid_taylor_factor`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_cross`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_kernelRHS_val`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_second`, `OAI.ElementaryPositivity.RawShuffle.fourTaylor_column_product` and `OAI.ElementaryPositivity.RawShuffle.fourTensorKernel_cancellation`; the proofs of `OAI.ElementaryPositivity.RawShuffle.fourGrid_relativeTaylor_factor`, `OAI.ElementaryPositivity.RawShuffle.fourGrid_taylor_factor`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_cross`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_kernelRHS_val`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_second`, `OAI.ElementaryPositivity.RawShuffle.fourTaylor_column_product`, `OAI.ElementaryPositivity.RawShuffle.fourTensorKernel_cancellation` and `OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion_injective`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom023

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_GradedBuilders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity

@[instance_reducible]
noncomputable def gradedRingOfAddLaws {J : Type*} [AddMonoid J] {A : J → Type*}
    [∀ j,AddCommGroup (A j)] [GradedMonoid.GMonoid A]
    (hzr : ∀ {i j} (x : A i),GradedMonoid.GMul.mul x (0 : A j)=0)
    (hzl : ∀ {i j} (x : A j),GradedMonoid.GMul.mul (0 : A i) x=0)
    (har : ∀ {i j} (x : A i) (y z : A j),
      GradedMonoid.GMul.mul x (y+z)=GradedMonoid.GMul.mul x y+GradedMonoid.GMul.mul x z)
    (hal : ∀ {i j} (x y : A i) (z : A j),
      GradedMonoid.GMul.mul (x+y) z=GradedMonoid.GMul.mul x z+GradedMonoid.GMul.mul y z) :
    DirectSum.GRing A where
  toGMonoid := inferInstance
  mul_zero := hzr
  zero_mul := hzl
  mul_add := har
  add_mul := hal
  natCast n := n • GradedMonoid.GOne.one
  natCast_zero := zero_nsmul _
  natCast_succ n := by rw [add_nsmul,one_nsmul]
  intCast n := n • GradedMonoid.GOne.one
  intCast_ofNat n := by simp only [natCast_zsmul]
  intCast_negSucc_ofNat n := negSucc_zsmul _ _

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentRectangularKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RectangularKernel
variable {I : Type*} [Fintype I]
variable {G : Type*} [CommGroup G]

noncomputable def rectangular {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b : I → I → ℤ) (v : ∀ i j,L i → R j → G) : G :=
  ∏ i,∏ j,∏ x : L i,∏ y : R j,v i j x y ^ b i j

end ElementaryPositivity.RectangularKernel

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CrossKernelExplicit
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

noncomputable def fourForwardDifference (d₁ e₁ d₂ e₂ : I → ℕ)
    (i j : I) (x : Fin (d₁ i)⊕Fin (e₁ i)) (y : Fin (d₂ j)⊕Fin (e₂ j)) :
    MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ :=
  X (Sum.inr ((Equiv.sigmaSumDistrib _ _) ⟨j,y⟩)) -
    X (Sum.inl ((Equiv.sigmaSumDistrib _ _) ⟨i,x⟩))

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourAffineKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def fourRelativeRaw (d₁ e₁ d₂ e₂ : I → ℕ) :
    MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ →ₐ[ℚ]
      Polynomial (MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) :=
  aeval (Sum.elim (fun x=>Polynomial.C (X (Sum.inl x))+Polynomial.X)
    (fun y=>Polynomial.C (X (Sum.inr y))))

noncomputable def fourAffine (d₁ e₁ d₂ e₂ : I → ℕ)
    (i j : I) (x : Fin (d₁ i)⊕Fin (e₁ i)) (y : Fin (d₂ j)⊕Fin (e₂ j)) :=
  affineUnit (fourForwardDifference d₁ e₁ d₂ e₂ i j x y)

noncomputable def fourClearingUnit (d₁ e₁ d₂ e₂ : I → ℕ) :=
  rectangular (fun i j : I=>if i=j then 1 else 0) (fourAffine d₁ e₁ d₂ e₂)

noncomputable def fourTotalInverseUnit (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :=
  rectangular (SeparationInfinity.inverseExponent a) (fourAffine d₁ e₁ d₂ e₂)

noncomputable def fourCrossAffineUnit (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :=
  (-1 : (LaurentSeries (MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ))ˣ) ^ (∑ i,e₁ i*d₂ i) *
    rectangular (fun i j : I=>if i=j then 1 else 0)
      (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inl x) (.inl y)) *
    rectangular (fun i j : I=>if i=j then 1 else 0)
      (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inr y)) *
    rectangular (fun i j=>(a i j:ℤ))
      (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inl x) (.inr y)) *
    rectangular (fun i j=>(a i j:ℤ))
      (fun i j x y=>-fourAffine d₁ e₁ d₂ e₂ j i (.inr y) (.inl x))

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourColumns
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance columnTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance columnTensorAlgebra (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance columnFourRing_r9efac5_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance columnFourAlgebra (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

noncomputable def firstColumnAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    S d₁⊗[ℚ] S d₂ →ₐ[ℚ] (S d₁⊗[ℚ] S e₁)⊗[ℚ](S d₂⊗[ℚ] S e₂) :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeLeft

noncomputable def secondColumnAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    S e₁⊗[ℚ] S e₂ →ₐ[ℚ] (S d₁⊗[ℚ] S e₁)⊗[ℚ](S d₂⊗[ℚ] S e₂) :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeRight

noncomputable def crossingColumnAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    S e₁⊗[ℚ] S d₂ →ₐ[ℚ] (S d₁⊗[ℚ] S e₁)⊗[ℚ](S d₂⊗[ℚ] S e₂) :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeLeft

def crossingColumnVars (d₁ e₁ d₂ e₂ : I → ℕ) :
    CellVars e₁ d₂ → CellVars d₁ e₁⊕CellVars d₂ e₂ :=
  Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inl)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.TensorPolynomials
open scoped TensorProduct
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]

noncomputable def tensorPolynomial (f : A →ₐ[ℚ] Polynomial A) (g : B →ₐ[ℚ] Polynomial B) :
    A⊗[ℚ]B →ₐ[ℚ] Polynomial (A⊗[ℚ]B) :=
  let L := (Polynomial.mapAlgHom (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A⊗[ℚ]B)).comp f
  let R := (Polynomial.mapAlgHom (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A⊗[ℚ]B)).comp g
  Algebra.TensorProduct.lift (S:=ℚ) L R (fun x y=>mul_comm (L x) (R y))

end ElementaryPositivity.TensorPolynomials

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.CommonTranslation ElementaryPositivity.TensorPolynomials
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance taylorTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance taylorTensorAlgebra (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance taylorFourRing_r9efac5_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance taylorFourAlgebra (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

noncomputable local instance taylorTensorNonUnital_r9efac5_1 (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (S d⊗[ℚ]S e) := (taylorTensorRing d e).toNonUnitalNonAssocSemiring
noncomputable def commonTaylorTensor (d e : I → ℕ) :
    S d⊗[ℚ]S e →ₐ[ℚ] Polynomial (S d⊗[ℚ]S e) :=
  tensorPolynomial (taylorS d) (taylorS e)

noncomputable def fourRelativeTaylor (d₁ e₁ d₂ e₂ : I → ℕ) :
    (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂) →ₐ[ℚ]
      Polynomial ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  tensorPolynomial (commonTaylorTensor d₁ e₁) Polynomial.CAlgHom

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ShuffleProjection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open ElementaryPositivity.LaurentAtInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance projectionTensorSCommRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance projectionTensorSAlgebra (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance

noncomputable local instance projectionFourSCommRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance projectionFourSAlgebra (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

noncomputable local instance projectionTensorSNonUnitalNonAssocSemiring (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (S d⊗[ℚ]S e) := (projectionTensorSCommRing d e).toNonUnitalNonAssocSemiring
noncomputable local instance projectionFourSNonUnitalNonAssocSemiring (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonUnitalNonAssocSemiring ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  (projectionFourSCommRing d₁ e₁ d₂ e₂).toNonUnitalNonAssocSemiring

noncomputable def restrictRows (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    S (d₁+e₁)⊗[ℚ]S (d₂+e₂) →ₐ[ℚ] (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂) :=
  Algebra.TensorProduct.map (restrictTensorAlg A) (restrictTensorAlg B)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def rowSplitEquiv {d₁ e₁ d₂ e₂ : I → ℕ}
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    CellVars (d₁+e₁) (d₂+e₂) ≃ CellVars d₁ e₁⊕CellVars d₂ e₂ :=
  Equiv.sumCongr (cutSplit A).symm (cutSplit B).symm

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ColumnTaylor
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.CommonTranslation ElementaryPositivity.LaurentAtInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance naturalTaylorTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance naturalTaylorTensorAlg (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance naturalTaylorFourRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance naturalTaylorFourAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourTensorKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance kernelTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance kernelTensorDistrib_r9efac5_1 (d e : I → ℕ) :
    DistribSMul (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) where
  smul_add := mul_add
noncomputable local instance kernelTensorAlg (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance kernelFourRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance kernelFourAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorDistrib
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelFourRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelFourAlg
noncomputable def mappedInverseKernel {R : Type*} [CommRing R] [Algebra ℚ R]
    (a : I → I → ℕ) (d e : I → ℕ) (f : S d⊗[ℚ]S e →ₐ[ℚ] R) : (LaurentSeries R)ˣ :=
  Units.map (mapRing f.toRingHom).toMonoidHom (SeparationInfinity.inverseKernelUnit a d e)

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorSelf
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorNonUnital
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelFourNonUnital
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelSeriesRing
noncomputable def fourRowsInverseUnit (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) : (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))ˣ :=
  mappedInverseKernel a (d₁+e₁) (d₂+e₂) (restrictRows d₁ e₁ d₂ e₂ A B)

noncomputable def fourFirstInverseUnit (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))ˣ :=
  mappedInverseKernel a d₁ d₂ (firstColumnAlg d₁ e₁ d₂ e₂)

noncomputable def fourSecondInverseUnit (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))ˣ :=
  mappedInverseKernel a e₁ e₂ (secondColumnAlg d₁ e₁ d₂ e₂)

noncomputable def fourCrossingInverseUnit (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))ˣ :=
  mappedInverseKernel a e₁ d₂ (crossingColumnAlg d₁ e₁ d₂ e₂)

noncomputable def fourSeriesValue (d₁ e₁ d₂ e₂ : I → ℕ) :
    LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) →+*
      LaurentSeries (MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) :=
  mapRing (fourValueAlg d₁ e₁ d₂ e₂).toRingHom

noncomputable def fourTensorKernelRHS (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))ˣ :=
  (-1)^eulerForm a d₂ e₁ *
    (fourFirstInverseUnit a d₁ e₁ d₂ e₂ * fourSecondInverseUnit a d₁ e₁ d₂ e₂ *
      (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
        (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹))

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GridQuotient
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TensorColumns
open scoped TensorProduct
variable {K A B C D : Type*} [CommRing K]
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K D]

noncomputable def first : A⊗[K]B →ₐ[K] (A⊗[K]C)⊗[K](B⊗[K]D) :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeLeft
noncomputable def second : C⊗[K]D →ₐ[K] (A⊗[K]C)⊗[K](B⊗[K]D) :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeRight

end ElementaryPositivity.TensorColumns

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorColumnSeriesFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TensorColumns
open scoped TensorProduct
open ElementaryPositivity.LinearDetection ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {A B C D : Type*}
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra ℚ A] [Algebra ℚ B] [Algebra ℚ C] [Algebra ℚ D]

noncomputable def seriesProduct (f : LaurentSeries (A⊗[ℚ]B)) (g : LaurentSeries (C⊗[ℚ]D)) :
    LaurentSeries ((A⊗[ℚ]C)⊗[ℚ](B⊗[ℚ]D)) :=
  mapRing (first (K:=ℚ) (A:=A) (B:=B) (C:=C) (D:=D)).toRingHom f *
    mapRing (second (K:=ℚ) (A:=A) (B:=B) (C:=C) (D:=D)).toRingHom g

end ElementaryPositivity.TensorColumns

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorColumnNaturality
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.LinearDetection
open ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing
attribute [local instance] cellSepTensorSemiring cellSepTensorNonAssoc cellSepFourSemiring cellSepFourNonAssoc cellSepFourModule
attribute [local instance] braidFourTensor braidFourTensorAlg braidFourRing braidFourAlg
attribute [local instance] braidFourTensorN braidFourTensorM braidFourN braidFourM

noncomputable local instance quotientFourSemiring (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d₁ e₁ d₂ e₂ : I → ℕ) :
    Semiring ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) :=
  (braidFourRing a μ d₁ e₁ d₂ e₂).toSemiring

noncomputable local instance quotientFourNonAssoc_r9efac5_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonAssocSemiring ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) :=
  (braidFourRing a μ d₁ e₁ d₂ e₂).toNonAssocSemiring
noncomputable def firstColumnBAlg (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    B a μ d₁⊗[ℚ]B a μ d₂ →ₐ[ℚ](B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂) :=
  ElementaryPositivity.TensorColumns.first
noncomputable def secondColumnBAlg (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    B a μ e₁⊗[ℚ]B a μ e₂ →ₐ[ℚ](B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂) :=
  ElementaryPositivity.TensorColumns.second

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalGradeAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma slopeZero (c η : I → ℝ) (θ : ℝ) : OnSlopeOrZero c η θ (0 : I → ℕ) := Or.inl rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_DirectSumBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open scoped DirectSum
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable (M : ι → Type*) (N : κ → Type*)
variable [∀ i,AddCommGroup (M i)] [∀ i,Module ℚ (M i)]
variable [∀ j,AddCommGroup (N j)] [∀ j,Module ℚ (N j)]
variable (P : Type*) [AddCommGroup P] [Module ℚ P]

noncomputable def directSumBilinear (f : ∀ i j,M i →ₗ[ℚ] N j →ₗ[ℚ] P) :
    (⨁ i,M i) →ₗ[ℚ] (⨁ j,N j) →ₗ[ℚ] P :=
  DirectSum.toModule ℚ ι ((⨁ j,N j) →ₗ[ℚ] P) (fun i=>
    { toFun := fun x=>DirectSum.toModule ℚ κ P (fun j=>f i j x)
      map_add' := by
        intro x y
        apply DirectSum.linearMap_ext
        intro j
        ext z
        simp only [LinearMap.comp_apply,DirectSum.toModule_lof,LinearMap.add_apply,map_add]
      map_smul' := by
        intro r x
        apply DirectSum.linearMap_ext
        intro j
        ext z
        simp only [LinearMap.comp_apply,DirectSum.toModule_lof,LinearMap.smul_apply,map_smul]
        rfl })

lemma directSumBilinear_lof (f : ∀ i j,M i →ₗ[ℚ] N j →ₗ[ℚ] P)
    (i : ι) (j : κ) (x : M i) (y : N j) :
    directSumBilinear M N P f (DirectSum.lof ℚ ι M i x) (DirectSum.lof ℚ κ N j y)=f i j x y := by
  simp only [directSumBilinear,DirectSum.toModule_lof,LinearMap.coe_mk,AddHom.coe_mk]

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorMiddleEnd
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open scoped TensorProduct
variable {A B C D : Type*}
variable [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
variable [AddCommGroup C] [Module ℚ C] [AddCommGroup D] [Module ℚ D]

noncomputable def middleGroup : (A⊗[ℚ]B)⊗[ℚ](C⊗[ℚ]D) ≃ₗ[ℚ] (A⊗[ℚ](B⊗[ℚ]C))⊗[ℚ]D :=
  (TensorProduct.assoc ℚ (A⊗[ℚ]B) C D).symm.trans
    (TensorProduct.congr (TensorProduct.assoc ℚ A B C) (LinearEquiv.refl ℚ D))

lemma middleGroup_tmul (a : A) (b : B) (c : C) (d : D) :
    middleGroup ((a⊗ₜ[ℚ]b)⊗ₜ[ℚ](c⊗ₜ[ℚ]d))=(a⊗ₜ[ℚ](b⊗ₜ[ℚ]c))⊗ₜ[ℚ]d := rfl

lemma middleGroup_symm_tmul (a : A) (b : B) (c : C) (d : D) :
    middleGroup.symm ((a⊗ₜ[ℚ](b⊗ₜ[ℚ]c))⊗ₜ[ℚ]d)=(a⊗ₜ[ℚ]b)⊗ₜ[ℚ](c⊗ₜ[ℚ]d) := rfl

noncomputable def middleEnd (f : B⊗[ℚ]C →ₗ[ℚ] B⊗[ℚ]C) :
    (A⊗[ℚ]B)⊗[ℚ](C⊗[ℚ]D) →ₗ[ℚ] (A⊗[ℚ]B)⊗[ℚ](C⊗[ℚ]D) :=
  middleGroup.symm.toLinearMap.comp
    ((TensorProduct.map (TensorProduct.map (LinearMap.id : A →ₗ[ℚ] A) f)
      (LinearMap.id : D →ₗ[ℚ] D)).comp middleGroup.toLinearMap)

lemma middleEnd_scalar (f : B⊗[ℚ]C →ₗ[ℚ] B⊗[ℚ]C)
    (a : A) (b : B) (c : C) (d : D) (r : ℚ) (h : f (b⊗ₜ[ℚ]c)=r•(b⊗ₜ[ℚ]c)) :
    middleEnd f ((a⊗ₜ[ℚ]b)⊗ₜ[ℚ](c⊗ₜ[ℚ]d))=r•((a⊗ₜ[ℚ]b)⊗ₜ[ℚ](c⊗ₜ[ℚ]d)) := by
  change middleGroup.symm ((TensorProduct.map (TensorProduct.map LinearMap.id f) LinearMap.id)
    (middleGroup ((a⊗ₜ[ℚ]b)⊗ₜ[ℚ](c⊗ₜ[ℚ]d))))=_
  rw [middleGroup_tmul,TensorProduct.map_tmul,TensorProduct.map_tmul,h]
  change middleGroup.symm ((a⊗ₜ[ℚ](r•(b⊗ₜ[ℚ]c)))⊗ₜ[ℚ]d)=_
  rw [TensorProduct.tmul_smul,←TensorProduct.smul_tmul',map_smul,middleGroup_symm_tmul]

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalTensorGradeProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

omit [DecidableEq I] in
lemma slopeDimensions_onSlope (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
    (d : slopeDimensions c η hc θ) : OnSlopeOrZero c η θ d.val := d.property

omit [DecidableEq I] in
lemma slopeDimensions_cellsOnSlope (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
    (d₁ e₁ d₂ e₂ : slopeDimensions c η hc θ) :
    OnSlopeOrZero c η θ d₁.val ∧ OnSlopeOrZero c η θ e₁.val ∧
      OnSlopeOrZero c η θ d₂.val ∧ OnSlopeOrZero c η θ e₂.val :=
  ⟨d₁.property,e₁.property,d₂.property,e₂.property⟩

end ElementaryPositivity.RawShuffle

end

end OAI
end


