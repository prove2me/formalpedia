-- Prove2me | Definitions.Def_OAIQ368Chrom035
-- name    : OAIQ368Chrom035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:42:38.867029+00:00
-- url     : https://prove2.me/theorems/9c6ddd97-aa59-4c7e-891a-c4339844e420
-- title:
--   Definitions bundle OAIQ368Chrom035 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 5 definitions, 4 instances and 20 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.columnFiltrationTerm`, `OAI.ElementaryPositivity.RawShuffle.columnGradeTerm`, `OAI.ElementaryPositivity.RawShuffle.globalSignedTensorMultiply`, `OAI.ElementaryPositivity.RawShuffle.signedCellGradeMultiply`, `OAI.ElementaryPositivity.RawShuffle.unitalGradeShuffle`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Histories_ShuffleLeafFiltration`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Histories/ShuffleLeafFiltration.lean), [`Chromatic_Histories_TwoLeafDiagonal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Histories/TwoLeafDiagonal.lean), [`Chromatic_Shuffle_AllPairDiagonal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/AllPairDiagonal.lean), [`Chromatic_Shuffle_BothTaylorB`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/BothTaylorB.lean), [`Chromatic_Shuffle_ManyBlockDiagonal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/ManyBlockDiagonal.lean), [`Chromatic_Shuffle_ManyBlockPolynomiality`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/ManyBlockPolynomiality.lean), [`Chromatic_Shuffle_SignedTensorGradeProduct`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/SignedTensorGradeProduct.lean), [`Chromatic_Shuffle_TensorMiddleEnd`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/TensorMiddleEnd.lean), [`Chromatic_Shuffle_TwoTargetFiltration`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/TwoTargetFiltration.lean), [`Chromatic_Shuffle_UnitalGrade`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/UnitalGrade.lean), [`Chromatic_Shuffle_UnitalGradeAlgebra`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/UnitalGradeAlgebra.lean), [`Chromatic_Walls_ShuffleFiltration`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/ShuffleFiltration.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom031`, `OAIQ368Chrom032` and `OAIQ368Chrom034` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom040`; the statement `OAI.ElementaryPositivity.RawShuffle.globalCoproduct_mul`; the proofs of `OAI.ElementaryPositivity.RawShuffle.globalCoproduct_mul`, `OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds`, `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component` and `OAI.ElementaryPositivity.RawShuffle.unitalSeparationConstant_shuffle_leading_all`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom031
import Definitions.Def_OAIQ368Chrom032
import Definitions.Def_OAIQ368Chrom034

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_BothTaylorB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

theorem bothLeading_diagonal_divisible (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (hd : d≠0) (he : e≠0)
    (hdθ : SlopeArithmetic.slope c η d=θ) (heθ : SlopeArithmetic.slope c η e=θ)
    (hsym : eulerForm a d e=eulerForm a e d) (p q W : ℤ)
    (hw : 2*(p+q)+eulerForm a d d+eulerForm a e e=W)
    (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) :
    IndependentCenters.DiagonalDivides (-eulerForm a d e).toNat
      (bothLeading a c η hc (d:=d) (e:=e) (hdθ.trans heθ.symm) p q f) := by
  let : CommRing (Polynomial (B a (SlopeArithmetic.slope c η) d ⊗[ℚ]
    B a (SlopeArithmetic.slope c η) e)) := inferInstance
  apply IndependentCenters.diagonalDivides_of_relative
  rw [bothLeading_relative]
  apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
  intro r
  change Polynomial.X^(-eulerForm a d e).toNat ∣
    relativeLeading a c η hc (hdθ.trans heθ.symm) p q ((taylorB a (SlopeArithmetic.slope c η) (d+e) f).coeff r)
  exact relativeLeading_taylor_divisible a c η hc θ d e hd he hdθ heθ r hsym p q W hw f hf

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ManyBlockDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem pairLeading_diagonal_divisible (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) (θ : ℝ) {d e : I → ℕ}
    (hd : (.leaf d : SplitTree I).OnSlope c η θ)
    (he : (.leaf e : SplitTree I).OnSlope c η θ)
    (hsym : eulerForm a d e = eulerForm a e d)
    (T : SplitTree I) (hT : T.OnSlope c η θ)
    (p q W : ℤ) (k : T.Degrees)
    (hw : 2*(p+q+T.totalDegree k)+eulerForm a d d+eulerForm a e e+T.doubleShift a = W)
    (f : B a (SlopeArithmetic.slope c η) ((d+e)+T.dim))
    (hf : f ∈ sourceFiltration a c η hc θ ((d+e)+T.dim) W) :
    (X (Sum.inl (Sum.inl ())) - X (Sum.inl (Sum.inr ()))) ^ (-eulerForm a d e).toNat ∣
      mapLinear (componentTensor a (SlopeArithmetic.slope c η)
        (.node (.node (.leaf d) (.leaf e)) T) ((p,q),k))
          (centeredRestrictionB a c η hc θ (.node (.node (.leaf d) (.leaf e)) T)
            ⟨⟨hd,he⟩,hT⟩ f) := by
  apply diagonal_dvd_of_relative_coeff
  intro z s hs
  rw [toRelative_mapLinear,centeredRestrictionB_pairRefinement a c η hc θ hd he T hT,
    coeff_mapLinear,coeff_map]
  exact (pairRelativeRefinement_component_coeff a c η hc (hd.2.trans he.2.symm) T s p q k _).trans
    (pairRefinementCoefficient_zero a c η hc θ hd.1 hd.2 he.2 hsym T hT p q W k hw f hf z s hs)

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_TwoLeafDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem twoLeading_diagonal_divisible (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e : I → ℕ}
    (hd : (.leaf d : SplitTree I).OnSlope c η θ)
    (he : (.leaf e : SplitTree I).OnSlope c η θ)
    (hsym : eulerForm a d e=eulerForm a e d) (p q W : ℤ)
    (hw : 2*(p+q)+eulerForm a d d+eulerForm a e e=W)
    (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) :
    (X (Sum.inl ()) - X (Sum.inr ())) ^ (-eulerForm a d e).toNat ∣
      mapLinear (componentTensor a (SlopeArithmetic.slope c η)
        (.node (.leaf d) (.leaf e)) (p,q))
        (centeredRestrictionB a c η hc θ (.node (.leaf d) (.leaf e)) ⟨hd,he⟩ f) := by
  rw [twoLeading_eq a c η hc θ hd he]
  have h := map_dvd ofTwo (bothLeading_diagonal_divisible a c η hc θ d e
    hd.1 he.1 hd.2 he.2 hsym p q W hw f hf)
  change ofTwo ((Polynomial.X-Polynomial.C Polynomial.X)^(-eulerForm a d e).toNat) ∣ _ at h
  simp only [map_pow,map_sub,ofTwo_X,ofTwo_C,Polynomial.toMvPolynomial_X] at h
  apply (pow_dvd_pow_of_dvd _ (-eulerForm a d e).toNat).trans h
  exact ⟨-1, ((mul_neg_one _).trans (neg_sub _ _)).symm⟩

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_AllPairDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

namespace SplitTree

theorem leadingPolynomial_diagonal_divisible (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (k : T.Degrees) (W : ℤ) (hw : 2*T.totalDegree k+T.doubleShift a=W)
    (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : f∈sourceFiltration a c η hc θ T.dim W)
    (i j : T.Centers) (hij : i≠j)
    (hsym : eulerForm a (T.leafDimension i) (T.leafDimension j) =
      eulerForm a (T.leafDimension j) (T.leafDimension i)) :
    (X i - X j)^(-eulerForm a (T.leafDimension i) (T.leafDimension j)).toNat ∣
      leadingPolynomial a c η hc θ T hT k f := by
  rcases Regroup.isolate_pair T i j hij with ⟨d,e,g,hi,hj⟩ | ⟨d,e,U,g,hi,hj⟩
  · have hdi : d=T.leafDimension i := by simpa only [hi,leafDimension] using g.leafDimension i
    have hej : e=T.leafDimension j := by simpa only [hj,leafDimension] using g.leafDimension j
    have hU := g.onSlope c η θ hT
    have h := twoLeading_diagonal_divisible a c η hc θ hU.1 hU.2
      (by simpa only [hdi,hej] using hsym) (g.degrees k).1 (g.degrees k).2 W
      (by have hw' := hw
          rw [← g.totalDegree k, ← g.doubleShift a] at hw'
          change 2*((g.degrees k).1+(g.degrees k).2)+(eulerForm a d d+eulerForm a e e)=W at hw'
          simpa only [add_assoc] using hw')
      (dimensionEquivB a (SlopeArithmetic.slope c η) g.dimension f)
      (dimensionEquivB_mem_sourceFiltration a c η hc θ g.dimension W f hf)
    change _ ∣ leadingPolynomial a c η hc θ _ hU (g.degrees k) _ at h
    rw [g.leadingPolynomial_natural a c η hc θ hT hU k f] at h
    have hh := map_dvd (extendPolynomial
      (g.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).symm.toAlgHom
      g.centers.symm) h
    rw [extendPolynomial_symm] at hh
    have hi' : g.centers.symm (Sum.inl ())=i := g.centers.symm_apply_eq.mpr hi.symm
    have hj' : g.centers.symm (Sum.inr ())=j := g.centers.symm_apply_eq.mpr hj.symm
    simpa only [map_pow,map_sub,extendPolynomial_X,hi',hj',hdi,hej] using hh
  · have hdi : d=T.leafDimension i := by simpa only [hi,leafDimension] using g.leafDimension i
    have hej : e=T.leafDimension j := by simpa only [hj,leafDimension] using g.leafDimension j
    have hU := g.onSlope c η θ hT
    have h := pairLeading_diagonal_divisible a c η hc θ hU.1.1 hU.1.2
      (by simpa only [hdi,hej] using hsym) U hU.2
      (g.degrees k).1.1 (g.degrees k).1.2 W (g.degrees k).2
      (by have h1 := g.totalDegree k; have h2 := g.doubleShift a
          change 2*((g.degrees k).1.1+(g.degrees k).1.2+U.totalDegree (g.degrees k).2)+
            eulerForm a d d+eulerForm a e e+U.doubleShift a=W
          have hw' : 2*(SplitTree.node (.node (.leaf d) (.leaf e)) U).totalDegree (g.degrees k)+
            (SplitTree.node (.node (.leaf d) (.leaf e)) U).doubleShift a=W := by rw [h1,h2]; exact hw
          change 2*((g.degrees k).1.1+(g.degrees k).1.2+U.totalDegree (g.degrees k).2)+
            ((eulerForm a d d+eulerForm a e e)+U.doubleShift a)=W at hw'
          simpa only [add_assoc] using hw')
      (dimensionEquivB a (SlopeArithmetic.slope c η) g.dimension f)
      (dimensionEquivB_mem_sourceFiltration a c η hc θ g.dimension W f hf)
    change _ ∣ leadingPolynomial a c η hc θ _ hU (g.degrees k) _ at h
    rw [g.leadingPolynomial_natural a c η hc θ hT hU k f] at h
    have hh := map_dvd (extendPolynomial
      (g.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).symm.toAlgHom
      g.centers.symm) h
    rw [extendPolynomial_symm] at hh
    have hi' : g.centers.symm (Sum.inl (Sum.inl ()))=i := g.centers.symm_apply_eq.mpr hi.symm
    have hj' : g.centers.symm (Sum.inl (Sum.inr ()))=j := g.centers.symm_apply_eq.mpr hj.symm
    simpa only [map_pow,map_sub,extendPolynomial_X,hi',hj',hdi,hej] using hh

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ManyBlockPolynomiality
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem leadingPolynomial_denominator_divisible (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (k : T.Degrees) (W : ℤ) (hw : 2*T.totalDegree k+T.doubleShift a=W)
    (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : f∈sourceFiltration a c η hc θ T.dim W)
    (s : Finset (T.Centers × T.Centers))
    (hs : ∀ ij∈s, ij.1≠ij.2) (hrev : ∀ ij∈s, (ij.2,ij.1)∉s)
    (hsym : ∀ ij∈s, eulerForm a (T.leafDimension ij.1) (T.leafDimension ij.2) =
      eulerForm a (T.leafDimension ij.2) (T.leafDimension ij.1)) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T))
      (centerDenominator a T s) ∣ leadingPolynomial a c η hc θ T hT k f := by
  classical
  apply product_dvd_of_scalar_factors
  · intro ij hij kl hkl hne
    apply (independent_diagonals (hs ij hij) (hs kl hkl) hne _).pow
    intro hr
    apply hrev ij hij
    have heq : (ij.2,ij.1)=kl := by
      simpa only [Prod.swap,Prod.eta] using congrArg Prod.swap hr
    rwa [heq]
  · intro ij hij
    have h := leadingPolynomial_diagonal_divisible a c η hc θ T hT k W hw f hf
      ij.2 ij.1 (hs ij hij).symm (hsym ij hij).symm
    simpa only [diagonal,map_pow,map_sub,map_X,hsym ij hij] using h

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem totalLeadingPolynomial_denominator_divisible (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (W : ℤ) (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : f∈sourceFiltration a c η hc θ T.dim W)
    (s : Finset (T.Centers × T.Centers))
    (hs : ∀ ij∈s, ij.1≠ij.2) (hrev : ∀ ij∈s, (ij.2,ij.1)∉s)
    (hsym : ∀ ij∈s, eulerForm a (T.leafDimension ij.1) (T.leafDimension ij.2) =
      eulerForm a (T.leafDimension ij.2) (T.leafDimension ij.1)) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T))
      (centerDenominator a T s) ∣ totalLeadingPolynomial a c η hc θ T hT W f := by
  classical
  obtain ⟨t,ht⟩ := polynomial_component_finite a (SlopeArithmetic.slope c η) T
    (centeredRestrictionB a c η hc θ T hT f)
  unfold totalLeadingPolynomial
  rw [mapLinear_weightComponent_eq_sum a (SlopeArithmetic.slope c η) T W _ t ht]
  apply Finset.dvd_sum
  intro k hk
  split_ifs with hw
  · exact leadingPolynomial_denominator_divisible a c η hc θ T hT k W hw f hf s hs hrev hsym
  · exact dvd_zero _

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_ShuffleLeafFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open SplitTree
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma shuffleB_translation_leaf_degreeCut (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (hd : d≠0) (he : e≠0)
    (hdθ : SlopeArithmetic.slope c η d=θ) (heθ : SlopeArithmetic.slope c η e=θ)
    (hχ : eulerForm a d e=eulerForm a e d) (U V : ℤ)
    (f : B a (SlopeArithmetic.slope c η) d) (g : B a (SlopeArithmetic.slope c η) e)
    (hf : f∈sourceFiltration a c η hc θ d U) (hg : g∈sourceFiltration a c η hc θ e V)
    (t : ℚ) :
    translationB a (SlopeArithmetic.slope c η) (d+e) t
      (shuffleB a c η hc d e (hdθ.trans heθ.symm) f g)∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) (.leaf (d+e)) (U+V) := by
  rw [translationB_shuffleB]
  exact shuffleB_leaf_degreeCut a c η hc d e _ hχ U V _ _
    (sourceFiltration_leaf_degreeCut a c η hc θ d hd hdθ U _
      (sourceFiltration_translation_mem a c η hc θ d U f hf t))
    (sourceFiltration_leaf_degreeCut a c η hc θ e he heθ V _
      (sourceFiltration_translation_mem a c η hc θ e V g hg t))

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ShuffleFiltration
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
open SplitTree
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem shuffleBUnit_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ) :
    ShuffleFiltered a c η hc θ d e := by
  classical
  suffices H : ∀ N : ℕ,∀ d e : I → ℕ,(∑ i,(d+e) i)=N → ShuffleFiltered a c η hc θ d e from
    H _ d e rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro d e hN hdθ heθ U V f g hf hg
    by_cases hd : d=0
    · subst d
      exact shuffleBUnit_filtered_zero_left a c η hc θ e _ U V f g hf hg
    by_cases he : e=0
    · subst e
      exact shuffleBUnit_filtered_zero_right a c η hc θ d _ U V f g hf hg
    have hdθ' : slope c η d=θ := hdθ.resolve_left hd
    have heθ' : slope c η e=θ := heθ.resolve_left he
    have hde := SlopeArithmetic.add_ne_zero_left d e hd
    rw [unitalSourceFiltration_nonzero a c η hc θ (d+e) hde]
    apply sourceFiltration_of_binary
    · intro t
      rw [show hdθ.compatible heθ=Or.inr (Or.inr (hdθ'.trans heθ'.symm)) from rfl,
        shuffleBUnit_eq_shuffleB]
      exact shuffleB_translation_leaf_degreeCut a c η hc θ d e hd he hdθ' heθ'
        (hχ d e hd he hdθ' heθ') U V f g
        (by rwa [unitalSourceFiltration_nonzero a c η hc θ d hd] at hf)
        (by rwa [unitalSourceFiltration_nonzero a c η hc θ e he] at hg) t
    · intro α β hα hβ hsα hsβ h
      apply restriction_shuffleBUnit_filtered a c η hc θ d e α β hα hβ hdθ' hsα hsβ _ h
      · intro d' e' h'
        apply ih (∑ i,α i) _ d' e' (by simp only [h'])
        have hp:=size_positive β hβ
        have hh : (∑ i,α i)+(∑ i,β i)=N := by
          rw [←Finset.sum_add_distrib]
          simpa only [Pi.add_apply] using (congrArg (fun x : I → ℕ=>∑ i,x i) h).trans hN
        omega
      · intro d' e' h'
        apply ih (∑ i,β i) _ d' e' (by simp only [h'])
        have hp:=size_positive α hα
        have hh : (∑ i,α i)+(∑ i,β i)=N := by
          rw [←Finset.sum_add_distrib]
          simpa only [Pi.add_apply] using (congrArg (fun x : I → ℕ=>∑ i,x i) h).trans hN
        omega
      · exact hf
      · exact hg

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TwoTargetFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma twoTargetTransferB_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd₁ : OnSlopeOrZero c η θ d₁) (he₁ : OnSlopeOrZero c η θ e₁)
    (hd₂ : OnSlopeOrZero c η θ d₂) (he₂ : OnSlopeOrZero c η θ e₂)
    (W : ℤ) (x : (B a (slope c η) d₁⊗[ℚ]B a (slope c η) e₁)⊗[ℚ]
      (B a (slope c η) d₂⊗[ℚ]B a (slope c η) e₂))
    (hx : x∈fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ W) :
    twoTargetTransferB a c η hc d₁ e₁ d₂ e₂ (hd₁.compatible he₁) (hd₂.compatible he₂) x∈
      unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) W := by
  let F:=unitalSourceFiltration a c η hc θ
  exact tensor_map_mem_filtration _ _ (F (d₁+e₁)) (F (d₂+e₂))
    (shuffleTensorBUnit a c η hc d₁ e₁ (hd₁.compatible he₁))
    (shuffleTensorBUnit a c η hc d₂ e₂ (hd₂.compatible he₂))
    (lift_mem_filtration _ _ _ (unitalSourceFiltration_antitone a c η hc θ (d₁+e₁)) _
      (shuffleBUnit_filtered a c η hc θ hχ d₁ e₁ hd₁ he₁))
    (lift_mem_filtration _ _ _ (unitalSourceFiltration_antitone a c η hc θ (d₂+e₂)) _
      (shuffleBUnit_filtered a c η hc θ hχ d₂ e₂ hd₂ he₂)) W x hx

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
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open SeparationInfinity
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def unitalGradeShuffle (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) (U V : ℤ) :
    UnitalSourceGrade a c η hc θ d U →ₗ[ℚ] UnitalSourceGrade a c η hc θ e V →ₗ[ℚ]
      UnitalSourceGrade a c η hc θ (d+e) (U+V) :=
  LinearFiltration.bilinear (unitalSourceFiltration a c η hc θ d U)
    (unitalSourceFiltration a c η hc θ d (U+1))
    (unitalSourceFiltration a c η hc θ e V) (unitalSourceFiltration a c η hc θ e (V+1))
    (unitalSourceFiltration a c η hc θ (d+e) (U+V))
    (unitalSourceFiltration a c η hc θ (d+e) (U+V+1))
    (shuffleBUnit a c η hc d e (hd.compatible he))
    (fun f hf g hg=>shuffleBUnit_filtered a c η hc θ hχ d e hd he U V f g hf hg)
    (fun f hf g hg=>by
      simpa only [add_assoc,add_comm (1:ℤ) V] using
        shuffleBUnit_filtered a c η hc θ hχ d e hd he (U+1) V f g hf hg)
    (fun f hf g hg=>by
      simpa only [add_assoc] using
        shuffleBUnit_filtered a c η hc θ hχ d e hd he U (V+1) f g hf hg)

lemma unitalGradeShuffle_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) (U V : ℤ)
    (f : unitalSourceFiltration a c η hc θ d U) (g : unitalSourceFiltration a c η hc θ e V) :
    unitalGradeShuffle a c η hc θ hχ d e hd he U V
      (Submodule.Quotient.mk f) (Submodule.Quotient.mk g)=
      (Submodule.Quotient.mk ⟨shuffleBUnit a c η hc d e (hd.compatible he) f.val g.val,
        shuffleBUnit_filtered a c η hc θ hχ d e hd he U V f.val g.val f.property g.property⟩ :
        UnitalSourceGrade a c η hc θ (d+e) (U+V)) := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalGradeAlgebra
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma unitalGradeShuffle_assoc (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e b : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) (hb : OnSlopeOrZero c η θ b)
    (U V W : ℤ) (f : UnitalSourceGrade a c η hc θ d U)
    (g : UnitalSourceGrade a c η hc θ e V) (h : UnitalSourceGrade a c η hc θ b W) :
    unitalGradeCast a c η hc θ (add_assoc d e b) (add_assoc U V W)
      (unitalGradeShuffle a c η hc θ hχ (d+e) b (hd.add hc he) hb (U+V) W
        (unitalGradeShuffle a c η hc θ hχ d e hd he U V f g) h)=
    unitalGradeShuffle a c η hc θ hχ d (e+b) hd (he.add hc hb) U (V+W) f
      (unitalGradeShuffle a c η hc θ hχ e b he hb V W g h) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    induction g using Submodule.Quotient.induction_on with
    | H g =>
      induction h using Submodule.Quotient.induction_on with
      | H h =>
        simp only [unitalGradeShuffle_mk,unitalGradeCast_mk]
        congr 1
        apply Subtype.ext
        rw [unitalFiltrationCast_val]
        exact shuffleBUnit_assoc a c η hc θ d e b hd he hb f.val g.val h.val

lemma unitalGradeShuffle_one_left (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (hd : OnSlopeOrZero c η θ d)
    (W : ℤ) (f : UnitalSourceGrade a c η hc θ d W) :
    unitalGradeShuffle a c η hc θ hχ 0 d (slopeZero c η θ) hd 0 W (unitalGradeOne a c η hc θ) f=
      unitalGradeCast a c η hc θ (zero_add d).symm (zero_add W).symm f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [unitalGradeOne,unitalGradeShuffle_mk,unitalGradeCast_mk]
    congr 1
    apply Subtype.ext
    rw [unitalFiltrationCast_val]
    exact shuffleBUnit_one_left a c η hc d _ f.val

lemma unitalGradeShuffle_one_right (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (hd : OnSlopeOrZero c η θ d)
    (W : ℤ) (f : UnitalSourceGrade a c η hc θ d W) :
    unitalGradeShuffle a c η hc θ hχ d 0 hd (slopeZero c η θ) W 0 f (unitalGradeOne a c η hc θ)=
      unitalGradeCast a c η hc θ (add_zero d).symm (add_zero W).symm f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [unitalGradeOne,unitalGradeShuffle_mk,unitalGradeCast_mk]
    congr 1
    apply Subtype.ext
    rw [unitalFiltrationCast_val]
    exact shuffleBUnit_one_right a c η hc d _ f.val
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
open scoped DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable instance componentGradedMul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)] :
    GradedMonoid.GMul (unitalComponent a c η hc θ) where
  mul {i j} f g := unitalGradeShuffle a c η hc θ hχ.out i.1.val j.1.val i.1.property j.1.property i.2 j.2 f g

lemma component_one_mul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (f : GradedMonoid (unitalComponent a c η hc θ)) : 1*f=f := by
  apply Sigma.ext (zero_add _)
  exact (heq_of_eq (unitalGradeShuffle_one_left a c η hc θ hχ.out f.1.1.val f.1.1.property f.1.2 f.2)).trans
    (unitalGradeCast_heq a c η hc θ _ _ f.2)

lemma component_mul_one (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (f : GradedMonoid (unitalComponent a c η hc θ)) : f*1=f := by
  apply Sigma.ext (add_zero _)
  exact (heq_of_eq (unitalGradeShuffle_one_right a c η hc θ hχ.out f.1.1.val f.1.1.property f.1.2 f.2)).trans
    (unitalGradeCast_heq a c η hc θ _ _ f.2)

lemma component_mul_assoc (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (f g h : GradedMonoid (unitalComponent a c η hc θ)) : (f*g)*h=f*(g*h) := by
  apply Sigma.ext (add_assoc _ _ _)
  exact (unitalGradeCast_heq a c η hc θ (add_assoc f.1.1.val g.1.1.val h.1.1.val)
    (add_assoc f.1.2 g.1.2 h.1.2) _).symm.trans
    (heq_of_eq (unitalGradeShuffle_assoc a c η hc θ hχ.out f.1.1.val g.1.1.val h.1.1.val
      f.1.1.property g.1.1.property h.1.1.property f.1.2 g.1.2 h.1.2 f.2 g.2 h.2))

noncomputable instance componentGradedMonoid (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)] :
    GradedMonoid.GMonoid (unitalComponent a c η hc θ) :=
  gradedMonoidOfLaws (component_one_mul a c η hc θ)
    (component_mul_one a c η hc θ) (component_mul_assoc a c η hc θ)

noncomputable instance componentGradedRing (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)] :
    DirectSum.GRing (unitalComponent a c η hc θ) :=
  gradedRingOfAddLaws
    (fun _=>map_zero _)
    (fun {i j} x=>by
      change unitalGradeShuffle a c η hc θ hχ.out i.1.val j.1.val
        i.1.property j.1.property i.2 j.2 0 x=0
      rw [map_zero]
      rfl)
    (fun _ _ _=>map_add _ _ _)
    (fun {i j} x y z=>by
      change unitalGradeShuffle a c η hc θ hχ.out i.1.val j.1.val
        i.1.property j.1.property i.2 j.2 (x+y) z=_
      rw [map_add]
      rfl)

lemma component_smul_mul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (r : ℚ) (x y : GradedMonoid (unitalComponent a c η hc θ)) : (r•x)*y=r•(x*y) := by
  apply Sigma.ext (show x.1+y.1=x.1+y.1 from rfl)
  apply heq_of_eq
  change unitalGradeShuffle a c η hc θ hχ.out x.1.1.val y.1.1.val
    x.1.1.property y.1.1.property x.1.2 y.1.2 (r•x.2) y.2=r•_
  rw [map_smul,LinearMap.smul_apply]
  rfl

lemma component_mul_smul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (r : ℚ) (x y : GradedMonoid (unitalComponent a c η hc θ)) : x*(r•y)=r•(x*y) := by
  apply Sigma.ext (show x.1+y.1=x.1+y.1 from rfl)
  apply heq_of_eq
  exact map_smul (unitalGradeShuffle a c η hc θ hχ.out x.1.1.val y.1.1.val
    x.1.1.property y.1.1.property x.1.2 y.1.2 x.2) r y.2

noncomputable instance componentGradedAlgebra (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)] :
    DirectSum.GAlgebra ℚ (unitalComponent a c η hc θ) :=
  gradedAlgebraOfBilinear (component_smul_mul a c η hc θ) (component_mul_smul a c η hc θ)

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
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
open ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma signedCellMultiplyB_filtered (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d₁ e₁ d₂ e₂ : I → ℕ) (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂)
    (U V : ℤ) (x : B a (slope c η) d₁⊗[ℚ]B a (slope c η) d₂)
    (y : B a (slope c η) e₁⊗[ℚ]B a (slope c η) e₂)
    (hx : x∈unitalSourceTensorFiltration a c η hc θ d₁ d₂ U)
    (hy : y∈unitalSourceTensorFiltration a c η hc θ e₁ e₂ V) :
    signedCellMultiplyB a c η hc θ d₁ e₁ d₂ e₂ hon x y∈
      unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) (U+V) := by
  rw [signedCellMultiplyB_apply]
  apply Submodule.smul_mem
  apply twoTargetTransferB_filtered a c η hc θ hχ d₁ e₁ d₂ e₂
    hon.1 hon.2.1 hon.2.2.1 hon.2.2.2 (U+V)
  exact interchange_mem_filtration (unitalSourceFiltration a c η hc θ d₁)
    (unitalSourceFiltration a c η hc θ d₂) (unitalSourceFiltration a c η hc θ e₁)
    (unitalSourceFiltration a c η hc θ e₂) U V x y hx hy

noncomputable def signedCellGradeMultiply (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d₁ e₁ d₂ e₂ : I → ℕ) (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂) (U V : ℤ) :
    UnitalSourceTensorGrade a c η hc θ d₁ d₂ U →ₗ[ℚ]
    UnitalSourceTensorGrade a c η hc θ e₁ e₂ V →ₗ[ℚ]
    UnitalSourceTensorGrade a c η hc θ (d₁+e₁) (d₂+e₂) (U+V) :=
  LinearFiltration.bilinear (unitalSourceTensorFiltration a c η hc θ d₁ d₂ U)
    (unitalSourceTensorFiltration a c η hc θ d₁ d₂ (U+1))
    (unitalSourceTensorFiltration a c η hc θ e₁ e₂ V)
    (unitalSourceTensorFiltration a c η hc θ e₁ e₂ (V+1))
    (unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) (U+V))
    (unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) (U+V+1))
    (signedCellMultiplyB a c η hc θ d₁ e₁ d₂ e₂ hon)
    (fun x hx y hy=>signedCellMultiplyB_filtered a c η hc θ hχ d₁ e₁ d₂ e₂ hon U V x y hx hy)
    (fun x hx y hy=>by simpa only [add_right_comm] using
      signedCellMultiplyB_filtered a c η hc θ hχ d₁ e₁ d₂ e₂ hon (U+1) V x y hx hy)
    (fun x hx y hy=>by simpa only [add_assoc] using
      signedCellMultiplyB_filtered a c η hc θ hχ d₁ e₁ d₂ e₂ hon U (V+1) x y hx hy)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open DimensionSplit SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def columnFiltrationTerm (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    {d e α β : I → ℕ} (U V : ℤ)
    (x : unitalSourceFiltration a c η hc θ d U)
    (y : unitalSourceFiltration a c η hc θ e V) (s : ColumnDimensionGrid d e α β) :
    unitalSourceTensorFiltration a c η hc θ α β (U+V) :=
  if hon : CellsOnSlope c η θ (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2) then
    unitalTensorFiltrationCast a c η hc θ s.property.1 s.property.2 rfl
      ⟨signedCellMultiplyB a c η hc θ _ _ _ _ hon
          (splitCoproductFiltration a c η hc θ s.val.1 ⟨hon.1,hon.2.2.1⟩ U x).val
          (splitCoproductFiltration a c η hc θ s.val.2 ⟨hon.2.1,hon.2.2.2⟩ V y).val,
        signedCellMultiplyB_filtered a c η hc θ hχ _ _ _ _ hon U V _ _
          (splitCoproductFiltration a c η hc θ s.val.1 ⟨hon.1,hon.2.2.1⟩ U x).property
          (splitCoproductFiltration a c η hc θ s.val.2 ⟨hon.2.1,hon.2.2.2⟩ V y).property⟩
  else 0

noncomputable def columnGradeTerm (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    {d e α β : I → ℕ} (U V : ℤ)
    (x : UnitalSourceGrade a c η hc θ d U)
    (y : UnitalSourceGrade a c η hc θ e V) (s : ColumnDimensionGrid d e α β) :
    UnitalSourceTensorGrade a c η hc θ α β (U+V) :=
  if hon : CellsOnSlope c η θ (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2) then
    unitalTensorGradeCast a c η hc θ s.property.1 s.property.2 rfl
      (signedCellGradeMultiply a c η hc θ hχ _ _ _ _ hon U V
        (splitCoproductGrade a c η hc θ s.val.1 ⟨hon.1,hon.2.2.1⟩ U x)
        (splitCoproductGrade a c η hc θ s.val.2 ⟨hon.2.1,hon.2.2.2⟩ V y))
  else 0

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorMiddleEnd
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
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

noncomputable def globalSignedTensorMultiply (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)] :
    UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ →ₗ[ℚ]
    UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ →ₗ[ℚ]
    UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  TensorProduct.curry ((TensorProduct.lift
    (Algebra.lmul ℚ (UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ)).toLinearMap).comp
      (middleEnd (globalSignOperator a c η hc θ)))

lemma globalSignedTensorMultiply_tmul_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (k l m n : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) (y : unitalComponent a c η hc θ l)
    (z : unitalComponent a c η hc θ m) (w : unitalComponent a c η hc θ n) :
    globalSignedTensorMultiply a c η hc θ
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y)
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) m z⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) n w)=
      ((-1:ℚ)^eulerForm a l.1.val m.1.val) •
        ((DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x *
          DirectSum.lof ℚ _ (unitalComponent a c η hc θ) m z)⊗ₜ[ℚ]
         (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y *
          DirectSum.lof ℚ _ (unitalComponent a c η hc θ) n w)) := by
  unfold globalSignedTensorMultiply
  simp only [TensorProduct.curry_apply,LinearMap.comp_apply]
  rw [middleEnd_scalar _ _ _ _ _ _ (globalSignOperator_tmul_lof a c η hc θ l m y z),map_smul,
    TensorProduct.lift.tmul]
  exact congrArg (fun t=>((-1:ℚ)^eulerForm a l.1.val m.1.val) • t)
    (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _)

end ElementaryPositivity.RawShuffle

end

end OAI
end


