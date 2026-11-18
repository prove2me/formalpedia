-- Prove2me | Definitions.Def_OAIQ368Chrom032
-- name    : OAIQ368Chrom032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:33:09.832049+00:00
-- url     : https://prove2.me/theorems/79ce7f40-8da3-43ec-a694-d0fe9bf96cd0
-- title:
--   Definitions bundle OAIQ368Chrom032 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 11 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Histories_ShuffleLeafFiltration`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Histories/ShuffleLeafFiltration.lean), [`Chromatic_Shuffle_Interaction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/Interaction.lean), [`Chromatic_Shuffle_ManyBlockDiagonal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/ManyBlockDiagonal.lean), [`Chromatic_Shuffle_TaylorSCoeffHomogeneous`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/TaylorSCoeffHomogeneous.lean), [`Chromatic_Walls_PolynomialCoeffLinear`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/PolynomialCoeffLinear.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom027` and `OAIQ368Chrom028` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom035`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom027
import Definitions.Def_OAIQ368Chrom028

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TaylorSCoeffHomogeneous
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity ElementaryPositivity.CommonTranslation
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma taylorB_coeff_graded (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (f : B a μ d) (k : ℤ) (hf : f∈gradeB a μ d k) (n : ℕ) :
    (taylorB a μ d f).coeff n ∈ gradeB a μ d (k-n) := by
  obtain ⟨g,hg,rfl⟩ := gradeB_homogeneous_representative a μ d k f hf
  change (taylorB a μ d (quotientAlg a μ d g)).coeff n ∈ _
  rw [taylorB_mk,Polynomial.coeff_map]
  change (destabilizingSpace a μ d).mkQ ((taylorS d g).coeff n) ∈ _
  rw [mem_gradeB_iff,componentB_mk,componentS_of_homogeneous _ _
    (taylorS_coeff_homogeneous d g k hg n),ite_eq_left rfl]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Interaction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient_apply _root_.OAI.ElementaryPositivity.RawShuffle.castS_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castS_trans _root_.OAI.ElementaryPositivity.RawShuffle.degreeZeroB_mk _root_.OAI.ElementaryPositivity.RawShuffle.fourValueAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.relativeCoeffB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity ElementaryPositivity.SeparatedSymmetry ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma component_separateTensor_homogeneous (d e : I → ℕ)
    (f : MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ) (k : ℤ)
    (hf : f.IsWeightedHomogeneous (fun _=>(1:ℤ)) k) (m n : ℤ) (h : m+n≠k) :
    TensorProduct.map (componentS d m) (componentS e n) (separateTensor d e f)=0 := by
  classical
  rw [← f.support_sum_monomial_coeff,map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro u hu
  let x := Finsupp.comapDomain Sum.inl u (Set.injOn_of_injective Sum.inl_injective)
  let y := Finsupp.comapDomain Sum.inr u (Set.injOn_of_injective Sum.inr_injective)
  have hxy : x.sumElim y=u := Finsupp.comapDomain_sumElim_comapDomain u
  have hw : Finsupp.weight (fun _=>(1:ℤ)) x + Finsupp.weight (fun _=>(1:ℤ)) y=k := by
    rw [← totalWeight_sumElim,hxy]
    exact hf (mem_support_iff.mp hu)
  rw [← hxy,monomial_sumElim,separateTensor_product_any,TensorProduct.map_tmul,
    componentS_of_homogeneous _ _ (reynoldsS_homogeneous _ _ _ (isWeightedHomogeneous_monomial _ _ _ rfl)),
    componentS_of_homogeneous _ _ (reynoldsS_homogeneous _ _ _ (isWeightedHomogeneous_monomial _ _ _ rfl))]
  split_ifs with hm hn <;> simp_all

lemma component_restrictTensor_homogeneous {d e : I → ℕ} (A : Cut d e)
    (f : S (d+e)) (k : ℤ) (hf : f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k)
    (m n : ℤ) (h : m+n≠k) :
    TensorProduct.map (componentS d m) (componentS e n) (restrictTensor A f)=0 := by
  exact component_separateTensor_homogeneous d e _ k (constantWeight_rename _ _ hf) m n h

theorem restrictionB_graded (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (A : Cut d e) (f : B a (SlopeArithmetic.slope c η) (d+e))
    (k : ℤ) (hf : f∈gradeB a (SlopeArithmetic.slope c η) (d+e) k)
    (m n : ℤ) (h : m+n≠k) :
    TensorProduct.map (componentB a (SlopeArithmetic.slope c η) d m)
      (componentB a (SlopeArithmetic.slope c η) e n) (restrictionB a c η hc hs A f)=0 := by
  obtain ⟨g,hg,rfl⟩ := gradeB_homogeneous_representative a _ (d+e) k f hf
  change TensorProduct.map _ _ (restrictionB a c η hc hs A (quotientAlg a _ (d+e) g))=0
  rw [restrictionB_mk,component_quotientTensor,component_restrictTensor_homogeneous A g k hg m n h,map_zero]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialCoeffLinear
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
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem relativeCoeffB_graded (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : B a μ d ⊗[ℚ] B a μ e) (k : ℤ)
    (hx : ∀ m n,m+n≠k → TensorProduct.map (componentB a μ d m) (componentB a μ e n) x=0)
    (s : ℕ) (p q : ℤ) (h : p+q≠k-s) :
    TensorProduct.map (componentB a μ d p) (componentB a μ e q) (relativeCoeffB a μ d e s x)=0 := by
  classical
  let F := (TensorProduct.map (componentB a μ d p) (componentB a μ e q)).comp (relativeCoeffB a μ d e s)
  change F x=0
  obtain ⟨t,ht,he⟩ := SplitTree.componentTensor_finite_decomposition a μ (.node (.leaf d) (.leaf e)) x
  change (∑ mn∈t,TensorProduct.map (componentB a μ d mn.1) (componentB a μ e mn.2) x)=x at he
  have hterm : ∀ mn∈t,F (TensorProduct.map (componentB a μ d mn.1) (componentB a μ e mn.2) x)=0 := by
    intro mn hmn
    by_cases hm : mn.1+mn.2=k
    · have hsep : p≠mn.1-s ∨ q≠mn.2 := by
        by_contra hh
        push Not at hh
        apply h
        rw [hh.1,hh.2,← hm]
        ring
      generalize x=y
      induction y using OAI.tensorInductionOn with
      | tmul f g =>
        change TensorProduct.map (componentB a μ d p) (componentB a μ e q)
          (relativeCoeffB a μ d e s (componentB a μ d mn.1 f ⊗ₜ[ℚ] componentB a μ e mn.2 g))=0
        rw [relativeCoeffB_tmul,TensorProduct.map_tmul,
          componentB_on_grade a μ d p (mn.1-s) _
            (taylorB_coeff_graded a μ d _ mn.1 ⟨f,rfl⟩ s),
          componentB_on_grade a μ e q mn.2 _ ⟨g,rfl⟩]
        rcases hsep with hp|hq
        · rw [ite_eq_right hp,TensorProduct.zero_tmul]
        · rw [ite_eq_right hq,TensorProduct.tmul_zero]
      | add y z hy hz => simp only [map_add,hy,hz,add_zero]
    · rw [hx mn.1 mn.2 hm,map_zero]
  calc
    F x=F (∑ mn∈t,TensorProduct.map (componentB a μ d mn.1) (componentB a μ e mn.2) x) := congrArg F he.symm
    _=0 := by rw [map_sum]; exact Finset.sum_eq_zero hterm

theorem relative_restriction_graded (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (A : Cut d e) (f : B a (SlopeArithmetic.slope c η) (d+e))
    (k : ℤ) (hf : f∈gradeB a (SlopeArithmetic.slope c η) (d+e) k)
    (s : ℕ) (p q : ℤ) (h : p+q≠k-s) :
    TensorProduct.map (componentB a (SlopeArithmetic.slope c η) d p)
      (componentB a (SlopeArithmetic.slope c η) e q)
      (relativeCoeffB a (SlopeArithmetic.slope c η) d e s (restrictionB a c η hc hs A f))=0 := by
  exact relativeCoeffB_graded a _ d e _ k (fun m n hm=>restrictionB_graded a c η hc hs A f k hf m n hm) s p q h

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem relativeLeading_taylor_divisible (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (hd : d≠0) (_he : e≠0)
    (hdθ : SlopeArithmetic.slope c η d=θ) (heθ : SlopeArithmetic.slope c η e=θ)
    (r : ℕ) (hsym : eulerForm a d e=eulerForm a e d) (p q W : ℤ)
    (hw : 2*(p+q)+eulerForm a d d+eulerForm a e e=W)
    (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) :
    Polynomial.X ^ (-eulerForm a d e).toNat ∣
      relativeLeading a c η hc (hdθ.trans heθ.symm) p q ((taylorB a (SlopeArithmetic.slope c η) (d+e) f).coeff r) := by
  classical
  apply Polynomial.X_pow_dvd_iff.mpr
  intro s hs
  let μ:=SlopeArithmetic.slope c η
  let F := (polynomialCoeffLinear
    (B a μ d ⊗[ℚ] B a μ e) s).comp
    (relativeLeading a c η hc (d:=d) (e:=e) (hdθ.trans heθ.symm) p q)
  let g := (taylorB a μ (d+e) f).coeff r
  change F g=0
  obtain ⟨t,ht,heq⟩ := componentB_finite_decomposition a μ (d+e) g
  have hterm : ∀ k∈t,F (componentB a μ (d+e) k g)=0 := by
    intro k hk
    by_cases hkdeg : p+q=k-s
    · have hsmall : 2*k+eulerForm a (d+e) (d+e)<W := by
        rw [eulerForm_add_left,eulerForm_add_right,eulerForm_add_right,← hsym]
        omega
      have slopeTot : SlopeArithmetic.slope c η (d+e)=θ :=
        (SlopeArithmetic.slope_add_same c η hc (hdθ.trans heθ.symm)).trans hdθ
      have hzero := hf (.leaf (d+e)) trivial
        ⟨SlopeArithmetic.add_ne_zero_left d e hd,slopeTot⟩ rfl k (Finsupp.single () r) hsmall
      rw [restrictionTest_leaf_coeff] at hzero
      have hz : componentB a μ (d+e) k g = (0 : B a μ (d+e)) := hzero
      exact (congrArg F hz).trans F.map_zero
    · exact relative_restriction_graded a c η hc (hdθ.trans heθ.symm) (firstCut d e)
        (componentB a μ (d+e) k g) k ⟨g,rfl⟩ s p q hkdeg
  calc
    F g=F (∑ k∈t,componentB a μ (d+e) k g) := congrArg F heq.symm
    _=0 := by rw [map_sum]; exact Finset.sum_eq_zero hterm

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
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma pairRelativeCoefficient_wrong_degree (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (s : ℕ) (p q m : ℤ) (h : p+q ≠ m-s)
    (f : B a (SlopeArithmetic.slope c η) (d+e)) :
    pairRelativeCoefficient a c η hc hs s p q
      (componentB a (SlopeArithmetic.slope c η) (d+e) m f) = 0 := by
  exact relative_restriction_graded a c η hc hs (firstCut d e)
    (componentB a (SlopeArithmetic.slope c η) (d+e) m f) m ⟨f,rfl⟩ s p q h

namespace SplitTree

theorem pairRefinementCoefficient_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) (θ : ℝ) {d e : I → ℕ}
    (hd : d ≠ 0) (hdθ : SlopeArithmetic.slope c η d = θ)
    (heθ : SlopeArithmetic.slope c η e = θ)
    (hsym : eulerForm a d e = eulerForm a e d)
    (T : SplitTree I) (hT : T.OnSlope c η θ)
    (p q W : ℤ) (k : T.Degrees)
    (hw : 2*(p+q+T.totalDegree k)+eulerForm a d d+eulerForm a e e+T.doubleShift a = W)
    (f : B a (SlopeArithmetic.slope c η) ((d+e)+T.dim))
    (hf : f ∈ sourceFiltration a c η hc θ ((d+e)+T.dim) W)
    (z : (SplitTree.node (.leaf (d+e)) T).Centers →₀ ℕ)
    (s : ℕ) (hs : s < (-eulerForm a d e).toNat) :
    pairRefinementCoefficient a c η hc (hdθ.trans heθ.symm) T s p q k
      ((centeredRestrictionB a c η hc θ (.node (.leaf (d+e)) T)
        ⟨⟨SlopeArithmetic.add_ne_zero_left d e hd,
          (SlopeArithmetic.slope_add_same c η hc (hdθ.trans heθ.symm)).trans hdθ⟩,hT⟩ f).coeff z) = 0 := by
  classical
  let μ := SlopeArithmetic.slope c η
  let U : SplitTree I := .node (.leaf (d+e)) T
  have hU : U.OnSlope c η θ :=
    ⟨⟨SlopeArithmetic.add_ne_zero_left d e hd,
      (SlopeArithmetic.slope_add_same c η hc (hdθ.trans heθ.symm)).trans hdθ⟩,hT⟩
  let x : tensor (quotientFamily a μ) U := (centeredRestrictionB a c η hc θ U hU f).coeff z
  let F := pairRefinementCoefficient a c η hc (hdθ.trans heθ.symm) T s p q k
  change F x = 0
  obtain ⟨t,ht,heq⟩ := componentTensor_finite_decomposition a μ U x
  have hterm : ∀ j ∈ t, F (componentTensor a μ U j x) = 0 := by
    intro j hj
    by_cases hk : k = j.2
    · subst k
      by_cases hm : p+q = j.1-s
      · have hsmall : 2*U.totalDegree j+U.doubleShift a < W := by
          change 2*(j.1+T.totalDegree j.2)+(eulerForm a (d+e) (d+e)+T.doubleShift a) < W
          rw [eulerForm_add_left,eulerForm_add_right,eulerForm_add_right,← hsym]
          have hs' : (s : ℤ) < -eulerForm a d e := Int.lt_toNat.mp hs
          linarith only [hs', hm, hw]
        have hz := sourceFiltration_allTrees a c η hc θ W f hf U hU rfl j z hsmall
        change componentTensor a μ U j x = 0 at hz
        rw [hz,map_zero]
      · generalize x = y
        induction y using OAI.tensorInductionOn with
        | tmul g h =>
          change pairRelativeCoefficient a c η hc (hdθ.trans heθ.symm) s p q
            (componentB a μ (d+e) j.1 g) ⊗ₜ[ℚ]
              componentTensor a μ T j.2 (componentTensor a μ T j.2 h) = 0
          change B a μ (d+e) at g
          rw [pairRelativeCoefficient_wrong_degree a c η hc (d := d) (e := e) (hdθ.trans heθ.symm) s p q j.1 hm, TensorProduct.zero_tmul]
        | add y y' hy hy' => simp only [map_add,hy,hy',add_zero]
    · generalize x = y
      induction y using OAI.tensorInductionOn with
      | tmul g h =>
        change pairRelativeCoefficient a c η hc (hdθ.trans heθ.symm) s p q
          (componentB a μ (d+e) j.1 g) ⊗ₜ[ℚ]
            componentTensor a μ T k (componentTensor a μ T j.2 h) = 0
        rw [componentTensor_componentTensor,ite_eq_right hk,TensorProduct.tmul_zero]
      | add y y' hy hy' => simp only [map_add,hy,hy',add_zero]
  calc
    F x = F (∑ j ∈ t, componentTensor a μ U j x) := congrArg F heq.symm
    _ = 0 := by rw [map_sum]; exact Finset.sum_eq_zero hterm

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_ShuffleLeafFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
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

lemma shuffleB_leaf_degreeCut (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (hχ : eulerForm a d e=eulerForm a e d) (U V : ℤ)
    (f : B a (SlopeArithmetic.slope c η) d) (g : B a (SlopeArithmetic.slope c η) e)
    (hf : f∈degreeCutSubmodule a (SlopeArithmetic.slope c η) (.leaf d) U)
    (hg : g∈degreeCutSubmodule a (SlopeArithmetic.slope c η) (.leaf e) V) :
    shuffleB a c η hc d e hs f g∈degreeCutSubmodule a (SlopeArithmetic.slope c η) (.leaf (d+e)) (U+V) := by
  classical
  intro k hk
  change ℤ at k
  change 2*k+eulerForm a (d+e) (d+e)<U+V at hk
  change componentB a (SlopeArithmetic.slope c η) (d+e) k (shuffleB a c η hc d e hs f g)=0
  obtain ⟨s,_,hsum⟩ := componentB_finite_decomposition a (SlopeArithmetic.slope c η) d f
  obtain ⟨t,_,htsum⟩ := componentB_finite_decomposition a (SlopeArithmetic.slope c η) e g
  rw [←hsum,←htsum]
  simp only [map_sum,LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro m hm
  by_cases hm' : 2*m+eulerForm a d d<U
  · have hz : componentB a (SlopeArithmetic.slope c η) d m f=0 := hf m hm'
    rw [hz,map_zero,LinearMap.zero_apply,map_zero]
  by_cases hn' : 2*n+eulerForm a e e<V
  · have hz : componentB a (SlopeArithmetic.slope c η) e n g=0 := hg n hn'
    rw [hz,map_zero,map_zero]
  rw [componentB_on_grade a _ _ k (m+n-eulerForm a d e) _
    (shuffleB_graded a c η hc d e hs m n _ _ ⟨f,rfl⟩ ⟨g,rfl⟩)]
  apply ite_eq_right
  rw [eulerForm_add_left,eulerForm_add_right,eulerForm_add_right,←hχ] at hk
  change 2*(k : ℤ)+(eulerForm a d d+eulerForm a d e+(eulerForm a d e+eulerForm a e e))<U+V at hk
  omega

lemma sourceFiltration_leaf_degreeCut (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hθ : SlopeArithmetic.slope c η d=θ)
    (U : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d U) :
    f∈degreeCutSubmodule a (SlopeArithmetic.slope c η) (.leaf d) U := by
  intro k hk
  have h:=hf (.leaf d) trivial ⟨hd,hθ⟩ rfl k 0 hk
  rwa [restrictionTest_leaf_zero] at h

end ElementaryPositivity.RawShuffle

end

end OAI
end


