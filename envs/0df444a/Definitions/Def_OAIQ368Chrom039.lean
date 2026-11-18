-- Prove2me | Definitions.Def_OAIQ368Chrom039
-- name    : OAIQ368Chrom039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:42:23.63973+00:00
-- url     : https://prove2.me/theorems/b333d184-091d-41a4-acc6-b463fed4a33d
-- title:
--   Definitions bundle OAIQ368Chrom039 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 123 declarations of OpenAI's Lean: 45 definitions and 78 theorems. The definitions and types are `OAI.ElementaryPositivity.CenterCalculus.boxRightLinear`, `OAI.ElementaryPositivity.FiniteLog.convPost`, `OAI.ElementaryPositivity.FiniteLog.nilEval`, `OAI.ElementaryPositivity.FiniteLog.nilEvalAlgHom`, `OAI.ElementaryPositivity.LinearDetection.tensorFiltrationAssoc`, `OAI.ElementaryPositivity.LinearDetection.unassocTensorFixedLeft`, `OAI.ElementaryPositivity.LinearFiltration.FGrade`, `OAI.ElementaryPositivity.LinearFiltration.gradeMap`, `OAI.ElementaryPositivity.LinearFiltration.tensorFiltrationComm`, `OAI.ElementaryPositivity.LinearFiltration.tensorGradeAssoc`, `OAI.ElementaryPositivity.LinearFiltration.tensorGradeComm`, `OAI.ElementaryPositivity.LinearFiltration.tensorGradeLift`, `OAI.ElementaryPositivity.LinearFiltration.tensorGradeMap`, `OAI.ElementaryPositivity.RawShuffle.DimensionSplit.swap`, `OAI.ElementaryPositivity.RawShuffle.LeftSlopeTriple`, `OAI.ElementaryPositivity.RawShuffle.SlopeTriple`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.PairSymmetric`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.Regroup.OrderPreserving`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.centerNumerator`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.centerPairs`, `OAI.ElementaryPositivity.RawShuffle.convVanishes`, `OAI.ElementaryPositivity.RawShuffle.dimensionSize`, `OAI.ElementaryPositivity.RawShuffle.filtrationDimensionEquiv`, `OAI.ElementaryPositivity.RawShuffle.globalGradeLof`, `OAI.ElementaryPositivity.RawShuffle.globalIteratedLeftSplit`, `OAI.ElementaryPositivity.RawShuffle.globalIteratedRightSplit`, `OAI.ElementaryPositivity.RawShuffle.globalLeftTripleCoproduct`, `OAI.ElementaryPositivity.RawShuffle.globalLeftTripleOutput`, `OAI.ElementaryPositivity.RawShuffle.globalSplitGradeCoproduct`, `OAI.ElementaryPositivity.RawShuffle.globalTripleCoproduct`, `OAI.ElementaryPositivity.RawShuffle.globalTripleGradeLeft`, `OAI.ElementaryPositivity.RawShuffle.globalTripleGradeRight`, `OAI.ElementaryPositivity.RawShuffle.iteratedCoproductLeft`, `OAI.ElementaryPositivity.RawShuffle.iteratedCoproductRight`, `OAI.ElementaryPositivity.RawShuffle.leftTripleBuild`, `OAI.ElementaryPositivity.RawShuffle.naturalTensorAdd`, `OAI.ElementaryPositivity.RawShuffle.naturalTensorModule`, `OAI.ElementaryPositivity.RawShuffle.separationCoefficientRestricted`, `OAI.ElementaryPositivity.RawShuffle.tensorSeparationLeft`, `OAI.ElementaryPositivity.RawShuffle.tensorSeparationRight` and 5 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_ConvolutionPostcomposition`, `Chromatic_GradedAlgebra_NilpotentLogarithm`, `Chromatic_GradedAlgebra_RationalPolynomialDivisibility`, `Chromatic_Shuffle_CoproductIteration`, `Chromatic_Shuffle_GlobalCoproductCoassociative`, `Chromatic_Shuffle_GlobalCoproductCocommutative`, `Chromatic_Shuffle_GlobalCoproductIteration`, `Chromatic_Shuffle_GlobalShuffleCoalgebra`, `Chromatic_Shuffle_GlobalTripleGradeInclusion`, `Chromatic_Shuffle_GlobalWordDetection`, `Chromatic_Shuffle_GradedCoproduct`, `Chromatic_Shuffle_PointEvaluation`, `Chromatic_Shuffle_PolynomialExtendInjective`, `Chromatic_Shuffle_SignedCoproductGridGrade`, `Chromatic_Shuffle_SymbolDetection`, `Chromatic_Shuffle_TaylorSCoeffHomogeneous`, `Chromatic_Shuffle_TensorPolynomialBox`, `Chromatic_Shuffle_TripleAssociativity`, `Chromatic_Shuffle_TripleFiltration`, `Chromatic_Shuffle_UnitalCoproductCoassociative`, `Chromatic_Shuffle_UnitalCoproductComparison`, `Chromatic_Shuffle_UnitalCoproductUnits`, `Chromatic_Walls_FilteredTensorComm`, `Chromatic_Walls_FilteredTensorInsert`, `Chromatic_Walls_Grade`, `Chromatic_Walls_RefinedTensorDetection`, `Chromatic_Walls_TensorFiltrationInterchange`, `Chromatic_Walls_TensorGradeFiniteSum`, `Chromatic_Walls_TensorGradeFunctor`, `Chromatic_Walls_TensorPolynomialLinear`, `Chromatic_Walls_UnitalCoproductNaturality`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom031` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom041` and `OAIQ368Chrom044`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom031

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_ConvolutionPostcomposition
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteLog
open WithConv
variable {R C A B : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
  [Coalgebra R C] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

noncomputable def convPost (φ : A →ₐ[R] B) : WithConv (C →ₗ[R] A) →ₐ[R] WithConv (C →ₗ[R] B) where
  toFun f := toConv (φ.toLinearMap.comp f.ofConv)
  map_zero' := by apply WithConv.ofConv_injective; ext x; exact φ.map_zero
  map_add' f g := by apply WithConv.ofConv_injective; ext x; exact φ.map_add _ _
  map_one' := by
    apply WithConv.ofConv_injective
    ext x
    exact φ.commutes _
  map_mul' f g := WithConv.ofConv_injective (LinearMap.algHom_comp_convMul_distrib φ f g)
  commutes' r := by
    apply WithConv.ofConv_injective
    ext x
    change φ (r • algebraMap R A (Coalgebra.counit (R := R) x))=
      r • algebraMap R B (Coalgebra.counit (R := R) x)
    rw [map_smul,φ.commutes]

lemma convPost_apply (φ : A →ₐ[R] B) (f : WithConv (C →ₗ[R] A)) (x : C) :
    ((convPost φ) f).ofConv x=φ (f.ofConv x) := rfl

end ElementaryPositivity.FiniteLog

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_NilpotentLogarithm
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteLog
open PowerSeries

lemma subst_one {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {g : PowerSeries S} (hg : HasSubst g) : (1 : PowerSeries R).subst g=1 :=
by
  rw [←coe_substAlgHom hg,map_one]

lemma deriv_log_mul_one_add_X :
    derivative ℚ (log ℚ) * (1+X)=1 := by
  rw [deriv_log,mul_add,mul_one]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [map_add,coeff_mk,coeff_succ_mul_X,coeff_one,
      Nat.succ_ne_zero,ite_false, if_false,pow_succ]
    simp

lemma log_subst_exp_sub_one : (log ℚ).subst (exp ℚ-1)=X := by
  apply derivative.ext
  · rw [derivative_subst HasSubst.exp_sub_one,derivative_X,map_sub,derivative_exp,
      derivative_one,sub_zero]
    have h := congrArg (fun f : PowerSeries ℚ=>f.subst (exp ℚ-1))
      deriv_log_mul_one_add_X
    simpa only [subst_mul HasSubst.exp_sub_one,subst_add HasSubst.exp_sub_one,
      subst_one HasSubst.exp_sub_one,subst_X HasSubst.exp_sub_one,add_sub_assoc,add_comm (1 : PowerSeries ℚ),add_sub_cancel_right,sub_add_cancel] using h
  · rw [constantCoeff_X]
    exact constantCoeff_subst_eq_zero
      (show MvPowerSeries.constantCoeff (exp ℚ-1)=0 from by
        change constantCoeff (exp ℚ-1)=0
        simp) _ (constantCoeff_log)

lemma subst_reverse {R : Type*} [CommRing R] (f g : PowerSeries R)
    (hf : constantCoeff f=0) (hg : constantCoeff g=0)
    (hu : IsUnit (coeff 1 f)) (hfg : f.subst g=X) : g.subst f=X := by
  let h := f.substInvOfIsUnit hu
  have hF : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  have hG : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  have hlf : PowerSeries.subst f h=X := subst_substInvOfIsUnit_left f hf hu
  have heq : g=h := by
    calc
      g=PowerSeries.subst g (X : PowerSeries R) := (subst_X hG).symm
      _=PowerSeries.subst g (PowerSeries.subst f h) := by rw [hlf]
      _=PowerSeries.subst (PowerSeries.subst g f) h := by
        rw [subst_comp_subst_apply (R := R) (S := R) (T := R) (υ := Unit) hF hG]
      _=h := by rw [hfg,X_subst]
  simpa only [heq] using hlf

lemma exp_subst_log : (exp ℚ).subst (log ℚ)=1+X := by
  have h := subst_reverse (log ℚ) (exp ℚ-1) (by simp) (by simp)
    (by simp) log_subst_exp_sub_one
  rw [subst_sub HasSubst.log,subst_one HasSubst.log] at h
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

end ElementaryPositivity.FiniteLog

end
section
namespace ElementaryPositivity.FiniteLog
open PowerSeries

variable {A B : Type*} [Ring A] [Ring B] [Algebra ℚ A] [Algebra ℚ B]

noncomputable def nilEval (x : A) (f : PowerSeries ℚ) : A :=
  ∑ i ∈ Finset.range (nilpotencyClass x), coeff i f • x^i

lemma nilEval_eq_sum {x : A} {n : ℕ} (hn : x^n=0) (f : PowerSeries ℚ) :
    nilEval x f=∑ i ∈ Finset.range n,coeff i f • x^i := by
  apply Finset.sum_subset (Finset.range_mono (csInf_le' hn))
  intro i hi hni
  rw [Finset.mem_range,not_lt] at hni
  rw [pow_eq_zero_of_le hni (pow_nilpotencyClass ⟨n,hn⟩),smul_zero]

lemma map_nilEval (φ : A →ₐ[ℚ] B) {x : A} (hx : IsNilpotent x) (f : PowerSeries ℚ) :
    φ (nilEval x f)=nilEval (φ x) f := by
  obtain ⟨n,hn⟩ := hx
  rw [nilEval_eq_sum hn,nilEval_eq_sum (show (φ x)^n=0 by rw [←map_pow,hn,map_zero])]
  simp only [map_sum,map_smul,map_pow]

lemma nilEval_exp {x : A} (hx : IsNilpotent x) : nilEval x (exp ℚ)=IsNilpotent.exp x := by
  obtain ⟨n,hn⟩ := hx
  rw [nilEval_eq_sum hn,IsNilpotent.exp_eq_sum hn]
  congr 1
  ext i
  simp only [coeff_exp,one_div,Algebra.algebraMap_self,RingHom.id_apply]

section CommRing
variable {S : Type*} [CommRing S] [Algebra ℚ S]

omit [Algebra ℚ S] in
lemma substConst_hasSubst {x : S} (hx : IsNilpotent x) : HasSubst (C x : PowerSeries S) := by
  change IsNilpotent (constantCoeff (C x))
  rwa [constantCoeff_C]

lemma nilEval_eq_constantCoeff {x : S} (hx : IsNilpotent x) (f : PowerSeries ℚ) :
    nilEval x f=constantCoeff (PowerSeries.subst (C x : PowerSeries S) f) := by
  rw [show constantCoeff (PowerSeries.subst (C x : PowerSeries S) f)=
    MvPowerSeries.constantCoeff (PowerSeries.subst (C x : PowerSeries S) f) from rfl,
    constantCoeff_subst (substConst_hasSubst hx)]
  simp only [map_pow,show MvPowerSeries.constantCoeff (C x : PowerSeries S)=x from constantCoeff_C x]
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra h
  rw [Finset.mem_coe,Finset.mem_range,not_lt] at h
  apply hi
  change coeff i f • x^i=0
  rw [pow_eq_zero_of_le h (pow_nilpotencyClass hx),smul_zero]

noncomputable def nilEvalAlgHom {x : S} (hx : IsNilpotent x) : PowerSeries ℚ →ₐ[ℚ] S :=
  (constantCoeff : PowerSeries S →+* S).toRatAlgHom.comp (substAlgHom (substConst_hasSubst hx))

lemma nilEvalAlgHom_apply {x : S} (hx : IsNilpotent x) (f : PowerSeries ℚ) :
    nilEvalAlgHom hx f=nilEval x f := by
  rw [nilEval_eq_constantCoeff hx]
  change constantCoeff ((substAlgHom (substConst_hasSubst hx)) f)=_
  rw [coe_substAlgHom]

lemma subst_eq_nilEval {z : PowerSeries S} (hz : IsNilpotent z) (f : PowerSeries ℚ) :
    PowerSeries.subst z f=nilEval z f := by
  ext n
  rw [coeff_subst' (hz.map constantCoeff)]
  simp only [nilEval,map_sum]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra h
  rw [Finset.mem_coe,Finset.mem_range,not_lt] at h
  apply hi
  change coeff i f • coeff n (z^i)=0
  rw [pow_eq_zero_of_le h (pow_nilpotencyClass hz),map_zero,smul_zero]

lemma subst_C_nilEval {x : S} (hx : IsNilpotent x) (f : PowerSeries ℚ) :
    PowerSeries.subst (C x : PowerSeries S) f=C (nilEval x f) := by
  rw [subst_eq_nilEval (hx.map C)]
  exact (map_nilEval (C : S →+* PowerSeries S).toRatAlgHom hx f).symm

lemma nilEval_nilpotent {x : S} (hx : IsNilpotent x) {f : PowerSeries ℚ}
    (hf : constantCoeff f=0) : IsNilpotent (nilEval x f) := by
  rw [nilEval_eq_constantCoeff hx]
  have h := (HasSubst.of_constantCoeff_zero' hf).comp (substConst_hasSubst hx)
  rwa [coe_substAlgHom] at h

lemma nilEval_subst {x : S} (hx : IsNilpotent x) {f : PowerSeries ℚ}
    (hf : constantCoeff f=0) (g : PowerSeries ℚ) :
    nilEval (nilEval x f) g=nilEval x (PowerSeries.subst f g) := by
  calc
    _=constantCoeff (PowerSeries.subst (C (nilEval x f) : PowerSeries S) g) :=
      nilEval_eq_constantCoeff (nilEval_nilpotent hx hf) g
    _=constantCoeff (PowerSeries.subst (PowerSeries.subst (C x : PowerSeries S) f) g) := by
      rw [subst_C_nilEval hx f]
    _=constantCoeff (PowerSeries.subst (C x : PowerSeries S) (PowerSeries.subst f g)) := by
      exact congrArg constantCoeff (subst_comp_subst_apply (R := ℚ) (S := ℚ) (T := S)
        (υ := Unit) (HasSubst.of_constantCoeff_zero' hf) (substConst_hasSubst hx) g).symm
    _=_ := (nilEval_eq_constantCoeff hx (PowerSeries.subst f g)).symm

lemma nilEval_X {x : S} (hx : IsNilpotent x) : nilEval x X=x := by
  rw [nilEval_eq_constantCoeff hx,subst_X (substConst_hasSubst hx),constantCoeff_C]

lemma nilEval_one {x : S} (hx : IsNilpotent x) : nilEval x 1=1 := by
  rw [←nilEvalAlgHom_apply hx,map_one]

lemma nilEval_add {x : S} (hx : IsNilpotent x) (f g : PowerSeries ℚ) :
    nilEval x (f+g)=nilEval x f+nilEval x g := by
  simp only [←nilEvalAlgHom_apply hx,map_add]

lemma nilEval_sub {x : S} (hx : IsNilpotent x) (f g : PowerSeries ℚ) :
    nilEval x (f-g)=nilEval x f-nilEval x g := by
  simp only [←nilEvalAlgHom_apply hx,map_sub]

lemma exp_nilEval_log {x : S} (hx : IsNilpotent x) :
    IsNilpotent.exp (nilEval x (log ℚ))=1+x := by
  rw [←nilEval_exp (nilEval_nilpotent hx constantCoeff_log),
    nilEval_subst hx constantCoeff_log,exp_subst_log,nilEval_add hx,nilEval_one hx,nilEval_X hx]

lemma nilEval_log_exp_sub_one {x : S} (hx : IsNilpotent x) :
    nilEval (IsNilpotent.exp x-1) (log ℚ)=x := by
  rw [←nilEval_exp hx,←nilEval_one hx,←nilEval_sub hx,
    nilEval_subst hx (by simp),log_subst_exp_sub_one,nilEval_X hx]

lemma nilEval_log_mul_comm {x y : S} (hx : IsNilpotent x) (hy : IsNilpotent y) :
    nilEval ((1+x)*(1+y)-1) (log ℚ)=nilEval x (log ℚ)+nilEval y (log ℚ) := by
  have hlx := nilEval_nilpotent hx (constantCoeff_log (A := ℚ))
  have hly := nilEval_nilpotent hy (constantCoeff_log (A := ℚ))
  have hs := nilEval_log_exp_sub_one ((Commute.all _ _).isNilpotent_add hlx hly)
  rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hlx hly,
    exp_nilEval_log hx,exp_nilEval_log hy] at hs
  exact hs

omit [Algebra ℚ S] in
lemma nilpotent_one_add_mul_sub_one {x y : S} (hx : IsNilpotent x) (hy : IsNilpotent y) :
    IsNilpotent ((1+x)*(1+y)-1) := by
  rw [show (1+x)*(1+y)-1=x+y+x*y by ring]
  exact (Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_add hx hy)
    ((Commute.all _ _).isNilpotent_mul_right hx)

end CommRing

open scoped IsMulCommutative in
lemma nilEval_log_mul_of_commute {x y : A} (hxy : Commute x y)
    (hx : IsNilpotent x) (hy : IsNilpotent y) :
    nilEval ((1+x)*(1+y)-1) (log ℚ)=nilEval x (log ℚ)+nilEval y (log ℚ) := by
  let s : Set A := {x,y}
  have hs : ∀ u ∈ s, ∀ v ∈ s, u*v=v*u := by
    intro u hu v hv
    rcases hu with rfl | hu
    · rcases hv with rfl | hv
      · rfl
      · rw [Set.mem_singleton_iff] at hv
        subst v
        exact hxy.eq
    · rw [Set.mem_singleton_iff] at hu
      subst u
      rcases hv with rfl | hv
      · exact hxy.eq.symm
      · rw [Set.mem_singleton_iff] at hv
        subst v
        rfl
  let T := Algebra.adjoin ℚ s
  let : IsMulCommutative T := Algebra.isMulCommutative_adjoin ℚ
    (fun left hleft right hright => hs left hleft right hright)
  let : CommRing T := inferInstance
  let tx : T := ⟨x,Algebra.subset_adjoin (Set.mem_insert x _)⟩
  let ty : T := ⟨y,Algebra.subset_adjoin (Set.mem_insert_of_mem x (Set.mem_singleton y))⟩
  have htx : IsNilpotent tx := by
    obtain ⟨n,hn⟩ := hx
    exact ⟨n,Subtype.ext hn⟩
  have hty : IsNilpotent ty := by
    obtain ⟨n,hn⟩ := hy
    exact ⟨n,Subtype.ext hn⟩
  have h := congrArg (Algebra.adjoin ℚ s).val (nilEval_log_mul_comm htx hty)
  rw [map_nilEval _ (nilpotent_one_add_mul_sub_one htx hty),map_add,
    map_nilEval _ htx,map_nilEval _ hty,map_sub,map_mul,map_add,map_add,map_one] at h
  exact h

end ElementaryPositivity.FiniteLog

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalPolynomialDivisibility
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SymbolCoordinates
open MvPolynomial
variable {σ A : Type*} [CommRing A] [Algebra ℚ A]

variable {ι : Type*} (b : Module.Basis ι ℚ A)

lemma coordinates_detect (f : MvPolynomial σ A) (h : ∀ i,coordinate b i f=0) : f=0 := by
  ext m
  apply b.repr.injective
  ext i
  have hh:=congrArg (fun polynomial : MvPolynomial σ ℚ => polynomial.coeff m) (h i)
  simpa using hh

theorem scalar_mul_eq_zero_iff (p : MvPolynomial σ ℚ) (hp : p≠0) (f : MvPolynomial σ A) :
    MvPolynomial.map (algebraMap ℚ A) p * f=0 ↔ f=0 := by
  constructor
  · intro hf
    apply coordinates_detect (Module.Free.chooseBasis ℚ A)
    intro i
    have h:=congrArg (coordinate (Module.Free.chooseBasis ℚ A) i) hf
    rw [coordinate_scalar_mul,map_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hp
  · rintro rfl
    exact mul_zero _

end ElementaryPositivity.SymbolCoordinates

namespace ElementaryPositivity.CenterCalculus
open MvPolynomial ElementaryPositivity.SymbolCoordinates
variable {A σ : Type*} [CommRing A] [Algebra ℚ A]

theorem scalar_mul_eq_zero (p : MvPolynomial σ ℚ) (hp : p≠0)
    (q : MvPolynomial σ A) (h : map (algebraMap ℚ A) p*q=0) : q=0 :=
  (scalar_mul_eq_zero_iff p hp q).mp h

theorem scalar_mul_injective (p : MvPolynomial σ ℚ) (hp : p≠0) :
    Function.Injective (fun q : MvPolynomial σ A=>map (algebraMap ℚ A) p*q) := by
  intro q r h
  dsimp only at h
  apply sub_eq_zero.mp
  apply scalar_mul_eq_zero p hp
  rw [mul_sub,h,sub_self]

end ElementaryPositivity.CenterCalculus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TaylorSCoeffHomogeneous
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.Regroup.assocInv_centers_left _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.Regroup.assocInv_centers_mid _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centerTranslation_tmul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.componentFinsupp_apply _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.leafVarsEquiv_center _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.leafVarsEquiv_pack _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.tensorValue_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem componentTensor_detect (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (f : tensor (quotientFamily a μ) T)
    (h : ∀ k,componentTensor a μ T k f=0) : f=0 := by
  obtain ⟨s,hs,he⟩ := componentTensor_finite_decomposition a μ T f
  rw [← he]
  simp [h]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorPolynomialBox
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
open scoped TensorProduct
variable {α β A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]

lemma box_mul (p p' : MvPolynomial α A) (q q' : MvPolynomial β B) :
    box (p*p') (q*q') = box p q * box p' q' := by
  simp only [box,map_mul]
  ring

lemma box_scalar (p : MvPolynomial α ℚ) (q : MvPolynomial β ℚ) :
    box (map (algebraMap ℚ A) p) (map (algebraMap ℚ B) q) =
      map (algebraMap ℚ (A ⊗[ℚ] B)) (rename Sum.inl p * rename Sum.inr q) := by
  have hL : (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A ⊗[ℚ] B).toRingHom.comp
      (algebraMap ℚ A)=algebraMap ℚ (A ⊗[ℚ] B) := by
    ext r
    exact (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A ⊗[ℚ] B).commutes r
  have hR : (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A ⊗[ℚ] B).toRingHom.comp
      (algebraMap ℚ B)=algebraMap ℚ (A ⊗[ℚ] B) := by
    ext r
    exact (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A ⊗[ℚ] B).commutes r
  simp only [box,map_mul,map_rename,map_map,hL,hR]

lemma box_scalar_left (p : MvPolynomial α ℚ) (q : MvPolynomial β ℚ)
    (f : MvPolynomial α A) (g : MvPolynomial β B) :
    box (map (algebraMap ℚ A) p*f) (map (algebraMap ℚ B) q*g)=
      map (algebraMap ℚ (A ⊗[ℚ] B)) (rename Sum.inl p*rename Sum.inr q)*box f g := by
  rw [box_mul,box_scalar]
end ElementaryPositivity.CenterCalculus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PointEvaluation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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

def centerPairs (T : SplitTree I) : Finset (T.Centers × T.Centers) :=
  Finset.univ.filter (fun ij=>ij.1 < ij.2)

omit [Fintype I] [DecidableEq I] in
lemma centerPairs_ne (T : SplitTree I) (ij : T.Centers×T.Centers) (h : ij∈T.centerPairs) :
    ij.1≠ij.2 := (Finset.mem_filter.mp h).2.ne

omit [Fintype I] [DecidableEq I] in
lemma centerPairs_norev (T : SplitTree I) (ij : T.Centers×T.Centers) (h : ij∈T.centerPairs) :
    (ij.2,ij.1)∉T.centerPairs := by
  intro hr
  exact lt_asymm (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp hr).2

noncomputable def centerNumerator (a : I → I → ℕ) (T : SplitTree I)
    (s : Finset (T.Centers×T.Centers)) : MvPolynomial T.Centers ℚ :=
  ∏ ij∈s,diagonal ij.1 ij.2 ^ (eulerForm a (T.leafDimension ij.1) (T.leafDimension ij.2)).toNat

omit [DecidableEq I] in
lemma centerDenominator_ne_zero (a : I → I → ℕ) (T : SplitTree I) :
    centerDenominator a T T.centerPairs≠0 := by
  exact Finset.prod_ne_zero_iff.mpr fun ij hij=>
    pow_ne_zero _ (diagonal_ne_zero (T.centerPairs_ne ij hij))

def PairSymmetric (a : I → I → ℕ) (T : SplitTree I) : Prop :=
  ∀ ij∈T.centerPairs,eulerForm a (T.leafDimension ij.1) (T.leafDimension ij.2) =
    eulerForm a (T.leafDimension ij.2) (T.leafDimension ij.1)

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SymbolDetection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def filtrationDimensionEquiv (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e : I → ℕ} (h : d=e) (W : ℤ) :
    sourceFiltration a c η hc θ d W ≃ₗ[ℚ] sourceFiltration a c η hc θ e W := by
  subst e
  exact LinearEquiv.refl ℚ _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RefinedTensorDetection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
variable {A σ : Type*} [CommRing A] [Algebra ℚ A]
lemma lineSpecialization_coeff_zero (v h : σ → ℚ) (p : MvPolynomial σ A) :
    (lineSpecialization v h p).coeff 0=evalRat v p := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have he:=lineSpecialization_eval v h p 0
  simpa only [map_zero,mul_zero,add_zero] using he
lemma evalRat_map_algebra_eq (v : σ → ℚ) (p : MvPolynomial σ ℚ) :
    evalRat (A:=A) v (map (algebraMap ℚ A) p)=algebraMap ℚ A (evalRat v p) := by
  rw [← lineSpecialization_coeff_zero v (fun _=>0),lineSpecialization_map_algebra,
    Polynomial.coeff_map,lineSpecialization_coeff_zero]
end ElementaryPositivity.CenterCalculus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TripleFiltration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
lemma additiveTensorFiltration_top (F : ℤ → Submodule K M) (G : ℤ → Submodule K N)
    (U V : ℤ) (hF : F U=⊤) (hG : G V=⊤) : additiveTensorFiltration F G (U+V)=⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using OAI.tensorInductionOn with
  | tmul x y =>
    exact tmul_mem_additiveTensorFiltration F G (le_refl _) (hF ▸ trivial) (hG ▸ trivial)
  | add x y hx hy => exact (additiveTensorFiltration F G (U+V)).add_mem hx hy
end ElementaryPositivity.LinearDetection

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TensorFiltrationInterchange
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

lemma assoc_mem_tensorFiltration (F : ℤ → Submodule K A) (G : ℤ → Submodule K B)
    (H : ℤ → Submodule K C) (W : ℤ) (x : (A⊗[K]B)⊗[K]C)
    (hx : x∈additiveTensorFiltration (additiveTensorFiltration F G) H W) :
    TensorProduct.assoc K A B C x∈additiveTensorFiltration F (additiveTensorFiltration G H) W := by
  let J:=additiveTensorFiltration F (additiveTensorFiltration G H) W
  let τ:=TensorProduct.assoc K A B C
  change τ x∈J
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨u,v,x,z,huv,hx,hz,rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨r,s,x,y,hrs,hx,hy,rfl⟩
      change x⊗ₜ[K](y⊗ₜ[K]z)∈J
      exact tmul_mem_additiveTensorFiltration _ _ (show W ≤ r+(s+v) by omega) hx
        (tmul_mem_additiveTensorFiltration _ _ (le_refl _) hy hz)
    | zero => rw [TensorProduct.zero_tmul,τ.map_zero]; exact J.zero_mem
    | add x y _ _ hx hy => rw [TensorProduct.add_tmul,τ.map_add]; exact J.add_mem hx hy
    | smul r x _ hx => rw [←TensorProduct.smul_tmul',τ.map_smul]; exact J.smul_mem r hx
  | zero => rw [map_zero]; exact J.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact J.add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact J.smul_mem r hx

lemma unassoc_mem_tensorFiltration (F : ℤ → Submodule K A) (G : ℤ → Submodule K B)
    (H : ℤ → Submodule K C) (W : ℤ) (x : A⊗[K](B⊗[K]C))
    (hx : x∈additiveTensorFiltration F (additiveTensorFiltration G H) W) :
    (TensorProduct.assoc K A B C).symm x∈additiveTensorFiltration (additiveTensorFiltration F G) H W := by
  let J:=additiveTensorFiltration (additiveTensorFiltration F G) H W
  let τ:=(TensorProduct.assoc K A B C).symm
  change τ x∈J
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨u,v,x,z,huv,hx,hz,rfl⟩
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨r,s,y,z,hrs,hy,hz,rfl⟩
      change (x⊗ₜ[K]y)⊗ₜ[K]z∈J
      exact tmul_mem_additiveTensorFiltration _ _ (show W≤(u+r)+s by omega)
        (tmul_mem_additiveTensorFiltration _ _ (le_refl _) hx hy) hz
    | zero => rw [TensorProduct.tmul_zero,τ.map_zero]; exact J.zero_mem
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add,τ.map_add]; exact J.add_mem hy hz
    | smul r z _ hz => rw [TensorProduct.tmul_smul,τ.map_smul]; exact J.smul_mem r hz
  | zero => rw [map_zero]; exact J.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact J.add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact J.smul_mem r hx

end ElementaryPositivity.LinearDetection

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GradedCoproduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open SeparationInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def separationCoefficientRestricted (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W j : ℤ) :
    sourceFiltration a c η hc θ (d+e) W →ₗ[ℚ] sourceTensorFiltration a c η hc θ d e W :=
  ((separationCoefficient a c η hc hs j).comp
    (sourceFiltration a c η hc θ (d+e) W).subtype).codRestrict
      (sourceTensorFiltration a c η hc θ d e W)
      (fun f=>separationCoefficient_filtration a c η hc θ d e hs W j f.val f.property)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalCoproductUnits
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.ShufflePolynomiality
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

namespace Regroup
lemma filtrationDimensionEquiv_val (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e : I → ℕ} (h : d=e) (W : ℤ)
    (f : sourceFiltration a c η hc θ d W) :
    (filtrationDimensionEquiv a c η hc θ h W f).val=
      dimensionEquivB a (SlopeArithmetic.slope c η) h f.val := by
  subst e
  rfl

lemma weightComponent_natural (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {T U : SplitTree I} (e : Regroup T U) (W : ℤ) (x : tensor (quotientFamily a μ) T) :
    e.equivalence (quotientFamily a μ) (weightComponent a μ T W x)=
      weightComponent a μ U W (e.equivalence (quotientFamily a μ) x) := by
  classical
  apply sub_eq_zero.mp
  apply componentTensor_detect a μ U
  intro k
  rw [map_sub]
  apply sub_eq_zero.mpr
  obtain ⟨j,rfl⟩:=e.degrees.surjective k
  rw [←componentTensor_natural,componentTensor_weightComponent,
    componentTensor_weightComponent,e.totalDegree,e.doubleShift]
  split_ifs
  · exact componentTensor_natural a μ e j x
  · exact map_zero _

def OrderPreserving {T U : SplitTree I} (e : Regroup T U) : Prop :=
  ∀ i j : T.Centers,e.centers i<e.centers j ↔ i<j

omit [Fintype I] [DecidableEq I] in
lemma assoc_orderPreserving (T U V : SplitTree I) : OrderPreserving (.assoc T U V) := by
  intro i j
  change Sum.Lex (· < · : T.Centers → T.Centers → Prop)
      (Sum.Lex (· < · : U.Centers → U.Centers → Prop) (· < · : V.Centers → V.Centers → Prop))
      ((Equiv.sumAssoc T.Centers U.Centers V.Centers) i)
      ((Equiv.sumAssoc T.Centers U.Centers V.Centers) j) ↔
    Sum.Lex (Sum.Lex (· < · : T.Centers → T.Centers → Prop) (· < · : U.Centers → U.Centers → Prop))
      (· < · : V.Centers → V.Centers → Prop) i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
    simp [Equiv.sumAssoc,Sum.lex_inl_inl,Sum.lex_inr_inr,Sum.lex_inr_inl,Sum.Lex.sep]

omit [DecidableEq I] in
lemma centerPower_natural (a : I → I → ℕ) {T U : SplitTree I} (e : Regroup T U)
    (he : e.OrderPreserving) (φ : ℤ → ℕ) :
    rename e.centers (∏ ij∈T.centerPairs,
      diagonal ij.1 ij.2 ^ φ (eulerForm a (T.leafDimension ij.1) (T.leafDimension ij.2)))=
      ∏ ij∈U.centerPairs,
        diagonal ij.1 ij.2 ^ φ (eulerForm a (U.leafDimension ij.1) (U.leafDimension ij.2)) := by
  classical
  simp only [centerPairs,Finset.prod_filter,map_prod,apply_ite,map_pow,map_one,
    diagonal,map_sub,rename_X]
  apply Fintype.prod_equiv (Equiv.prodCongr e.centers e.centers)
  intro ij
  simp only [Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,he ij.1 ij.2,e.leafDimension]

omit [DecidableEq I] in
lemma centerNumerator_natural (a : I → I → ℕ) {T U : SplitTree I} (e : Regroup T U)
    (he : e.OrderPreserving) :
    rename e.centers (centerNumerator a T T.centerPairs)=centerNumerator a U U.centerPairs :=
  centerPower_natural a e he Int.toNat

omit [DecidableEq I] in
lemma centerDenominator_natural (a : I → I → ℕ) {T U : SplitTree I} (e : Regroup T U)
    (he : e.OrderPreserving) :
    rename e.centers (centerDenominator a T T.centerPairs)=centerDenominator a U U.centerPairs :=
  centerPower_natural a e he (fun z=>(-z).toNat)

end Regroup
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FilteredTensorComm
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
open LinearDetection
open scoped TensorProduct
variable {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]

lemma comm_mem_tensorFiltration (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W : ℤ) (x : M ⊗[ℚ] N) (hx : x∈additiveTensorFiltration F G W) :
    TensorProduct.comm ℚ M N x∈additiveTensorFiltration G F W := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨u,v,x,y,h,hx,hy,rfl⟩
    exact tmul_mem_additiveTensorFiltration G F (by omega) hy hx
  | zero => simpa only [map_zero] using (additiveTensorFiltration G F W).zero_mem
  | add x y hx hy hix hiy => simpa only [map_add] using (additiveTensorFiltration G F W).add_mem hix hiy
  | smul r x hx hix => simpa only [map_smul] using (additiveTensorFiltration G F W).smul_mem r hix

noncomputable def tensorFiltrationComm (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W : ℤ) : additiveTensorFiltration F G W ≃ₗ[ℚ] additiveTensorFiltration G F W :=
  { restrict _ _ (TensorProduct.comm ℚ M N).toLinearMap (comm_mem_tensorFiltration F G W) with
    invFun := fun x=>⟨TensorProduct.comm ℚ N M x.val,comm_mem_tensorFiltration G F W x.val x.property⟩
    left_inv := fun x=>by apply Subtype.ext; exact (TensorProduct.comm ℚ M N).symm_apply_apply x.val
    right_inv := fun x=>by apply Subtype.ext; exact (TensorProduct.comm ℚ M N).apply_symm_apply x.val }

noncomputable def tensorGradeComm (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (W : ℤ) : Grade (additiveTensorFiltration F G W) (additiveTensorFiltration F G (W+1)) →ₗ[ℚ]
      Grade (additiveTensorFiltration G F W) (additiveTensorFiltration G F (W+1)) :=
  map _ _ _ _ (TensorProduct.comm ℚ M N).toLinearMap
    (comm_mem_tensorFiltration F G W) (comm_mem_tensorFiltration F G (W+1))

end ElementaryPositivity.LinearFiltration

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CoproductIteration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.LinearDetection ElementaryPositivity.LinearFiltration
open SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma tensorSeparationLeft_filtration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (W : ℤ) (x : B a (SlopeArithmetic.slope c η) (d+e)⊗[ℚ]B a (SlopeArithmetic.slope c η) f)
    (hx : x∈sourceTensorFiltration a c η hc θ (d+e) f W) :
    TensorProduct.map (separationCoefficient a c η hc hs 0) LinearMap.id x∈
      sourceTripleFiltration a c η hc θ d e f W :=
  tensor_map_mem_filtration (sourceFiltration a c η hc θ (d+e)) (sourceFiltration a c η hc θ f)
    (sourceTensorFiltration a c η hc θ d e) (sourceFiltration a c η hc θ f)
    (separationCoefficient a c η hc hs 0) LinearMap.id
    (fun w=>separationCoefficient_filtration a c η hc θ d e hs w 0) (fun _ _ h=>h) W x hx

noncomputable def tensorSeparationLeft (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W : ℤ) :
    sourceTensorFiltration a c η hc θ (d+e) f W →ₗ[ℚ]
      sourceTripleFiltration a c η hc θ d e f W :=
  let C : B a (SlopeArithmetic.slope c η) (d+e) →ₗ[ℚ]
      B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e :=
    separationCoefficient a c η hc hs 0
  let F : (B a (SlopeArithmetic.slope c η) (d+e)⊗[ℚ]B a (SlopeArithmetic.slope c η) f) →ₗ[ℚ]
      ((B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e)⊗[ℚ]
        B a (SlopeArithmetic.slope c η) f) := TensorProduct.map C LinearMap.id
  (F.comp (sourceTensorFiltration a c η hc θ (d+e) f W).subtype).codRestrict
    (sourceTripleFiltration a c η hc θ d e f W)
    (fun x=>tensorSeparationLeft_filtration a c η hc θ d e f hs W x.val x.property)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SignedCoproductGridGrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open ElementaryPositivity.PackConvolution ElementaryPositivity.LinearDetection
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

lemma unitalSourceTensorFiltration_antitone (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : I → ℕ) :
    Antitone (unitalSourceTensorFiltration a c η hc θ d e) :=
  additiveTensorFiltration_antitone _ _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_Grade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
variable {M : Type*} [AddCommGroup M] [Module ℚ M]

lemma grade_same_subsingleton (F : Submodule ℚ M) : Subsingleton (Grade F F) := by
  have h : next F F=⊤ := by ext x; simp [next]
  change Subsingleton (F ⧸ next F F)
  rw [h]
  infer_instance
end ElementaryPositivity.LinearFiltration

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalCoproductComparison
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cocommTensorBCommRing cocommTensorBAlgebra

lemma filtrationDimensionEquiv_castB (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e : I → ℕ} (h : d=e) (W : ℤ)
    (f : sourceFiltration a c η hc θ d W) :
    (filtrationDimensionEquiv a c η hc θ h W f).val=castB a (slope c η) h f.val := by
  subst e
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalCoproductCocommutative
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma unitalGradeCast_trans (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e f : I → ℕ} {U V W : ℤ}
    (hde : d=e) (hef : e=f) (hUV : U=V) (hVW : V=W)
    (x : UnitalSourceGrade a c η hc θ d U) :
    unitalGradeCast a c η hc θ hef hVW (unitalGradeCast a c η hc θ hde hUV x)=
      unitalGradeCast a c η hc θ (hde.trans hef) (hUV.trans hVW) x := by
  subst e; subst f; subst V; subst W
  rfl

namespace DimensionSplit

def swap {d : I → ℕ} (s : DimensionSplit d) : DimensionSplit d :=
  ofPair (right s) (left s) ((add_comm _ _).trans (left_add_right s))
omit [Fintype I] [DecidableEq I] in
@[simp] lemma left_swap {d : I → ℕ} (s : DimensionSplit d) : left (swap s)=right s :=
  left_ofPair _ _ _
omit [Fintype I] [DecidableEq I] in
@[simp] lemma right_swap {d : I → ℕ} (s : DimensionSplit d) : right (swap s)=left s :=
  right_ofPair _ _ _
omit [Fintype I] [DecidableEq I] in
@[simp] lemma swap_swap {d : I → ℕ} (s : DimensionSplit d) : swap (swap s)=s := by
  apply DimensionSplit.ext
  simp only [left_swap,right_swap]
end DimensionSplit

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TensorGradeFunctor
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
open ElementaryPositivity.LinearDetection
open scoped TensorProduct DirectSum
variable {M N M' N' X Y X' Y' : Type*}
  [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  [AddCommGroup M'] [Module ℚ M'] [AddCommGroup N'] [Module ℚ N']
  [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]
  [AddCommGroup X'] [Module ℚ X'] [AddCommGroup Y'] [Module ℚ Y']

abbrev FGrade (F : ℤ → Submodule ℚ M) (u : ℤ) := Grade (F u) (F (u+1))

noncomputable def gradeMap (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (f : M →ₗ[ℚ] N) (hf : ∀ w x,x∈F w → f x∈G w) (W : ℤ) :
    FGrade F W →ₗ[ℚ] FGrade G W :=
  map (F W) (F (W+1)) (G W) (G (W+1)) f (hf W) (hf (W+1))

lemma gradeMap_id (F : ℤ → Submodule ℚ M)
    (hf : ∀ w x,x∈F w → LinearMap.id (R:=ℚ) (M:=M) x∈F w) (W : ℤ) :
    gradeMap F F LinearMap.id hf W=LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x => rfl

noncomputable def tensorGradeMap (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (F' : ℤ → Submodule ℚ M') (G' : ℤ → Submodule ℚ N')
    (f : M →ₗ[ℚ] M') (g : N →ₗ[ℚ] N')
    (hf : ∀ w x,x∈F w → f x∈F' w) (hg : ∀ w y,y∈G w → g y∈G' w) (W : ℤ) :
    TensorGrade F G W →ₗ[ℚ] TensorGrade F' G' W :=
  gradeMap (additiveTensorFiltration F G) (additiveTensorFiltration F' G')
    (TensorProduct.map f g) (tensor_map_mem_filtration F G F' G' f g hf hg) W

lemma tensorGradeMap_part (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (F' : ℤ → Submodule ℚ M') (G' : ℤ → Submodule ℚ N')
    (f : M →ₗ[ℚ] M') (g : N →ₗ[ℚ] N')
    (hf : ∀ w x,x∈F w → f x∈F' w) (hg : ∀ w y,y∈G w → g y∈G' w) (W u : ℤ)
    (x : FGrade F u) (y : FGrade G (W-u)) :
    tensorGradeMap F G F' G' f g hf hg W (tensorGradeInclusionW F G W u (x⊗ₜ[ℚ]y))=
      tensorGradeInclusionW F' G' W u
        (gradeMap F F' f hf u x⊗ₜ[ℚ]gradeMap G G' g hg (W-u) y) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y => rfl

noncomputable def tensorGradeLift (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G)
    (f : ∀ u,FGrade F u →ₗ[ℚ] X) (g : ∀ v,FGrade G v →ₗ[ℚ] Y) (W : ℤ) :
    TensorGrade F G W →ₗ[ℚ] X⊗[ℚ]Y :=
  (DirectSum.toModule ℚ ℤ (X⊗[ℚ]Y) (fun u=>TensorProduct.map (f u) (g (W-u)))).comp
    (tensorGradeEquiv F G hF hG W).symm.toLinearMap

lemma tensorGradeLift_part (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G)
    (f : ∀ u,FGrade F u →ₗ[ℚ] X) (g : ∀ v,FGrade G v →ₗ[ℚ] Y) (W u : ℤ)
    (x : FGrade F u) (y : FGrade G (W-u)) :
    tensorGradeLift F G hF hG f g W (tensorGradeInclusionW F G W u (x⊗ₜ[ℚ]y))=
      f u x⊗ₜ[ℚ]g (W-u) y := by
  change DirectSum.toModule ℚ ℤ _ _ ((tensorGradeEquiv F G hF hG W).symm _) = _
  rw [tensorGradeEquiv_symm_inclusion,DirectSum.toModule_lof,TensorProduct.map_tmul]

lemma tensorGradeLift_map_natural (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (F' : ℤ → Submodule ℚ M') (G' : ℤ → Submodule ℚ N')
    (hF : Antitone F) (hG : Antitone G) (hF' : Antitone F') (hG' : Antitone G')
    (f : M →ₗ[ℚ] M') (g : N →ₗ[ℚ] N')
    (hf : ∀ w x,x∈F w → f x∈F' w) (hg : ∀ w y,y∈G w → g y∈G' w)
    (l : ∀ u,FGrade F' u →ₗ[ℚ] X) (r : ∀ v,FGrade G' v →ₗ[ℚ] Y)
    (W : ℤ) (x : TensorGrade F G W) :
    tensorGradeLift F' G' hF' hG' l r W (tensorGradeMap F G F' G' f g hf hg W x)=
      tensorGradeLift F G hF hG (fun u=>(l u).comp (gradeMap F F' f hf u))
        (fun v=>(r v).comp (gradeMap G G' g hg v)) W x := by
  induction x using tensorGrade_induction F G hF hG W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht u x y => rw [tensorGradeMap_part,tensorGradeLift_part,tensorGradeLift_part]; rfl

lemma tensorGradeLift_comp (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G)
    (f : ∀ u,FGrade F u →ₗ[ℚ] X) (g : ∀ v,FGrade G v →ₗ[ℚ] Y)
    (l : X →ₗ[ℚ] X') (r : Y →ₗ[ℚ] Y') (W : ℤ) (x : TensorGrade F G W) :
    TensorProduct.map l r (tensorGradeLift F G hF hG f g W x)=
      tensorGradeLift F G hF hG (fun u=>l.comp (f u)) (fun v=>r.comp (g v)) W x := by
  induction x using tensorGrade_induction F G hF hG W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht u x y => rw [tensorGradeLift_part,tensorGradeLift_part,TensorProduct.map_tmul]; rfl

end ElementaryPositivity.LinearFiltration

end
section
namespace ElementaryPositivity.LinearFiltration
open ElementaryPositivity.LinearDetection
open scoped TensorProduct DirectSum
variable {M N P X Y Z : Type*}
  [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  [AddCommGroup P] [Module ℚ P] [AddCommGroup X] [Module ℚ X]
  [AddCommGroup Y] [Module ℚ Y] [AddCommGroup Z] [Module ℚ Z]

lemma tensorGradeLift_mk_tmul (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G)
    (f : ∀ u,FGrade F u →ₗ[ℚ] X) (g : ∀ v,FGrade G v →ₗ[ℚ] Y)
    (W u v : ℤ) (h : u+v=W) (x : F u) (y : G v) :
    tensorGradeLift F G hF hG f g W
      (mk _ _ ⟨x.val⊗ₜ[ℚ]y.val,tmul_mem_additiveTensorFiltration F G (by omega) x.property y.property⟩)=
      f u (mk _ _ x)⊗ₜ[ℚ]g v (mk _ _ y) := by
  have hv : v=W-u := by omega
  subst v
  exact tensorGradeLift_part F G hF hG f g W u (mk _ _ x) (mk _ _ y)

noncomputable def tensorGradeAssoc (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (H : ℤ → Submodule ℚ P) (W : ℤ) :
    TensorGrade (additiveTensorFiltration F G) H W →ₗ[ℚ]
      TensorGrade F (additiveTensorFiltration G H) W :=
  gradeMap (additiveTensorFiltration (additiveTensorFiltration F G) H)
    (additiveTensorFiltration F (additiveTensorFiltration G H))
    (TensorProduct.assoc ℚ M N P).toLinearMap (assoc_mem_tensorFiltration F G H) W

lemma tensorGradeLift_assoc (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (H : ℤ → Submodule ℚ P) (hF : Antitone F) (hG : Antitone G) (hH : Antitone H)
    (f : ∀ u,FGrade F u →ₗ[ℚ] X) (g : ∀ v,FGrade G v →ₗ[ℚ] Y)
    (h : ∀ w,FGrade H w →ₗ[ℚ] Z) (W : ℤ)
    (x : TensorGrade (additiveTensorFiltration F G) H W) :
    tensorGradeLift F (additiveTensorFiltration G H) hF (additiveTensorFiltration_antitone G H)
      f (tensorGradeLift G H hG hH g h) W (tensorGradeAssoc F G H W x)=
    TensorProduct.assoc ℚ X Y Z
      (tensorGradeLift (additiveTensorFiltration F G) H (additiveTensorFiltration_antitone F G) hH
        (tensorGradeLift F G hF hG f g) h W x) := by
  induction x using tensorGrade_induction (additiveTensorFiltration F G) H
    (additiveTensorFiltration_antitone F G) hH W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht u x z =>
    induction x using tensorGrade_induction F G hF hG u with
    | hz => simp only [TensorProduct.zero_tmul,map_zero]
    | ha x y hx hy => simp only [TensorProduct.add_tmul,map_add,hx,hy]
    | ht r x y =>
      rw [tensorGradeLift_part,tensorGradeLift_part,TensorProduct.assoc_tmul]
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        induction y using Submodule.Quotient.induction_on with
        | H y =>
          induction z using Submodule.Quotient.induction_on with
          | H z =>
            let yz : additiveTensorFiltration G H (W-r) :=
              ⟨y.val⊗ₜ[ℚ]z.val,tmul_mem_additiveTensorFiltration G H (by omega) y.property z.property⟩
            have houter := tensorGradeLift_mk_tmul F (additiveTensorFiltration G H)
              hF (additiveTensorFiltration_antitone G H) f (tensorGradeLift G H hG hH g h)
              W r (W-r) (by omega) x yz
            refine houter.trans ?_
            exact congrArg (fun t=>f r (mk _ _ x)⊗ₜ[ℚ]t)
              (tensorGradeLift_mk_tmul G H hG hH g h (W-r) (u-r) (W-u) (by omega) y z)

end ElementaryPositivity.LinearFiltration

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TensorGradeFiniteSum
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
open scoped TensorProduct
variable {M N X Y D : Type*} [AddCommGroup M] [Module ℚ M]
  [AddCommGroup N] [Module ℚ N] [AddCommGroup X] [Module ℚ X]
  [AddCommGroup Y] [Module ℚ Y] [Fintype D]

lemma tensorGradeLift_sum_left (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G)
    (f : D → ∀ u,FGrade F u →ₗ[ℚ] X) (g : ∀ v,FGrade G v →ₗ[ℚ] Y)
    (W : ℤ) (x : TensorGrade F G W) :
    tensorGradeLift F G hF hG (fun u=>∑ d,f d u) g W x=
      ∑ d,tensorGradeLift F G hF hG (f d) g W x := by
  induction x using tensorGrade_induction F G hF hG W with
  | hz => simp only [map_zero,Finset.sum_const_zero]
  | ha x y hx hy => simp only [map_add,hx,hy,Finset.sum_add_distrib]
  | ht u x y => simp only [tensorGradeLift_part,LinearMap.sum_apply,TensorProduct.sum_tmul]

lemma tensorGradeLift_sum_right (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G)
    (f : ∀ u,FGrade F u →ₗ[ℚ] X) (g : D → ∀ v,FGrade G v →ₗ[ℚ] Y)
    (W : ℤ) (x : TensorGrade F G W) :
    tensorGradeLift F G hF hG f (fun v=>∑ d,g d v) W x=
      ∑ d,tensorGradeLift F G hF hG f (g d) W x := by
  induction x using tensorGrade_induction F G hF hG W with
  | hz => simp only [map_zero,Finset.sum_const_zero]
  | ha x y hx hy => simp only [map_add,hx,hy,Finset.sum_add_distrib]
  | ht u x y => simp only [tensorGradeLift_part,LinearMap.sum_apply,TensorProduct.tmul_sum]
end ElementaryPositivity.LinearFiltration

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalCoproductIteration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def globalGradeLof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d : slopeDimensions c η hc θ) (u : ℤ) :
    FGrade (unitalSourceFiltration a c η hc θ d.val) u →ₗ[ℚ] UnitalShuffle a c η hc θ :=
  DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,u)

noncomputable def globalSplitGradeCoproduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d : slopeDimensions c η hc θ)
    (s : SlopeSplit c η hc θ d.val) (u : ℤ) :
    FGrade (unitalSourceFiltration a c η hc θ d.val) u →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  globalSplitCoproduct a c η hc θ (d,u) s

lemma globalCoproduct_tensor_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    TensorProduct.map (globalCoproduct a c η hc θ) LinearMap.id
      (globalTensorGradeInclusion a c η hc θ d e W x)=
      ∑ s : SlopeSplit c η hc θ d.val,
        tensorGradeLift (unitalSourceFiltration a c η hc θ d.val)
          (unitalSourceFiltration a c η hc θ e.val)
          (unitalSourceFiltration_antitone a c η hc θ d.val)
          (unitalSourceFiltration_antitone a c η hc θ e.val)
          (fun u=>globalSplitGradeCoproduct a c η hc θ d s u)
          (fun v=>globalGradeLof a c η hc θ e v) W x := by
  have hh : (fun u=>(globalCoproduct a c η hc θ).comp
      (globalGradeLof a c η hc θ d u))=
      (fun u=>∑ s : SlopeSplit c η hc θ d.val,globalSplitGradeCoproduct a c η hc θ d s u) := by
    funext u
    apply LinearMap.ext
    intro y
    change globalCoproduct a c η hc θ (globalGradeLof a c η hc θ d u y)=_
    exact (globalCoproduct_lof a c η hc θ (d,u) y).trans
      (LinearMap.sum_apply Finset.univ (fun s : SlopeSplit c η hc θ d.val=>
        globalSplitCoproduct a c η hc θ (d,u) s) y).symm
  have H := tensorGradeLift_comp
    (unitalSourceFiltration a c η hc θ d.val) (unitalSourceFiltration a c η hc θ e.val)
    (unitalSourceFiltration_antitone a c η hc θ d.val)
    (unitalSourceFiltration_antitone a c η hc θ e.val)
    (fun u=>globalGradeLof a c η hc θ d u)
    (fun v=>globalGradeLof a c η hc θ e v)
    (globalCoproduct a c η hc θ) LinearMap.id W x
  simp only [LinearMap.id_comp,hh] at H
  exact H.trans (tensorGradeLift_sum_left _ _ _ _
    (fun s u=>globalSplitGradeCoproduct a c η hc θ d s u)
    (fun v=>globalGradeLof a c η hc θ e v) W x)

lemma globalCoproduct_tensor_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    TensorProduct.map LinearMap.id (globalCoproduct a c η hc θ)
      (globalTensorGradeInclusion a c η hc θ d e W x)=
      ∑ s : SlopeSplit c η hc θ e.val,
        tensorGradeLift (unitalSourceFiltration a c η hc θ d.val)
          (unitalSourceFiltration a c η hc θ e.val)
          (unitalSourceFiltration_antitone a c η hc θ d.val)
          (unitalSourceFiltration_antitone a c η hc θ e.val)
          (fun v=>globalGradeLof a c η hc θ d v)
          (fun u=>globalSplitGradeCoproduct a c η hc θ e s u) W x := by
  have hh : (fun u=>(globalCoproduct a c η hc θ).comp
      (globalGradeLof a c η hc θ e u))=
      (fun u=>∑ s : SlopeSplit c η hc θ e.val,globalSplitGradeCoproduct a c η hc θ e s u) := by
    funext u
    apply LinearMap.ext
    intro y
    change globalCoproduct a c η hc θ (globalGradeLof a c η hc θ e u y)=_
    exact (globalCoproduct_lof a c η hc θ (e,u) y).trans
      (LinearMap.sum_apply Finset.univ (fun s : SlopeSplit c η hc θ e.val=>
        globalSplitCoproduct a c η hc θ (e,u) s) y).symm
  have H := tensorGradeLift_comp
    (unitalSourceFiltration a c η hc θ d.val) (unitalSourceFiltration a c η hc θ e.val)
    (unitalSourceFiltration_antitone a c η hc θ d.val)
    (unitalSourceFiltration_antitone a c η hc θ e.val)
    (fun u=>globalGradeLof a c η hc θ d u)
    (fun v=>globalGradeLof a c η hc θ e v)
    LinearMap.id (globalCoproduct a c η hc θ) W x
  simp only [LinearMap.id_comp,hh] at H
  exact H.trans (tensorGradeLift_sum_right _ _ _ _
    (fun v=>globalGradeLof a c η hc θ d v)
    (fun s u=>globalSplitGradeCoproduct a c η hc θ e s u) W x)

noncomputable def globalIteratedLeftSplit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (t : SlopeSplit c η hc θ (left s.val)) :
    unitalComponent a c η hc θ k →ₗ[ℚ]
      (UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ)⊗[ℚ]UnitalShuffle a c η hc θ :=
  (tensorGradeLift (unitalSourceFiltration a c η hc θ (left s.val))
    (unitalSourceFiltration a c η hc θ (right s.val))
    (unitalSourceFiltration_antitone a c η hc θ (left s.val))
    (unitalSourceFiltration_antitone a c η hc θ (right s.val))
    (fun u=>globalSplitCoproduct a c η hc θ (⟨left s.val,s.property.1⟩,u) t)
    (fun v=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (⟨right s.val,s.property.2⟩,v)) k.2).comp
      ((unitalGradeCoproduct a c η hc θ (left s.val) (right s.val)
        (s.property.1.compatible s.property.2) k.2).comp
        (unitalGradeCast a c η hc θ (left_add_right s.val).symm rfl).toLinearMap)

noncomputable def globalIteratedRightSplit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (t : SlopeSplit c η hc θ (right s.val)) :
    unitalComponent a c η hc θ k →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ](UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :=
  (tensorGradeLift (unitalSourceFiltration a c η hc θ (left s.val))
    (unitalSourceFiltration a c η hc θ (right s.val))
    (unitalSourceFiltration_antitone a c η hc θ (left s.val))
    (unitalSourceFiltration_antitone a c η hc θ (right s.val))
    (fun v=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (⟨left s.val,s.property.1⟩,v))
    (fun u=>globalSplitCoproduct a c η hc θ (⟨right s.val,s.property.2⟩,u) t) k.2).comp
      ((unitalGradeCoproduct a c η hc θ (left s.val) (right s.val)
        (s.property.1.compatible s.property.2) k.2).comp
        (unitalGradeCast a c η hc θ (left_add_right s.val).symm rfl).toLinearMap)

lemma globalCoproduct_iterated_left_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.map (globalCoproduct a c η hc θ) LinearMap.id
      (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))=
      ∑ s : SlopeSplit c η hc θ k.1.val,∑ t : SlopeSplit c η hc θ (left s.val),
        globalIteratedLeftSplit a c η hc θ k s t x := by
  rw [globalCoproduct_lof,map_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact globalCoproduct_tensor_left a c η hc θ ⟨left s.val,s.property.1⟩
    ⟨right s.val,s.property.2⟩ k.2
    (unitalGradeCoproduct a c η hc θ (left s.val) (right s.val)
      (s.property.1.compatible s.property.2) k.2
        (unitalGradeCast a c η hc θ (left_add_right s.val).symm rfl x))

lemma globalCoproduct_iterated_right_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.map LinearMap.id (globalCoproduct a c η hc θ)
      (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))=
      ∑ s : SlopeSplit c η hc θ k.1.val,∑ t : SlopeSplit c η hc θ (right s.val),
        globalIteratedRightSplit a c η hc θ k s t x := by
  rw [globalCoproduct_lof,map_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact globalCoproduct_tensor_right a c η hc θ ⟨left s.val,s.property.1⟩
    ⟨right s.val,s.property.2⟩ k.2
    (unitalGradeCoproduct a c η hc θ (left s.val) (right s.val)
      (s.property.1.compatible s.property.2) k.2
        (unitalGradeCast a c η hc θ (left_add_right s.val).symm rfl x))
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FilteredTensorInsert
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

noncomputable def tensorFiltrationAssoc (F : ℤ → Submodule K A) (G : ℤ → Submodule K B)
    (H : ℤ → Submodule K C) (W : ℤ) :
    additiveTensorFiltration (additiveTensorFiltration F G) H W ≃ₗ[K]
      additiveTensorFiltration F (additiveTensorFiltration G H) W :=
  { toFun := fun x=>⟨TensorProduct.assoc K A B C x.val,assoc_mem_tensorFiltration F G H W x.val x.property⟩
    invFun := fun x=>⟨(TensorProduct.assoc K A B C).symm x.val,unassoc_mem_tensorFiltration F G H W x.val x.property⟩
    left_inv := by intro x; apply Subtype.ext; exact (TensorProduct.assoc K A B C).symm_apply_apply x.val
    right_inv := by intro x; apply Subtype.ext; exact (TensorProduct.assoc K A B C).apply_symm_apply x.val
    map_add' := by intro x y; apply Subtype.ext; exact (TensorProduct.assoc K A B C).map_add x.val y.val
    map_smul' := by intro r x; apply Subtype.ext; exact (TensorProduct.assoc K A B C).map_smul r x.val }

noncomputable def unassocTensorFixedLeft (F : ℤ → Submodule K A) (G : ℤ → Submodule K B)
    (H : ℤ → Submodule K C) (U V : ℤ) (x : F U) :
    additiveTensorFiltration G H V →ₗ[K] additiveTensorFiltration (additiveTensorFiltration F G) H (U+V) :=
  (((TensorProduct.assoc K A B C).symm.toLinearMap.comp (TensorProduct.mk K A (B⊗[K]C) x.val)).comp
    (additiveTensorFiltration G H V).subtype).codRestrict _ (fun y=>
      unassoc_mem_tensorFiltration F G H (U+V) (x.val⊗ₜ[K]y.val)
        (tmul_mem_additiveTensorFiltration F (additiveTensorFiltration G H) (le_refl _) x.property y.property))

end ElementaryPositivity.LinearDetection

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TensorPolynomialLinear
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
open scoped TensorProduct
variable {A B α β : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]

noncomputable def boxRightLinear (p : MvPolynomial α A) :
    MvPolynomial β B →ₗ[ℚ] MvPolynomial (α⊕β) (A⊗[ℚ]B) :=
  { toFun := box p
    map_add' := by intro q r; simp only [box,map_add,mul_add]
    map_smul' := by
      intro r q
      ext z
      rw [←Finsupp.comapDomain_sumElim_comapDomain z,coeff_box,coeff_smul,coeff_smul,coeff_box]
      exact (TensorProduct.mk ℚ A B _).map_smul r _ }

end ElementaryPositivity.CenterCalculus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TripleAssociativity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.LinearDetection ElementaryPositivity.LinearFiltration
open SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma tensorSeparationRight_filtration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : I → ℕ)
    (hs : SlopeArithmetic.slope c η e=SlopeArithmetic.slope c η f)
    (W : ℤ) (x : B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) (e+f))
    (hx : x∈sourceTensorFiltration a c η hc θ d (e+f) W) :
    TensorProduct.map LinearMap.id (separationCoefficient a c η hc hs 0) x∈
      additiveTensorFiltration (sourceFiltration a c η hc θ d)
        (sourceTensorFiltration a c η hc θ e f) W :=
  tensor_map_mem_filtration (sourceFiltration a c η hc θ d) (sourceFiltration a c η hc θ (e+f))
    (sourceFiltration a c η hc θ d) (sourceTensorFiltration a c η hc θ e f)
    LinearMap.id (separationCoefficient a c η hc hs 0)
    (fun _ _ h=>h) (fun w=>separationCoefficient_filtration a c η hc θ e f hs w 0) W x hx

noncomputable def tensorSeparationRight (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : I → ℕ)
    (hs : SlopeArithmetic.slope c η e=SlopeArithmetic.slope c η f) (W : ℤ) :
    sourceTensorFiltration a c η hc θ d (e+f) W →ₗ[ℚ]
      additiveTensorFiltration (sourceFiltration a c η hc θ d)
        (sourceTensorFiltration a c η hc θ e f) W :=
  let C : B a (SlopeArithmetic.slope c η) (e+f) →ₗ[ℚ]
      B a (SlopeArithmetic.slope c η) e⊗[ℚ]B a (SlopeArithmetic.slope c η) f :=
    separationCoefficient a c η hc hs 0
  let F : (B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) (e+f)) →ₗ[ℚ]
      (B a (SlopeArithmetic.slope c η) d⊗[ℚ](B a (SlopeArithmetic.slope c η) e⊗[ℚ]
        B a (SlopeArithmetic.slope c η) f)) := TensorProduct.map LinearMap.id C
  (F.comp (sourceTensorFiltration a c η hc θ d (e+f) W).subtype).codRestrict
    (additiveTensorFiltration (sourceFiltration a c η hc θ d)
      (sourceTensorFiltration a c η hc θ e f) W)
    (fun x=>tensorSeparationRight_filtration a c η hc θ d e f hs W x.val x.property)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PolynomialExtendInjective
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.pairAdd
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.tripleAdd
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.tripleFilterAdd
noncomputable def iteratedCoproductLeft (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : I → ℕ)
    (hde : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (hef : SlopeArithmetic.slope c η e=SlopeArithmetic.slope c η f) (W : ℤ) :
    sourceFiltration a c η hc θ ((d+e)+f) W →ₗ[ℚ] sourceTripleFiltration a c η hc θ d e f W :=
  (tensorSeparationLeft a c η hc θ d e f hde W).comp
    (separationCoefficientRestricted a c η hc θ (d+e) f
      ((SlopeArithmetic.slope_add_same c η hc hde).trans (hde.trans hef)) W 0)

noncomputable def iteratedCoproductRight (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : I → ℕ)
    (hde : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (hef : SlopeArithmetic.slope c η e=SlopeArithmetic.slope c η f) (W : ℤ) :
    sourceFiltration a c η hc θ ((d+e)+f) W →ₗ[ℚ]
      additiveTensorFiltration (sourceFiltration a c η hc θ d)
        (sourceTensorFiltration a c η hc θ e f) W :=
  ((tensorSeparationRight a c η hc θ d e f hef W).comp
    (separationCoefficientRestricted a c η hc θ d (e+f)
      (hde.trans (SlopeArithmetic.slope_add_same c η hc hef).symm) W 0)).comp
    (filtrationDimensionEquiv a c η hc θ (add_assoc d e f) W).toLinearMap

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_UnitalCoproductNaturality
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
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] unitalSepTensor unitalSepTensorA
noncomputable local instance naturalTensorAdd (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    AddCommGroup (B a μ d⊗[ℚ]B a μ e) := TensorProduct.addCommGroup
noncomputable local instance naturalTensorModule (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Module ℚ (B a μ d⊗[ℚ]B a μ e) := TensorProduct.leftModule

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalCoproductCoassociative
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
  ElementaryPositivity.LinearFiltration SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] naturalTensorAdd naturalTensorModule pairAdd tripleAdd tripleFilterAdd

noncomputable local instance unitalTripleRightAdd (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e f : I → ℕ) : AddCommGroup (B a μ d⊗[ℚ](B a μ e⊗[ℚ]B a μ f)) :=
  TensorProduct.addCommGroup
noncomputable local instance unitalTripleRightModule (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e f : I → ℕ) : Module ℚ (B a μ d⊗[ℚ](B a μ e⊗[ℚ]B a μ f)) :=
  TensorProduct.leftModule

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
  ElementaryPositivity.LinearFiltration SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] naturalTensorAdd naturalTensorModule pairAdd tripleAdd tripleFilterAdd
  unitalTripleRightAdd unitalTripleRightModule

lemma unitalSeparationConstant_filtered (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : I → ℕ)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (W : ℤ) (x : B a (slope c η) (d+e))
    (hx : x∈unitalSourceFiltration a c η hc θ (d+e) W) :
    unitalSeparationConstant a c η hc d e hs x∈unitalSourceTensorFiltration a c η hc θ d e W :=
  unitalSeparationSeries_coeff_filtration a c η hc θ d e hs W 0 x hx

noncomputable def unitalTensorCoproductLeft (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : I → ℕ)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (W : ℤ) :
    UnitalSourceTensorGrade a c η hc θ (d+e) f W →ₗ[ℚ]
      TensorGrade (unitalSourceTensorFiltration a c η hc θ d e)
        (unitalSourceFiltration a c η hc θ f) W :=
  tensorGradeMap (unitalSourceFiltration a c η hc θ (d+e))
    (unitalSourceFiltration a c η hc θ f) (unitalSourceTensorFiltration a c η hc θ d e)
    (unitalSourceFiltration a c η hc θ f)
    (unitalSeparationConstant a c η hc d e hs) LinearMap.id
    (unitalSeparationConstant_filtered a c η hc θ d e hs) (fun _ _ h=>h) W

noncomputable def unitalTensorCoproductRight (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : I → ℕ)
    (hs : e=0 ∨ f=0 ∨ slope c η e=slope c η f) (W : ℤ) :
    UnitalSourceTensorGrade a c η hc θ d (e+f) W →ₗ[ℚ]
      TensorGrade (unitalSourceFiltration a c η hc θ d)
        (unitalSourceTensorFiltration a c η hc θ e f) W :=
  tensorGradeMap (unitalSourceFiltration a c η hc θ d)
    (unitalSourceFiltration a c η hc θ (e+f)) (unitalSourceFiltration a c η hc θ d)
    (unitalSourceTensorFiltration a c η hc θ e f) LinearMap.id
    (unitalSeparationConstant a c η hc e f hs)
    (fun _ _ h=>h) (unitalSeparationConstant_filtered a c η hc θ e f hs) W

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalTripleGradeInclusion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
  ElementaryPositivity.LinearDetection DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
noncomputable def globalTripleGradeLeft (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : slopeDimensions c η hc θ) (W : ℤ) :
    TensorGrade (unitalSourceTensorFiltration a c η hc θ d.val e.val)
      (unitalSourceFiltration a c η hc θ f.val) W →ₗ[ℚ]
      (UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ)⊗[ℚ]UnitalShuffle a c η hc θ :=
  tensorGradeLift (unitalSourceTensorFiltration a c η hc θ d.val e.val)
    (unitalSourceFiltration a c η hc θ f.val) (unitalSourceTensorFiltration_antitone a c η hc θ d.val e.val)
    (unitalSourceFiltration_antitone a c η hc θ f.val)
    (globalTensorGradeInclusion a c η hc θ d e)
    (fun w=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (f,w)) W

noncomputable def globalTripleGradeRight (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : slopeDimensions c η hc θ) (W : ℤ) :
    TensorGrade (unitalSourceFiltration a c η hc θ d.val)
      (unitalSourceTensorFiltration a c η hc θ e.val f.val) W →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ](UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :=
  tensorGradeLift (unitalSourceFiltration a c η hc θ d.val)
    (unitalSourceTensorFiltration a c η hc θ e.val f.val)
    (unitalSourceFiltration_antitone a c η hc θ d.val)
    (unitalSourceTensorFiltration_antitone a c η hc θ e.val f.val)
    (fun w=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,w))
    (globalTensorGradeInclusion a c η hc θ e f) W

lemma globalTripleGrade_assoc (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : slopeDimensions c η hc θ) (W : ℤ)
    (x : TensorGrade (unitalSourceTensorFiltration a c η hc θ d.val e.val)
      (unitalSourceFiltration a c η hc θ f.val) W) :
    globalTripleGradeRight a c η hc θ d e f W
      (tensorGradeAssoc (unitalSourceFiltration a c η hc θ d.val)
        (unitalSourceFiltration a c η hc θ e.val) (unitalSourceFiltration a c η hc θ f.val) W x)=
      TensorProduct.assoc ℚ _ _ _ (globalTripleGradeLeft a c η hc θ d e f W x) :=
  tensorGradeLift_assoc _ _ _ (unitalSourceFiltration_antitone a c η hc θ d.val)
    (unitalSourceFiltration_antitone a c η hc θ e.val)
    (unitalSourceFiltration_antitone a c η hc θ f.val)
    (fun u=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,u))
    (fun u=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (e,u))
    (fun u=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (f,u)) W x

lemma globalTripleGrade_left_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ (d.val+e.val) f.val W) :
    globalTripleGradeLeft a c η hc θ d e f W
      (unitalTensorCoproductLeft a c η hc θ d.val e.val f.val (d.property.compatible e.property) W x)=
      tensorGradeLift (unitalSourceFiltration a c η hc θ (d.val+e.val))
        (unitalSourceFiltration a c η hc θ f.val)
        (unitalSourceFiltration_antitone a c η hc θ (d.val+e.val))
        (unitalSourceFiltration_antitone a c η hc θ f.val)
        (fun u=>(globalTensorGradeInclusion a c η hc θ d e u).comp
          (unitalGradeCoproduct a c η hc θ d.val e.val (d.property.compatible e.property) u))
        (fun u=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (f,u)) W x := by
  have H := tensorGradeLift_map_natural
    (unitalSourceFiltration a c η hc θ (d.val+e.val))
    (unitalSourceFiltration a c η hc θ f.val)
    (unitalSourceTensorFiltration a c η hc θ d.val e.val)
    (unitalSourceFiltration a c η hc θ f.val)
    (unitalSourceFiltration_antitone a c η hc θ (d.val+e.val))
    (unitalSourceFiltration_antitone a c η hc θ f.val)
    (unitalSourceTensorFiltration_antitone a c η hc θ d.val e.val)
    (unitalSourceFiltration_antitone a c η hc θ f.val)
    (unitalSeparationConstant a c η hc d.val e.val (d.property.compatible e.property))
    LinearMap.id
    (unitalSeparationConstant_filtered a c η hc θ d.val e.val (d.property.compatible e.property))
    (fun _ _ h=>h)
    (globalTensorGradeInclusion a c η hc θ d e)
    (fun u=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (f,u)) W x
  simp only [gradeMap_id] at H
  exact H

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

abbrev LeftSlopeTriple (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ) :=
  Σ s : SlopeSplit c η hc θ d,SlopeSplit c η hc θ (left s.val)
abbrev SlopeTriple (c η : I → ℝ) (_hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ) :=
  {p : (I → ℕ) × (I → ℕ) × (I → ℕ) //
    (p.1+p.2.1)+p.2.2=d ∧ OnSlopeOrZero c η θ p.1 ∧
      OnSlopeOrZero c η θ p.2.1 ∧ OnSlopeOrZero c η θ p.2.2}

def leftTripleBuild (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ)
    (p : SlopeTriple c η hc θ d) : LeftSlopeTriple c η hc θ d :=
  ⟨⟨ofPair (p.val.1+p.val.2.1) p.val.2.2 p.property.1,
      by simpa only [left_ofPair,right_ofPair] using
        And.intro (p.property.2.1.add hc p.property.2.2.1) p.property.2.2.2⟩,
    ⟨ofPair p.val.1 p.val.2.1 rfl,
      by simpa only [left_ofPair,right_ofPair] using
        And.intro p.property.2.1 p.property.2.2.1⟩⟩

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalCoproductCoassociative
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def globalTripleCoproduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (p : SlopeTriple c η hc θ k.1.val) :
    unitalComponent a c η hc θ k →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ](UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :=
  (globalTripleGradeRight a c η hc θ ⟨p.val.1,p.property.2.1⟩
    ⟨p.val.2.1,p.property.2.2.1⟩ ⟨p.val.2.2,p.property.2.2.2⟩ k.2).comp
    ((unitalTensorCoproductRight a c η hc θ p.val.1 p.val.2.1 p.val.2.2
      (p.property.2.2.1.compatible p.property.2.2.2) k.2).comp
      ((unitalGradeCoproduct a c η hc θ p.val.1 (p.val.2.1+p.val.2.2)
        (p.property.2.1.compatible (p.property.2.2.1.add hc p.property.2.2.2)) k.2).comp
        (unitalGradeCast a c η hc θ
          ((add_assoc _ _ _).symm.trans p.property.1).symm rfl).toLinearMap))

noncomputable def globalLeftTripleOutput (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (d e f : slopeDimensions c η hc θ) (hp : d.val+e.val+f.val=k.1.val)
    (x : unitalComponent a c η hc θ k) :=
    TensorProduct.assoc ℚ _ _ _ (globalTripleGradeLeft a c η hc θ d e f k.2
      (unitalTensorCoproductLeft a c η hc θ d.val e.val f.val (d.property.compatible e.property) k.2
        (unitalGradeCoproduct a c η hc θ (d.val+e.val) f.val
          ((d.property.add hc e.property).compatible f.property) k.2
          (unitalGradeCast a c η hc θ hp.symm rfl x))))

noncomputable def globalLeftTripleCoproduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (p : SlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :=
    globalLeftTripleOutput a c η hc θ k ⟨p.val.1,p.property.2.1⟩
      ⟨p.val.2.1,p.property.2.2.1⟩ ⟨p.val.2.2,p.property.2.2.2⟩ p.property.1 x

lemma globalTensorGrade_coproduct_family_cast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) :
    (fun u=>(globalTensorGradeInclusion a c η hc θ d e u).comp
      ((unitalGradeCoproduct a c η hc θ d.val e.val (d.property.compatible e.property) u).comp
        (unitalGradeCast a c η hc θ (rfl : d.val+e.val=d.val+e.val) (rfl : u=u)).toLinearMap) :
      (u : ℤ) → FGrade (unitalSourceFiltration a c η hc θ (d.val+e.val)) u →ₗ[ℚ]
        UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ)=
    (fun u=>(globalTensorGradeInclusion a c η hc θ d e u).comp
      (unitalGradeCoproduct a c η hc θ d.val e.val (d.property.compatible e.property) u)) := rfl

lemma globalTripleGrade_left_cast_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ (d.val+e.val) f.val W) :
    TensorProduct.assoc ℚ _ _ _
      (tensorGradeLift (unitalSourceFiltration a c η hc θ (d.val+e.val))
        (unitalSourceFiltration a c η hc θ f.val)
        (unitalSourceFiltration_antitone a c η hc θ (d.val+e.val))
        (unitalSourceFiltration_antitone a c η hc θ f.val)
        (fun u=>(globalTensorGradeInclusion a c η hc θ d e u).comp
          ((unitalGradeCoproduct a c η hc θ d.val e.val (d.property.compatible e.property) u).comp
            (unitalGradeCast a c η hc θ rfl rfl).toLinearMap))
        (fun v=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (f,v)) W x)=
    TensorProduct.assoc ℚ _ _ _ (globalTripleGradeLeft a c η hc θ d e f W
      (unitalTensorCoproductLeft a c η hc θ d.val e.val f.val (d.property.compatible e.property) W x)) := by
  rw [globalTensorGrade_coproduct_family_cast]
  exact congrArg (TensorProduct.assoc ℚ _ _ _) (globalTripleGrade_left_natural a c η hc θ d e f W x).symm

lemma globalIteratedLeftSplit_dimensions (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (t : SlopeSplit c η hc θ (left s.val))
    (b d e f : I → ℕ) (hb : left s.val=b) (hd : left t.val=d)
    (he : right t.val=e) (hf : right s.val=f)
    (hbs : OnSlopeOrZero c η θ b) (hds : OnSlopeOrZero c η θ d)
    (hes : OnSlopeOrZero c η θ e) (hfs : OnSlopeOrZero c η θ f)
    (hde : d+e=b) (hbf : b+f=k.1.val) (x : unitalComponent a c η hc θ k) :
    globalIteratedLeftSplit a c η hc θ k s t x =
      tensorGradeLift (unitalSourceFiltration a c η hc θ b)
        (unitalSourceFiltration a c η hc θ f)
        (unitalSourceFiltration_antitone a c η hc θ b)
        (unitalSourceFiltration_antitone a c η hc θ f)
        (fun u=>(globalTensorGradeInclusion a c η hc θ ⟨d,hds⟩ ⟨e,hes⟩ u).comp
          ((unitalGradeCoproduct a c η hc θ d e (hds.compatible hes) u).comp
            (unitalGradeCast a c η hc θ hde.symm rfl).toLinearMap))
        (fun v=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (⟨f,hfs⟩,v)) k.2
        (unitalGradeCoproduct a c η hc θ b f (hbs.compatible hfs) k.2
          (unitalGradeCast a c η hc θ hbf.symm rfl x)) := by
  subst b; subst d; subst e; subst f
  rfl

lemma globalIteratedLeftSplit_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (t : SlopeSplit c η hc θ (left s.val))
    (d e f : slopeDimensions c η hc θ)
    (hb : left s.val=d.val+e.val) (hd : left t.val=d.val)
    (he : right t.val=e.val) (hf : right s.val=f.val)
    (hp : d.val+e.val+f.val=k.1.val) (x : unitalComponent a c η hc θ k) :
    TensorProduct.assoc ℚ _ _ _ (globalIteratedLeftSplit a c η hc θ k s t x)=
    globalLeftTripleOutput a c η hc θ k d e f hp x := by
  unfold globalLeftTripleOutput
  rw [globalIteratedLeftSplit_dimensions a c η hc θ k s t (d.val+e.val) d.val e.val f.val
    hb hd he hf (d.property.add hc e.property) d.property e.property f.property rfl hp x]
  exact globalTripleGrade_left_cast_natural a c η hc θ d e f k.2 _

lemma globalIteratedLeftSplit_build_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ)
    (k : SlopeWeight c η hc θ) (p : SlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.assoc ℚ _ _ _
      (globalIteratedLeftSplit a c η hc θ k (leftTripleBuild c η hc θ k.1.val p).1
        (leftTripleBuild c η hc θ k.1.val p).2 x)=
      globalLeftTripleCoproduct a c η hc θ k p x := by
  exact globalIteratedLeftSplit_natural a c η hc θ k
    (leftTripleBuild c η hc θ k.1.val p).1 (leftTripleBuild c η hc θ k.1.val p).2
    ⟨p.val.1,p.property.2.1⟩ ⟨p.val.2.1,p.property.2.2.1⟩ ⟨p.val.2.2,p.property.2.2.2⟩ rfl rfl
    (right_ofPair p.val.1 p.val.2.1 rfl) (right_ofPair (p.val.1+p.val.2.1) p.val.2.2 p.property.1)
    p.property.1 x

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalShuffleCoalgebra
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic DimensionSplit WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

def dimensionSize (d : I → ℕ) : ℕ := ∑ i,d i

variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {A : Type*} [Ring A] [Algebra ℚ A]

def convVanishes (n : ℕ) (f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)) : Prop :=
  ∀ k : SlopeWeight c η hc θ, dimensionSize k.1.val < n →
    ∀ x : unitalComponent a c η hc θ k,
      f.ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)=0

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalWordDetection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*} [LinearOrder J]

noncomputable def wordMultiplicity : List J → ℕ
  | [] => 1
  | i::l => (l.count i+1)*wordMultiplicity l

end ElementaryPositivity.RawShuffle

end

end OAI
end


