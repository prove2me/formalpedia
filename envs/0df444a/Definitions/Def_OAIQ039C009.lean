-- Prove2me | Definitions.Def_OAIQ039C009
-- name    : OAIQ039C009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:12:26.682749+00:00
-- url     : https://prove2.me/theorems/c50ea564-eef4-4903-aca9-b2fbf2e82f5f
-- title:
--   Definitions bundle OAIQ039C009 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 12 definitions, 1 inductive type or structure and 20 theorems. The definitions and types are `OAI.Kadison.FaithfulNormalFunctional.functional`, `OAI.Kadison.FaithfulNormalFunctional.term`, `OAI.Kadison.FaithfulNormalFunctional.weight`, `OAI.Kadison.FaithfulNormalFunctional.weighted`, `OAI.Kadison.FejerTest.HaarMoments`, `OAI.Kadison.FinitePatching.PartialUnitary`, `OAI.Kadison.FinitePatching.PartialUnitary.power`, `OAI.Kadison.FiniteTest.flip`, `OAI.Kadison.MatrixUnits.ofPartialIsometries`, `OAI.Kadison.MatrixUnits.representation`, `OAI.Kadison.VectorGNS.embedding`, `OAI.Kadison.VectorGNS.preIsometry`, `OAI.Kadison.VectorGNS.preMap`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_FaithfulNormalFunctional`, `Commutator_FaithfulVectorGNS`, `Commutator_FejerTest`, `Commutator_FiniteHankel`, `Commutator_FiniteTestPatching`, `Commutator_GNSVectorEmbedding`, `Commutator_MatrixUnits`, `Commutator_PartialUnitaryAlgebra`, `Commutator_PolarDecomposition`, `Commutator_PolarExtension`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C024`, `OAIQ039C025` and `OAIQ039C029`; the proofs of `OAI_Kadison_NormalRepresentation_traced_factor_bound`, `OAI_Kadison_OrbitStateHull_exists_faithful_normal_trace` and `OAI_Kadison_TracialGNS_actual_block_classification`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_FaithfulNormalFunctional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.FaithfulNormalFunctional

variable {H : Type*} [NormedAddCommGroup H]

variable (x : ℕ → H)

def weight (n : ℕ) : ℝ := (1/2:ℝ)^n/(1+‖x n‖^2)

lemma weight_pos (n : ℕ) : 0<weight x n := by
  apply div_pos
  · positivity
  · positivity

lemma weight_norm_bound (n : ℕ) : weight x n*‖x n‖^2≤(1/2:ℝ)^n := by
  have hd : 0<1+‖x n‖^2 := by positivity
  rw [weight,div_mul_eq_mul_div,div_le_iff₀ hd]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) n]

variable [InnerProductSpace ℂ H] [CompleteSpace H]

def term (n : ℕ) (T : H →L[ℂ] H) : ℂ :=
  (weight x n:ℂ)*inner ℂ (x n) (T (x n))

lemma term_bound (n : ℕ) (T : H →L[ℂ] H) : ‖term x n T‖≤(1/2:ℝ)^n*‖T‖ := by
  rw [term,norm_mul,Complex.norm_real,Real.norm_of_nonneg (weight_pos x n).le]
  calc
    _≤weight x n*(‖x n‖*(‖T‖*‖x n‖)) := mul_le_mul_of_nonneg_left
      ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)))
      (weight_pos x n).le
    _=(weight x n*‖x n‖^2)*‖T‖ := by ring
    _≤_ := mul_le_mul_of_nonneg_right (weight_norm_bound x n) (norm_nonneg T)

lemma term_summable (T : H →L[ℂ] H) : Summable (fun n => term x n T) :=
  ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)).mul_right ‖T‖).of_norm_bounded
    (fun n => term_bound x n T)

lemma term_add (n : ℕ) (S T : H →L[ℂ] H) : term x n (S+T)=term x n S+term x n T := by
  simp [term,mul_add]

lemma term_smul (n : ℕ) (z : ℂ) (T : H →L[ℂ] H) : term x n (z•T)=z*term x n T := by
  simp only [term,smul_apply,inner_smul_right]
  ring

lemma term_nonneg (n : ℕ) {T : H →L[ℂ] H} (hT : 0≤T) : 0≤term x n T := by
  apply mul_nonneg (Complex.zero_le_real.mpr (weight_pos x n).le)
  exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hT).inner_nonneg_right _

def functional : (H →L[ℂ] H) →ₚ[ℂ] ℂ where
  toFun T := ∑' n,term x n T
  map_add' S T := by simp_rw [term_add]; exact (term_summable x S).tsum_add (term_summable x T)
  map_smul' z T := by simp_rw [term_smul,tsum_mul_left]; rfl
  monotone' := by
    intro S T hST
    have hnon : 0≤∑' n,term x n (T-S) := tsum_nonneg (fun n => term_nonneg x n (sub_nonneg.mpr hST))
    have hsub : (∑' n,term x n (T-S))=(∑' n,term x n T)-(∑' n,term x n S) := by
      rw [←(term_summable x T).tsum_sub (term_summable x S)]
      congr 1
      ext n
      simp [term,mul_sub]
    rw [hsub] at hnon
    exact sub_nonneg.mp hnon


end Kadison.FaithfulNormalFunctional

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FejerTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.FejerTest

variable {A : Type*} [CStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

variable (φ : A →ₚ[ℂ] ℂ) (w : A)

def HaarMoments : Prop :=
  ∀ i j : ℕ, φ (star (w^i) * w^j) = if i=j then 1 else 0

end Kadison.FejerTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteHankel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.FiniteCompression

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [CompleteSpace H] [DecidableEq I] in
lemma inner_sum_diagonal (x y : I → H)
    (h : ∀ i j, i ≠ j → inner ℂ (x i) (y j) = 0) :
    inner ℂ (∑ i, x i) (∑ i, y i) = ∑ i, inner ℂ (x i) (y i) := by
  simp only [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_eq_single i (fun j _ hji => h j i hji) (by simp)

end Kadison.FiniteCompression

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GNSVectorEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open UniformSpace ContinuousLinearMap

namespace Kadison.VectorGNS

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (τ : A →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hτ : ∀ a,τ a=inner ℂ ξ (φ a ξ))

def preMap : τ.PreGNS →ₗ[ℂ] H where
  toFun x := φ (τ.ofPreGNS x) ξ
  map_add' x y := by simp only [map_add,add_apply]
  map_smul' c x := by simp only [map_smul,smul_apply,RingHom.id_apply]

include hτ in
lemma inner_preMap (x y : τ.PreGNS) :
    inner ℂ (preMap τ φ ξ x) (preMap τ φ ξ y)=inner ℂ x y := by
  rw [PositiveLinearMap.preGNS_inner_def,hτ,map_mul,map_star]
  change inner ℂ (φ (τ.ofPreGNS x) ξ) (φ (τ.ofPreGNS y) ξ)=
    inner ℂ ξ ((φ (τ.ofPreGNS x)).adjoint (φ (τ.ofPreGNS y) ξ))
  exact (adjoint_inner_right _ _ _).symm

def preIsometry : τ.PreGNS →ₗᵢ[ℂ] H :=
  (preMap τ φ ξ).isometryOfInner (inner_preMap τ φ ξ hτ)

def embedding : τ.GNS →ₗᵢ[ℂ] H where
  toLinearMap := ((preIsometry τ φ ξ hτ).toContinuousLinearMap.extend
    (Completion.toComplL : τ.PreGNS →L[ℂ] τ.GNS)).toLinearMap
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x =>
      change ‖((preIsometry τ φ ξ hτ).toContinuousLinearMap.extend
        (Completion.toComplL : τ.PreGNS →L[ℂ] τ.GNS))
        ((Completion.toComplL : τ.PreGNS →L[ℂ] τ.GNS) x)‖=‖(x:τ.GNS)‖
      rw [extend_eq _ Completion.denseRange_coe (Completion.isUniformInducing_coe _),
        LinearIsometry.coe_toContinuousLinearMap,LinearIsometry.norm_map,Completion.norm_coe]

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FaithfulVectorGNS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology ENNReal

namespace Kadison.FaithfulNormalFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (x : ℕ → H)

def weighted (n : ℕ) : H := (Real.sqrt (weight x n) : ℂ) • x n

omit [CompleteSpace H] in
lemma weighted_norm_sq (n : ℕ) : ‖weighted x n‖^2=weight x n*‖x n‖^2 := by
  rw [weighted,norm_smul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (weight_pos x n).le]

omit [CompleteSpace H] in
lemma weighted_mem : Memℓp (weighted x) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr
  have hs : Summable (fun n => ‖weighted x n‖^2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => by
      rw [weighted_norm_sq]; exact weight_norm_bound x n)
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1))
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hs

end Kadison.FaithfulNormalFunctional

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestPatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.FiniteTest

section Signs

variable {I : Type*} [DecidableEq I]

def flip (i : I) (σ : I → Bool) : I → Bool := Function.update σ i (!(σ i))

end Signs

end Kadison.FiniteTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.MatrixUnits

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [StarRing A]
  [Algebra ℂ A] [StarModule ℂ A]

def representation (e : ι → ι → A)
    (hmul : ∀ i j k l, e i j * e k l = if j=k then e i l else 0)
    (hstar : ∀ i j, star (e i j)=e j i)
    (hone : ∑ i,e i i=1) : Matrix ι ι ℂ →⋆ₐ[ℂ] A where
  toFun x := ∑ i,∑ j,x i j • e i j
  map_zero' := by simp
  map_one' := by simpa [Matrix.one_apply] using hone
  map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
  map_mul' x y := by
    simp only [Matrix.mul_apply,Finset.sum_smul,Finset.sum_mul,Finset.mul_sum,
      smul_mul_smul_comm,hmul,smul_ite,smul_zero]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    conv_rhs =>
      rw [Finset.sum_comm]
      arg 2
      ext j
      rw [Finset.sum_comm]
    exact Finset.sum_comm
  commutes' c := by
    change (∑ i,∑ j,(algebraMap ℂ (Matrix ι ι ℂ) c) i j • e i j)=_
    simp [Matrix.algebraMap_matrix_apply,←Finset.smul_sum,hone,Algebra.algebraMap_eq_smul_one]
  map_star' x := by
    simp only [Matrix.star_apply,star_sum,star_smul,hstar]
    exact Finset.sum_comm

@[simp] lemma representation_apply (e : ι → ι → A) (hmul) (hstar) (hone)
    (x : Matrix ι ι ℂ) : representation e hmul hstar hone x=∑ i,∑ j,x i j • e i j := rfl

omit [Fintype ι] [Algebra ℂ A] [StarModule ℂ A] in
lemma partialIsometry_cross (q : A) (p v : ι → A)
    (hsource : ∀ i, star (v i)*v i=q)
    (htarget : ∀ i, p i*v i=v i)
    (hself : ∀ i, star (p i)=p i)
    (horth : ∀ i j, i≠j → p i*p j=0) (i j : ι) :
    star (v i)*v j=if i=j then q else 0 := by
  split_ifs with h
  · subst j
    exact hsource i
  · have hleft : star (v i)*p i=star (v i) := by
      simpa only [star_mul,hself] using congrArg star (htarget i)
    calc
      _=(star (v i)*p i)*(p j*v j) := by rw [hleft,htarget]
      _=star (v i)*(p i*p j)*v j := by noncomm_ring
      _=0 := by rw [horth i j h,mul_zero,zero_mul]

def ofPartialIsometries (q : A) (p v : ι → A)
    (hsource : ∀ i, star (v i)*v i=q)
    (hfinal : ∀ i, v i*star (v i)=p i)
    (hfix : ∀ i, v i*q=v i)
    (htarget : ∀ i, p i*v i=v i)
    (hself : ∀ i, star (p i)=p i)
    (horth : ∀ i j, i≠j → p i*p j=0)
    (hone : ∑ i,p i=1) : Matrix ι ι ℂ →⋆ₐ[ℂ] A :=
  representation (fun i j => v i*star (v j)) (by
    intro i j k l
    calc
      _=v i*(star (v j)*v k)*star (v l) := by noncomm_ring
      _=if j=k then v i*star (v l) else 0 := by
        rw [partialIsometry_cross q p v hsource htarget hself horth]
        split_ifs
        · rw [hfix]
        · rw [mul_zero,zero_mul])
    (by intro i j; simp only [star_mul,star_star])
    (by simpa only [hfinal] using hone)

@[simp] lemma ofPartialIsometries_single (q : A) (p v : ι → A)
    (hsource) (hfinal) (hfix) (htarget) (hself) (horth) (hone)
    (i j : ι) :
    ofPartialIsometries q p v hsource hfinal hfix htarget hself horth hone
      (Matrix.single i j (1:ℂ))=v i*star (v j) := by
  classical
  simp [ofPartialIsometries,representation,Matrix.single_apply,ite_and]

end Kadison.MatrixUnits

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

variable (A : Type*) [CStarAlgebra A]

structure PartialUnitary where
  val : A
  support : A
  projection : IsStarProjection support
  star_mul : star val*val=support
  mul_star : val*star val=support
  mul_support : val*support=val
  support_mul : support*val=val

namespace PartialUnitary

variable {A}

@[simp] lemma star_mul_support (v : PartialUnitary A) : star v.val*v.support=star v.val := by
  simpa only [StarMul.star_mul,v.projection.isSelfAdjoint.star_eq,star_star] using
    congrArg star v.support_mul

@[simp] lemma support_mul_star (v : PartialUnitary A) : v.support*star v.val=star v.val := by
  simpa only [StarMul.star_mul,v.projection.isSelfAdjoint.star_eq,star_star] using
    congrArg star v.mul_support

def power (v : PartialUnitary A) : ℤ → A
  | .ofNat 0 => v.support
  | .ofNat (n+1) => v.val^(n+1)
  | .negSucc n => (star v.val)^(n+1)

@[simp] lemma power_zero (v : PartialUnitary A) : v.power 0=v.support := rfl

end PartialUnitary

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PolarDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma projection_commutes (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (B : H →L[ℂ] H) (hB : ∀ x∈P, B x∈P) (hsB : ∀ x∈P, star B x∈P) :
    P.starProjection*B=B*P.starProjection := by
  ext x
  change P.starProjection (B x)=B (P.starProjection x)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hB _ (P.starProjection_apply_mem x)
  · intro w hw
    rw [←map_sub,←ContinuousLinearMap.adjoint_inner_right]
    exact Submodule.starProjection_inner_eq_zero x _ (hsB w hw)

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PolarExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma positive_kills_of_compression {D P : H →L[ℂ] H} (hD : 0≤D)
    (hP : IsSelfAdjoint P) (h : P*D*P=0) : D*P=0 := by
  have hs : star (CFC.sqrt D*P)*(CFC.sqrt D*P)=0 := by
    rw [star_mul,hP.star_eq,(CFC.sqrt_nonneg D).star_eq]
    calc
      _=P*(CFC.sqrt D*CFC.sqrt D)*P := by noncomm_ring
      _=0 := by rw [CFC.sqrt_mul_sqrt_self D hD,h]
  have hz := (CStarRing.star_mul_self_eq_zero_iff _).mp hs
  calc
    _=(CFC.sqrt D*CFC.sqrt D)*P := by rw [CFC.sqrt_mul_sqrt_self D hD]
    _=0 := by rw [mul_assoc,hz,mul_zero]

lemma abs_fixes_of_square_fixes {W P : H →L[ℂ] H}
    (h : (star W*W)*P=P) : CFC.abs W*P=P := by
  let A := CFC.abs W
  have hA : 0≤A := CFC.abs_nonneg W
  have hu : IsUnit (A+1) := (IsStrictlyPositive.nonneg_add hA isStrictlyPositive_one).isUnit
  have hsq : A*A=star W*W := CFC.abs_mul_abs W
  have he : (A+1)*(A*P-P)=0 := by
    calc
      _=(A*A)*P-P := by noncomm_ring
      _=0 := by rw [hsq,h,sub_self]
  have hz : A*P-P=0 := by
    exact hu.mul_left_cancel (by simpa using he : (A+1)*(A*P-P)=(A+1)*0)
  exact sub_eq_zero.mp hz

end Kadison.Polar

end

end
end

end OAI
end


