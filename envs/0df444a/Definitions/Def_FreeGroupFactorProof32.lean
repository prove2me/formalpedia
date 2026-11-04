-- Prove2me | Definitions.Def_FreeGroupFactorProof32
-- name    : FreeGroupFactorProof32
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T05:09:27.641368+00:00
-- url     : https://prove2.me/theorems/4777787a-df25-49d6-a784-de186773b7a3
-- title:
--   Free group factors: supporting development, part 32
-- statement:
--   Part 32 of the supporting Lean development for the isomorphism of all interpolated free group factors. It continues the chain of earlier parts and contains proved upstream lemmas on the polynomial flow and on corners of the stabilization, with the declarations they rest on, in source order. No result is assumed.
--
--   **Formalization Note** Eight of these lemmas were first published as child theorems, but the platform's target-type check rejected their universe-polymorphic solutions even though the solution type and the published statement have the same elaborated term locally. They are therefore proved here, so that the parent theorems can use them. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof31

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31

namespace FreeGroupFactorMain
namespace InfiniteICC

end InfiniteICC

end FreeGroupFactorMain

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_9} [CStarAlgebra A]

end
section
open scoped ENNReal ComplexConjugate

variable {I : Type u_11} {J : Type u_12}
end
section
open scoped ENNReal

variable {I : Type u_14} {J : Type u_15}

variable {G : Type u_16} [Group G]

end
section
open scoped ENNReal
variable {I : Type u_17} {J : Type u_18}

def matrixEntry (T : GroupOperator (I × J)) (i j : I) : GroupOperator J :=
  (lp.evalCLM ℂ (fun _ : I => GroupHilbert J) 2 i).comp
    ((hilbertFlatten I J).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (T.comp (productSingle I J j)))

@[simp] theorem matrixEntry_apply (T : GroupOperator (I × J)) (i j : I)
    (ξ : GroupHilbert J) (k : J) :
    matrixEntry T i j ξ k = T (productSingle I J j ξ) (i,k) := by
  exact hilbertFlatten_symm_apply _ _ _

theorem productSingle_single [DecidableEq I] [DecidableEq J] [DecidableEq (I × J)]
    (j : I) (g : J) : productSingle I J j (lp.single 2 g 1) = lp.single 2 (j,g) 1 := by
  classical
  ext x
  rcases x with ⟨i,k⟩
  simp only [productSingle_apply,lp.single_apply,Pi.single_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

theorem matrixEntry_ext (T U : GroupOperator (I × J))
    (h : ∀ i j, matrixEntry T i j = matrixEntry U i j) : T = U := by
  classical
  apply operator_matrix_ext
  intro x
  rcases x with ⟨j,g⟩
  rw [← productSingle_single]
  ext y
  rcases y with ⟨i,k⟩
  simpa only [matrixEntry_apply] using congrArg (fun A : GroupOperator J => A (lp.single 2 g 1) k) (h i j)

theorem productAmplification_productSingle (S : GroupOperator J) (j : I) (ξ : GroupHilbert J) :
    productAmplification I J S (productSingle I J j ξ) = productSingle I J j (S ξ) := by
  classical
  ext x
  rcases x with ⟨i,k⟩
  rw [productAmplification_apply,productSingle_apply]
  have he : (hilbertFlatten I J).symm (productSingle I J j ξ) i = if i=j then ξ else 0 := by
    ext l
    simp only [hilbertFlatten_symm_apply,productSingle_apply]
    split_ifs <;> rfl
  rw [he]
  split_ifs <;> simp

theorem matrixEntry_diagonal_mul (S : GroupOperator J) (T : GroupOperator (I × J)) (i j : I) :
    matrixEntry (productAmplification I J S * T) i j = S * matrixEntry T i j := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext k
  simp only [matrixEntry_apply,mul_apply_eq_comp,productAmplification_apply]
  rfl

theorem matrixEntry_mul_diagonal (S : GroupOperator J) (T : GroupOperator (I × J)) (i j : I) :
    matrixEntry (T * productAmplification I J S) i j = matrixEntry T i j * S := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext k
  simp only [matrixEntry_apply,mul_apply_eq_comp,productAmplification_productSingle]

variable {G : Type u_21} [Group G]

theorem mem_stabilization_iff_matrix (T : GroupOperator (ℕ × G)) :
    T ∈ stabilization G ↔ ∀ i j, matrixEntry T i j ∈ groupVonNeumann G := by
  rw [stabilization,StarSubalgebra.mem_centralizer_iff,stabilizedRightTranslations_eq_range]
  constructor
  · intro h i j
    rw [mem_groupVN_iff_commute_right]
    intro g
    have hh := (h _ ⟨g,rfl⟩).1
    have he := congrArg (fun A => matrixEntry A i j) hh
    simpa only [matrixEntry_diagonal_mul,matrixEntry_mul_diagonal] using he
  · intro h S hS
    obtain ⟨g,rfl⟩ := hS
    have hc (g : G) : productAmplification ℕ G (rightRegular g) * T =
        T * productAmplification ℕ G (rightRegular g) := by
      apply matrixEntry_ext
      intro i j
      rw [matrixEntry_diagonal_mul,matrixEntry_mul_diagonal]
      exact (mem_groupVN_iff_commute_right _).mp (h i j) g
    exact ⟨hc g,by rw [← map_star,rightRegular_star]; exact hc g⁻¹⟩

end
section
variable {I : Type u_22} {J : Type u_23}

 def productCoordinate (I : Type u_24) (J : Type u_25) (i : I) : GroupHilbert (I × J) →L[ℂ] GroupHilbert J :=
  (lp.evalCLM ℂ (fun _ : I => GroupHilbert J) 2 i).comp
    (hilbertFlatten I J).symm.toContinuousLinearEquiv.toContinuousLinearMap

 theorem productCoordinate_apply (i : I) (ξ : GroupHilbert (I × J)) (j : J) :
    productCoordinate I J i ξ j=ξ (i,j) := hilbertFlatten_symm_apply _ _ _

 def matrixUnit (I : Type u_26) (J : Type u_27) (i j : I) : GroupOperator (I × J) :=
  (productSingle I J i).comp (productCoordinate I J j)

 theorem matrixUnit_apply [DecidableEq I] (i j k : I) (ξ : GroupHilbert (I × J)) (g : J) :
    matrixUnit I J i j ξ (k,g)=if k=i then ξ (j,g) else 0 := by
  simp only [matrixUnit,ContinuousLinearMap.comp_apply,productSingle_apply,productCoordinate_apply]

 theorem matrixUnit_productSingle [DecidableEq I] (i j l : I) (ξ : GroupHilbert J) :
    matrixUnit I J i j (productSingle I J l ξ)=if j=l then productSingle I J i ξ else 0 := by
  by_cases h : j=l
  · subst l
    rw [ite_eq_left rfl]
    ext x
    rcases x with ⟨k,g⟩
    simp only [matrixUnit_apply,productSingle_apply,ite_true]
  · rw [ite_eq_right h]
    ext x
    rcases x with ⟨k,g⟩
    simp only [matrixUnit_apply,productSingle_apply,ite_eq_right h,ite_self,lp.coeFn_zero,Pi.zero_apply]

 theorem matrixEntry_matrixUnit_mul [DecidableEq I] (i j k l : I) (T : GroupOperator (I × J)) :
    matrixEntry (matrixUnit I J i j*T) k l=if k=i then matrixEntry T j l else 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext g
  simp only [matrixEntry_apply,mul_apply_eq_comp,matrixUnit_apply]
  split_ifs <;> simp only [matrixEntry_apply,zero_apply,lp.coeFn_zero,Pi.zero_apply]

 theorem matrixEntry_mul_matrixUnit [DecidableEq I] (i j k l : I) (T : GroupOperator (I × J)) :
    matrixEntry (T*matrixUnit I J i j) k l=if j=l then matrixEntry T k i else 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext g
  simp only [matrixEntry_apply,mul_apply_eq_comp,matrixUnit_productSingle]
  split_ifs <;> simp

 theorem matrixEntry_matrixUnit [DecidableEq I] (i j k l : I) :
    matrixEntry (matrixUnit I J i j) k l=if k=i ∧ j=l then 1 else 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext g
  simp only [matrixEntry_apply,matrixUnit_apply,productSingle_apply]
  split_ifs <;> simp_all

 theorem matrixEntry_productAmplification [DecidableEq I] (S : GroupOperator J) (i j : I) :
    matrixEntry (productAmplification I J S) i j=if i=j then S else 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext g
  rw [matrixEntry_apply,productAmplification_productSingle,productSingle_apply]
  split_ifs <;> rfl

 variable {G : Type u_28} [Group G]

 theorem matrixUnit_mem_stabilization (i j : ℕ) : matrixUnit ℕ G i j ∈ stabilization G := by
  rw [mem_stabilization_iff_matrix]
  intro k l
  rw [matrixEntry_matrixUnit]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

 theorem diagonal_mem_stabilization (S : groupVonNeumann G) :
    productAmplification ℕ G (S : GroupOperator G) ∈ stabilization G := by
  rw [mem_stabilization_iff_matrix]
  intro k l
  rw [matrixEntry_productAmplification]
  split_ifs
  · exact S.property
  · exact zero_mem _

 theorem stabilization_center_diagonal (T : stabilization G)
    (hc : ∀ S : stabilization G, Commute T S) :
    (T : GroupOperator (ℕ × G))=productAmplification ℕ G (matrixEntry (T : GroupOperator (ℕ × G)) 0 0) := by
  have hm (i j : ℕ) : (T : GroupOperator (ℕ × G))*matrixUnit ℕ G i j=
      matrixUnit ℕ G i j*(T : GroupOperator (ℕ × G)) :=
    congrArg (fun A : stabilization G => (A : GroupOperator (ℕ × G))) (hc ⟨_,matrixUnit_mem_stabilization i j⟩).eq
  have hoff (i j : ℕ) (hij : i ≠ j) : matrixEntry (T : GroupOperator (ℕ × G)) i j=0 := by
    have he := congrArg (fun A => matrixEntry A i j) (hm j j)
    simpa only [matrixEntry_mul_matrixUnit,matrixEntry_matrixUnit_mul,ite_true,ite_eq_right hij] using he
  have hdiag (i : ℕ) : matrixEntry (T : GroupOperator (ℕ × G)) i i=matrixEntry (T : GroupOperator (ℕ × G)) 0 0 := by
    have he := congrArg (fun A => matrixEntry A i 0) (hm i 0)
    simpa only [matrixEntry_mul_matrixUnit,matrixEntry_matrixUnit_mul,ite_true] using he
  apply matrixEntry_ext
  intro i j
  rw [matrixEntry_productAmplification]
  split_ifs with hij
  · subst j
    exact hdiag i
  · exact hoff i j hij

 theorem stabilization_center_scalar
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G, Commute T S) →
      ∃ c : ℂ, T=c • (1 : groupVonNeumann G))
    (T : stabilization G) (hc : ∀ S : stabilization G, Commute T S) :
    ∃ c : ℂ, (T : GroupOperator (ℕ × G))=c • (1 : GroupOperator (ℕ × G)) := by
  let A : groupVonNeumann G := ⟨matrixEntry (T : GroupOperator (ℕ × G)) 0 0,
    (mem_stabilization_iff_matrix _).mp T.property 0 0⟩
  have hA : ∀ S : groupVonNeumann G, Commute A S := by
    intro S
    apply Subtype.ext
    have he := congrArg (fun U : stabilization G => matrixEntry (U : GroupOperator (ℕ × G)) 0 0)
      (hc ⟨_,diagonal_mem_stabilization S⟩).eq
    change matrixEntry ((T : GroupOperator (ℕ × G))*productAmplification ℕ G (S : GroupOperator G)) 0 0=
      matrixEntry (productAmplification ℕ G (S : GroupOperator G)*(T : GroupOperator (ℕ × G))) 0 0 at he
    change matrixEntry (T : GroupOperator (ℕ × G)) 0 0*(S : GroupOperator G)=
      (S : GroupOperator G)*matrixEntry (T : GroupOperator (ℕ × G)) 0 0
    simpa only [matrixEntry_mul_diagonal,matrixEntry_diagonal_mul] using he
  obtain ⟨c,hcA⟩ := hbase A hA
  refine ⟨c,?_⟩
  rw [stabilization_center_diagonal T hc]
  have he : matrixEntry (T : GroupOperator (ℕ × G)) 0 0=c • (1 : GroupOperator G) :=
    congrArg (fun U : groupVonNeumann G => (U : GroupOperator G)) hcA
  rw [he,map_smul,map_one]

 theorem stabilization_center_projection
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G, Commute T S) →
      ∃ c : ℂ, T=c • (1 : groupVonNeumann G))
    (P : GroupOperator (ℕ × G)) (hP : P ∈ stabilization G) (hp : IsStarProjection P)
    (hc : ∀ S ∈ stabilization G, Commute P S) : P=0 ∨ P=1 := by
  classical
  have hc' : ∀ S : stabilization G, Commute (⟨P,hP⟩ : stabilization G) S :=
    fun S => Subtype.ext (hc S S.property).eq
  obtain ⟨c,he⟩ := stabilization_center_scalar hbase ⟨P,hP⟩ hc'
  change P=c • (1 : GroupOperator (ℕ × G)) at he
  have hh := congrArg (fun A : GroupOperator (ℕ × G) => A (lp.single 2 (0,1) (1 : ℂ)) (0,1)) hp.isIdempotentElem
  rw [he] at hh
  have hcc : c*c=c := by
    change c*(c*(lp.single 2 (0,1) (1 : ℂ) : GroupHilbert (ℕ × G)) (0,1))=
      c*(lp.single 2 (0,1) (1 : ℂ) : GroupHilbert (ℕ × G)) (0,1) at hh
    simpa only [lp.single_apply,Pi.single_eq_same,mul_one] using hh
  have hzero : c*(c-1)=0 := by linear_combination hcc
  rcases mul_eq_zero.mp hzero with hz|ho
  · left
    simpa only [hz,zero_smul ℂ (A := GroupOperator (ℕ × G))] using he
  · right
    have ho : c=1 := sub_eq_zero.mp ho
    simpa only [ho,one_smul] using he

end
open scoped ENNReal
variable {I : Type u_29} {J : Type u_30}

 theorem hilbert_ofReal_norm_sq (ξ : lp (fun _ : I => GroupHilbert J) 2) :
    ENNReal.ofReal (‖ξ‖^2)=∑' i, ENNReal.ofReal (‖ξ i‖^2) := by
  have hs : HasSum (fun i => ‖ξ i‖^2) (‖ξ‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal) ξ
  rw [← hs.tsum_eq,ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hs.summable]

 theorem productSingle_inner_right (i : I) (ξ : GroupHilbert (I × J)) (η : GroupHilbert J) :
    inner ℂ ξ (productSingle I J i η)=inner ℂ (productCoordinate I J i ξ) η := by
  classical
  change inner ℂ ξ ((hilbertFlatten I J) (lp.single 2 i η))=
    inner ℂ (((hilbertFlatten I J).symm ξ) i) η
  have he := (hilbertFlatten I J).inner_map_map ((hilbertFlatten I J).symm ξ) (lp.single 2 i η)
  simpa only [LinearIsometryEquiv.apply_symm_apply,lp.inner_single_right] using he

 theorem productSingle_inner_left (i : I) (ξ : GroupHilbert (I × J)) (η : GroupHilbert J) :
    inner ℂ (productSingle I J i η) ξ=inner ℂ η (productCoordinate I J i ξ) := by
  have he := congrArg (star : ℂ → ℂ) (productSingle_inner_right i ξ η)
  change (starRingEnd ℂ) (inner ℂ ξ (productSingle I J i η))=
    (starRingEnd ℂ) (inner ℂ (productCoordinate I J i ξ) η) at he
  simpa only [inner_conj_symm] using he

 theorem matrixEntry_star (T : GroupOperator (I × J)) (i j : I) :
    matrixEntry (star T) i j=star (matrixEntry T j i) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  have he (T : GroupOperator (I × J)) (i j : I) (ξ : GroupHilbert J) :
      matrixEntry T i j ξ=productCoordinate I J i (T (productSingle I J j ξ)) := rfl
  rw [he,← productSingle_inner_left,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,productSingle_inner_right]
  change inner ℂ (matrixEntry T j i η) ξ=inner ℂ η (star (matrixEntry T j i) ξ)
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

 variable {G : Type u_31} [Group G] [DecidableEq G]

 theorem stabilizedProjectionTrace_eq_matrix (T : stabilization G) :
    stabilizedProjectionTrace T=∑' j : ℕ, ∑' i : ℕ,
      ENNReal.ofReal (‖matrixEntry (T : GroupOperator (ℕ × G)) i j (lp.single 2 (1 : G) (1 : ℂ))‖^2) := by
  classical
  apply tsum_congr
  intro j
  rw [← (hilbertFlatten ℕ G).symm.norm_map,hilbert_ofReal_norm_sq]
  apply tsum_congr
  intro i
  congr 2
  congr 1
  ext g
  rw [matrixEntry_apply,productSingle_single,hilbertFlatten_symm_apply]
  apply congrArg (fun ξ : GroupHilbert (ℕ × G) => (T : GroupOperator (ℕ × G)) ξ (i,g))
  ext x
  simp only [lp.single_apply,Pi.single_apply]
  split_ifs <;> rfl

 theorem groupVN_adjoint_delta_norm (T : groupVonNeumann G) :
    ‖(star T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖^2=
    ‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖^2 := by
  classical
  have ht : canonicalTrace (T*star T)=(‖(star T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖^2 : ℂ) := by
    simpa only [star_star,StarMemClass.coe_star] using canonicalTrace_star_mul (star T)
  have he' : (‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖^2 : ℂ)=
      (‖(star T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖^2 : ℂ) := by
    rw [← canonicalTrace_star_mul,← ht]
    exact canonicalTrace_mul (star T) T
  have hh := congrArg Complex.re he'
  simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using hh.symm

 theorem stabilizedProjectionTrace_star (T : stabilization G) :
    stabilizedProjectionTrace (star T)=stabilizedProjectionTrace T := by
  classical
  rw [stabilizedProjectionTrace_eq_matrix,stabilizedProjectionTrace_eq_matrix,ENNReal.tsum_comm]
  apply tsum_congr
  intro i
  apply tsum_congr
  intro j
  congr 1
  simp only [StarMemClass.coe_star]
  rw [matrixEntry_star]
  exact groupVN_adjoint_delta_norm ⟨_,(mem_stabilization_iff_matrix _).mp T.property j i⟩

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25

namespace FreeGroupFactorMain.Amplification
namespace OperatorSum
variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def IsPartial (U : Operator E) : Prop := U*star U*U=U

 theorem initial_projection {U : Operator E} (h : IsPartial U) : IsStarProjection (star U*U) := by
  constructor
  · change (star U*U)*(star U*U)=star U*U
    calc
      _ = star U*(U*star U*U) := by noncomm_ring
      _ = _ := by rw [h]
  · simp only [IsSelfAdjoint,star_mul,star_star]

 theorem partial_star {U : Operator E} (h : IsPartial U) : IsPartial (star U) := by
  have hs := congrArg star h
  simpa only [IsPartial,star_mul,star_star,mul_assoc] using hs

 theorem partial_norm_le {U : Operator E} (h : IsPartial U) : ‖U‖ ≤ 1 := by
  have hn := (initial_projection h).norm_le (star U*U)
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg U]

structure OrthogonalPartials {ι : Type u_7} (U : ι → Operator E) : Prop where
  isPartial : ∀ i, IsPartial (U i)
  initial : Pairwise (fun i j => star (U i)*U j=0)
  final : Pairwise (fun i j => U i*star (U j)=0)

 theorem OrthogonalPartials.adjoint {ι : Type u_8} {U : ι → Operator E} (h : OrthogonalPartials U) :
    OrthogonalPartials (fun i => star (U i)) where
  isPartial i := partial_star (h.isPartial i)
  initial i j hij := by simpa only [star_star] using h.final hij
  final i j hij := by simpa only [star_star] using h.initial hij

 theorem OrthogonalPartials.finite_offdiag {ι : Type u_9} {U : ι → Operator E}
    (h : OrthogonalPartials U) (s : Finset ι) :
    star (∑ i ∈ s, U i)*(∑ i ∈ s, U i) = ∑ i ∈ s, star (U i)*U i := by
  classical
  simp only [star_sum,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_eq_single_of_mem i hi (fun j _ hji => h.initial hji)

 theorem OrthogonalPartials.finite_partial {ι : Type u_10} {U : ι → Operator E}
    (h : OrthogonalPartials U) (s : Finset ι) : IsPartial (∑ i ∈ s, U i) := by
  classical
  change (∑i ∈ s,U i)*star (∑i ∈ s,U i)*(∑i ∈ s,U i) = _
  have hs : (∑i ∈ s,U i)*star (∑i ∈ s,U i) = ∑i ∈ s,U i*star (U i) := by
    simpa only [star_sum,star_star] using h.adjoint.finite_offdiag s
  rw [hs,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single_of_mem i hi]
  · exact h.isPartial i
  · intro j _ hji
    rw [mul_assoc,h.initial (Ne.symm hji),mul_zero]

 theorem OrthogonalPartials.ranges {ι : Type u_11} {U : ι → Operator E}
    (h : OrthogonalPartials U) :
    OrthogonalFamily ℂ (fun i => U i |>.toLinearMap.range)
      (fun i => (U i).toLinearMap.range.subtypeₗᵢ) := by
  rintro i j hij ⟨_,x,rfl⟩ ⟨_,y,rfl⟩
  change inner ℂ (U i x) (U j y) = 0
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ x ((star (U i)*U j) y) = 0
  rw [h.initial hij,zero_apply,inner_zero_right]

 theorem OrthogonalPartials.apply_summable {ι : Type u_12} {U : ι → Operator E}
    (h : OrthogonalPartials U) (x : E) : Summable (fun i => U i x) := by
  let f : ∀ i, (U i).toLinearMap.range := fun i => ⟨U i x,LinearMap.mem_range_self _ x⟩
  apply (h.ranges.summable_iff_norm_sq_summable f).mpr
  apply summable_of_sum_le (fun i => sq_nonneg ‖f i‖) (c := ‖x‖^2)
  intro s
  rw [← h.ranges.norm_sum f s]
  have hn : ‖∑i ∈ s, U i x‖ ≤ ‖x‖ := by
    have hb := (∑i ∈ s, U i).le_opNorm x
    have ho := partial_norm_le (h.finite_partial s)
    calc
      _ = ‖(∑i ∈ s,U i) x‖ := by simp only [sum_apply]
      _ ≤ ‖∑i ∈ s,U i‖*‖x‖ := hb
      _ ≤ 1*‖x‖ := mul_le_mul_of_nonneg_right ho (norm_nonneg _)
      _ = _ := one_mul _
  change ‖∑i ∈ s,U i x‖^2 ≤ ‖x‖^2
  simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hn

 theorem OrthogonalPartials.tsum_bound {ι : Type u_13} {U : ι → Operator E}
    (h : OrthogonalPartials U) (x : E) : ‖∑'i, U i x‖ ≤ ‖x‖ := by
  apply le_of_tendsto ((h.apply_summable x).hasSum.norm)
  apply Filter.Eventually.of_forall
  intro s
  calc
    _ = ‖(∑i ∈ s,U i) x‖ := by simp only [sum_apply]
    _ ≤ ‖∑i ∈ s,U i‖*‖x‖ := (∑i ∈ s,U i).le_opNorm x
    _ ≤ 1*‖x‖ := mul_le_mul_of_nonneg_right (partial_norm_le (h.finite_partial s)) (norm_nonneg _)
    _ = _ := one_mul _

 def OrthogonalPartials.sum {ι : Type u_14} {U : ι → Operator E} (h : OrthogonalPartials U) : Operator E :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑'i,U i x
      map_add' := fun x y => by
        simp only [map_add]
        exact (h.apply_summable x).tsum_add (h.apply_summable y)
      map_smul' := fun c x => by
        simp only [map_smul,RingHom.id_apply]
        exact (h.apply_summable x).tsum_const_smul c }
    1 (fun x => by
      change ‖∑' i, U i x‖ ≤ 1 * ‖x‖
      rw [one_mul]
      exact h.tsum_bound x)

 theorem OrthogonalPartials.sum_apply {ι : Type u_15} {U : ι → Operator E}
    (h : OrthogonalPartials U) (x : E) : h.sum x = ∑'i,U i x := rfl

end OperatorSum
end FreeGroupFactorMain.Amplification
namespace FreeGroupFactorMain.Amplification.OperatorSum

section
variable {E : Type u_16} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type u_17} {U : ι → Operator E}

 theorem OrthogonalPartials.sum_star (h : OrthogonalPartials U) :
    h.adjoint.sum = star h.sum := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  rw [h.adjoint.sum_apply,h.sum_apply]
  change (innerSL ℂ y) (∑' i, star (U i) x) = ((innerSL ℂ).flip x) (∑' i, U i y)
  rw [(innerSL ℂ y).map_tsum (h.adjoint.apply_summable x)]
  have hr := ((innerSL ℂ).flip x).map_tsum (h.apply_summable y)
  rw [hr]
  apply tsum_congr
  intro i
  exact ContinuousLinearMap.adjoint_inner_right (U i) y x

 theorem OrthogonalPartials.star_single_mul_sum (h : OrthogonalPartials U) (i : ι) :
    star (U i)*h.sum = star (U i)*U i := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  rw [mul_apply_eq_comp,h.sum_apply,(star (U i)).map_tsum (h.apply_summable x)]
  rw [tsum_eq_single i]
  · rfl
  · intro j hji
    change (star (U i)*U j) x = 0
    rw [h.initial hji.symm,zero_apply]

 theorem OrthogonalPartials.star_sum_mul_single (h : OrthogonalPartials U) (i : ι) :
    star h.sum*U i = star (U i)*U i := by
  have he := congrArg star (h.star_single_mul_sum i)
  simpa only [star_mul,star_star] using he

 theorem OrthogonalPartials.sum_mul_star_single (h : OrthogonalPartials U) (i : ι) :
    h.sum*star (U i) = U i*star (U i) := by
  have he := h.adjoint.star_sum_mul_single i
  simpa only [h.sum_star,star_star] using he

 theorem OrthogonalPartials.sum_partial (h : OrthogonalPartials U) : IsPartial h.sum := by
  apply ContinuousLinearMap.ext
  intro x
  change (h.sum*star h.sum) (h.sum x) = h.sum x
  rw [h.sum_apply,(h.sum*star h.sum).map_tsum (h.apply_summable x)]
  apply tsum_congr
  intro i
  change (h.sum*star h.sum*U i) x = U i x
  rw [mul_assoc,h.star_sum_mul_single,← mul_assoc,h.sum_mul_star_single,h.isPartial]

 theorem OrthogonalPartials.sum_mem_centralizer (h : OrthogonalPartials U)
    (s : Set (Operator E)) (hU : ∀ i, U i ∈ StarSubalgebra.centralizer ℂ s) :
    h.sum ∈ StarSubalgebra.centralizer ℂ s := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro S hS
  have hc (i) := (StarSubalgebra.mem_centralizer_iff ℂ).mp (hU i) S hS
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    change S (h.sum x) = h.sum (S x)
    rw [h.sum_apply,h.sum_apply,S.map_tsum (h.apply_summable x)]
    apply tsum_congr
    intro i
    exact DFunLike.congr_fun (hc i).1 x
  · apply ContinuousLinearMap.ext
    intro x
    change star S (h.sum x) = h.sum (star S x)
    rw [h.sum_apply,h.sum_apply,(star S).map_tsum (h.apply_summable x)]
    apply tsum_congr
    intro i
    exact DFunLike.congr_fun (hc i).2 x

 theorem OrthogonalPartials.sum_left_support (h : OrthogonalPartials U)
    (q : Operator E) (hq : ∀ i, q*U i=U i) : q*h.sum=h.sum := by
  apply ContinuousLinearMap.ext
  intro x
  rw [mul_apply_eq_comp,h.sum_apply,q.map_tsum (h.apply_summable x)]
  apply tsum_congr
  intro i
  exact DFunLike.congr_fun (hq i) x

 theorem OrthogonalPartials.sum_right_support (h : OrthogonalPartials U)
    (p : Operator E) (hp : ∀ i, U i*p=U i) : h.sum*p=h.sum := by
  apply ContinuousLinearMap.ext
  intro x
  rw [mul_apply_eq_comp,h.sum_apply,h.sum_apply]
  apply tsum_congr
  intro i
  exact DFunLike.congr_fun (hp i) x

end
variable {E : Type u_18} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem residual_projection {p e : Operator E} (hp : IsStarProjection p)
    (he : IsStarProjection e) (hep : e*p=e) : IsStarProjection (p-e) := by
  have hpe : p*e=e := by
    have h := congrArg star hep
    simpa only [star_mul,hp.isSelfAdjoint.star_eq,he.isSelfAdjoint.star_eq] using h
  exact ⟨he.isIdempotentElem.sub hp.isIdempotentElem hep hpe,hp.isSelfAdjoint.sub he.isSelfAdjoint⟩

 theorem OrthogonalPartials.sum_final_mul_single {ι : Type u_19} {U : ι → Operator E}
    (h : OrthogonalPartials U) (i : ι) : h.sum*star h.sum*U i=U i := by
  rw [mul_assoc,h.star_sum_mul_single,← mul_assoc,h.sum_mul_star_single,h.isPartial]

 theorem OrthogonalPartials.single_mul_sum_initial {ι : Type u_20} {U : ι → Operator E}
    (h : OrthogonalPartials U) (i : ι) : U i*star h.sum*h.sum=U i := by
  have he := congrArg star (h.adjoint.sum_final_mul_single i)
  simpa only [h.sum_star,star_mul,star_star,mul_assoc] using he

 theorem IsPartial.initial_zero {U : Operator E} (h : star U*U=0) : U=0 := by
  have hn := congrArg norm h
  rw [CStarRing.norm_star_mul_self,norm_zero] at hn
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg U])

def PartialFamily (s : Set (Operator E)) (p q : Operator E) (F : Set (Operator E)) : Prop :=
  (∀ U ∈ F, U ≠ 0 ∧ U ∈ StarSubalgebra.centralizer ℂ s ∧ IsPartial U ∧ q*U=U ∧ U*p=U) ∧
    F.Pairwise (fun U V => star U*V=0 ∧ U*star V=0)

 theorem maximal_partial_family (s : Set (Operator E)) (p q : Operator E) :
    ∃ F, Maximal (PartialFamily s p q) F := by
  apply zorn_subset {F | PartialFamily s p q F}
  intro c hc hchain
  refine ⟨⋃₀ c,⟨?_,?_⟩,fun S hS => Set.subset_sUnion_of_mem hS⟩
  · intro U hU
    obtain ⟨F,hF,hUF⟩ := Set.mem_sUnion.mp hU
    exact (hc hF).1 U hUF
  · intro U hU V hV hne
    obtain ⟨F,hF,hUF⟩ := Set.mem_sUnion.mp hU
    obtain ⟨G,hG,hVG⟩ := Set.mem_sUnion.mp hV
    rcases hchain.total hF hG with hFG|hGF
    · exact (hc hG).2 (hFG hUF) hVG hne
    · exact (hc hF).2 hUF (hGF hVG) hne

 theorem PartialFamily.orthogonal {s : Set (Operator E)} {p q : Operator E}
    {F : Set (Operator E)} (h : PartialFamily s p q F) :
    OrthogonalPartials (fun U : F => (U : Operator E)) where
  isPartial U := (h.1 U U.property).2.2.1
  initial := by
    intro U V hne
    exact (h.2 U.property V.property (fun he => hne (Subtype.ext he))).1
  final := by
    intro U V hne
    exact (h.2 U.property V.property (fun he => hne (Subtype.ext he))).2

 theorem commutant_maximal_partial (s : Set (Operator E)) (p q : Operator E)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpm : p ∈ StarSubalgebra.centralizer ℂ s) (hqm : q ∈ StarSubalgebra.centralizer ℂ s) :
    ∃ V ∈ StarSubalgebra.centralizer ℂ s, IsPartial V ∧ q*V=V ∧ V*p=V ∧
      ∀ T ∈ StarSubalgebra.centralizer ℂ s, (q-V*star V)*T*(p-star V*V)=0 := by
  classical
  obtain ⟨F,hF⟩ := maximal_partial_family s p q
  let h := hF.1.orthogonal
  let V := h.sum
  have hV : V ∈ StarSubalgebra.centralizer ℂ s :=
    h.sum_mem_centralizer s (fun U => (hF.1.1 U U.property).2.1)
  have hVp : V*p=V := h.sum_right_support p (fun U => (hF.1.1 U U.property).2.2.2.2)
  have hqV : q*V=V := h.sum_left_support q (fun U => (hF.1.1 U U.property).2.2.2.1)
  refine ⟨V,hV,h.sum_partial,hqV,hVp,?_⟩
  intro T hT
  let pr := p-star V*V
  let qr := q-V*star V
  have hpr : IsStarProjection pr := residual_projection hp (initial_projection h.sum_partial) (by rw [mul_assoc,hVp])
  have hqr : IsStarProjection qr := residual_projection hq (by simpa only [star_star] using initial_projection (partial_star h.sum_partial)) (by
    have he := congrArg star hqV
    simp only [star_mul,hq.isSelfAdjoint.star_eq] at he
    rw [mul_assoc,he])
  have hprm : pr ∈ StarSubalgebra.centralizer ℂ s := sub_mem hpm (mul_mem (star_mem hV) hV)
  have hqrm : qr ∈ StarSubalgebra.centralizer ℂ s := sub_mem hqm (mul_mem hV (star_mem hV))
  have hq_qr : q*qr=qr := by
    dsimp [qr]
    rw [mul_sub,hq.isIdempotentElem,← mul_assoc,hqV]
  have hpr_p : pr*p=pr := by
    dsimp [pr]
    rw [sub_mul,hp.isIdempotentElem,mul_assoc,hVp]
  by_contra hne
  let W := Polar.partialIsometry (qr*T*pr)
  have hWne : W ≠ 0 := Polar.partialIsometry_nonzero hne
  have hWm : W ∈ StarSubalgebra.centralizer ℂ s :=
    Polar.partialIsometry_mem_centralizer s (mul_mem (mul_mem hqrm hT) hprm)
  have hWp : W*pr=W := Polar.partialIsometry_right_support hpr.isSelfAdjoint (by rw [mul_assoc,hpr.isIdempotentElem])
  have hqW : qr*W=W := Polar.partialIsometry_left_support (by rw [← mul_assoc,← mul_assoc,hqr.isIdempotentElem])
  have hWpartial : IsPartial W := Polar.partialIsometry_partial _
  have hWp' : W*p=W := by rw [← hWp,mul_assoc,hpr_p]
  have hqW' : q*W=W := by rw [← hqW,← mul_assoc,hq_qr]
  have hqrU (U : F) : qr*U=0 := by
    change (q-V*star V)*(U : Operator E)=0
    rw [sub_mul,(hF.1.1 U U.property).2.2.2.1,h.sum_final_mul_single]
    exact sub_self _
  have hUpr (U : F) : (U : Operator E)*pr=0 := by
    change (U : Operator E)*(p-star V*V)=0
    rw [mul_sub,(hF.1.1 U U.property).2.2.2.2,← mul_assoc,h.single_mul_sum_initial]
    exact sub_self _
  have hUW (U : F) : star (U : Operator E)*W=0 ∧ (U : Operator E)*star W=0 := by
    have he := congrArg star (hqrU U)
    simp only [star_mul,hqr.isSelfAdjoint.star_eq,star_zero (Operator E)] at he
    have hw := congrArg star hWp
    simp only [star_mul,hpr.isSelfAdjoint.star_eq] at hw
    constructor
    · rw [← hqW,← mul_assoc,he,zero_mul]
    · rw [← hw,← mul_assoc,hUpr,zero_mul]
  have hWU (U : F) : star W*(U : Operator E)=0 ∧ W*star (U : Operator E)=0 := by
    constructor
    · simpa only [star_mul,star_star,star_zero (Operator E)] using congrArg star (hUW U).1
    · simpa only [star_mul,star_star,star_zero (Operator E)] using congrArg star (hUW U).2
  have hinsert : PartialFamily s p q (insert W F) := by
    constructor
    · intro U hU
      rcases Set.mem_insert_iff.mp hU with rfl|hU
      · exact ⟨hWne,hWm,hWpartial,hqW',hWp'⟩
      · exact hF.1.1 U hU
    · apply hF.1.2.insert
      intro U hU _
      exact ⟨hWU ⟨U,hU⟩,hUW ⟨U,hU⟩⟩
  have hWF : W ∈ F := hF.2 hinsert (Set.subset_insert _ _) (Set.mem_insert _ _)
  exact hWne (IsPartial.initial_zero (hUW ⟨W,hWF⟩).1)

end FreeGroupFactorMain.Amplification.OperatorSum
namespace FreeGroupFactorMain.Amplification.Polar
variable {E : Type u_21} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem centralSupportSpace_invariant (A : StarSubalgebra ℂ (Operator E)) (p S : Operator E)
    (h : ∀ T ∈ A, ∀ y, ∃ U ∈ A, ∃ z, S (T (p y))=U (p z)) :
    ∀ x ∈ centralSupportSpace A p, S x ∈ centralSupportSpace A p := by
  let K := Submodule.span ℂ {x | ∃ T ∈ A, ∃ y, x=T (p y)}
  have hi : K ∈ Module.End.invtSubmodule S := by
    rw [Module.End.mem_invtSubmodule_iff_map_le,Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro x ⟨T,hT,y,rfl⟩
    change S (T (p y)) ∈ K
    obtain ⟨U,hU,z,he⟩ := h T hT y
    exact Submodule.subset_span ⟨U,hU,z,he⟩
  exact Submodule.topologicalClosure_mem_invtSubmodule hi

 theorem centralSupport_commutes (A : StarSubalgebra ℂ (Operator E)) (p S : Operator E)
    (hS : S ∈ A) : Commute (centralSupportSpace A p).starProjection S := by
  apply starProjection_commute
  · apply centralSupportSpace_invariant
    intro T hT y
    exact ⟨S*T,mul_mem hS hT,y,rfl⟩
  · apply centralSupportSpace_invariant
    intro T hT y
    exact ⟨star S*T,mul_mem (star_mem hS) hT,y,rfl⟩

 theorem centralSupport_mem_centralizer (s : Set (Operator E)) (p : Operator E)
    (hp : p ∈ StarSubalgebra.centralizer ℂ s) :
    (centralSupportSpace (StarSubalgebra.centralizer ℂ s) p).starProjection ∈
      StarSubalgebra.centralizer ℂ s := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro S hS
  have hinv (S' : Operator E) (he : ∀ T ∈ StarSubalgebra.centralizer ℂ s, S'*T=T*S') :
      ∀ x ∈ centralSupportSpace (StarSubalgebra.centralizer ℂ s) p,
        S' x ∈ centralSupportSpace (StarSubalgebra.centralizer ℂ s) p := by
    apply centralSupportSpace_invariant
    intro T hT y
    refine ⟨T,hT,S' y,?_⟩
    change (S'*T*p) y=(T*p*S') y
    rw [he T hT,mul_assoc,he p hp,← mul_assoc]
  have h₁ : ∀ T ∈ StarSubalgebra.centralizer ℂ s, S*T=T*S :=
    fun T hT => ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT S hS).1
  have h₂ : ∀ T ∈ StarSubalgebra.centralizer ℂ s, star S*T=T*star S :=
    fun T hT => ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT S hS).2
  have hc := starProjection_commute _ S (hinv S h₁) (hinv (star S) h₂)
  have hcs := starProjection_commute _ (star S) (hinv (star S) h₂) (by simpa only [star_star] using hinv S h₁)
  exact ⟨hc.eq.symm,hcs.eq.symm⟩

 theorem centralSupport_fixes (A : StarSubalgebra ℂ (Operator E)) (p : Operator E) :
    (centralSupportSpace A p).starProjection*p=p := by
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.starProjection_eq_self_iff.mpr
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span ⟨1,one_mem A,x,by simp⟩

 theorem centralSupport_annihilated (A : StarSubalgebra ℂ (Operator E)) (p q : Operator E)
    (h : ∀ T ∈ A, q*T*p=0) : q*(centralSupportSpace A p).starProjection=0 := by
  have hK : centralSupportSpace A p ≤ q.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro x ⟨T,hT,y,rfl⟩
      change (q*T*p) y=0
      rw [h T hT,zero_apply]
    · exact q.isClosed_ker
  apply ContinuousLinearMap.ext
  intro x
  exact hK (Submodule.starProjection_apply_mem _ x)

 theorem cross_corner_nonzero (s : Set (Operator E))
    (hfactor : ∀ P ∈ StarSubalgebra.centralizer ℂ s, IsStarProjection P →
      (∀ S ∈ StarSubalgebra.centralizer ℂ s, Commute P S) → P=0 ∨ P=1)
    (p q : Operator E) (hp : p ∈ StarSubalgebra.centralizer ℂ s) (hpne : p ≠ 0) (hqne : q ≠ 0) :
    ∃ T ∈ StarSubalgebra.centralizer ℂ s, q*T*p ≠ 0 := by
  by_contra! h
  let A := StarSubalgebra.centralizer ℂ s
  let P := (centralSupportSpace A p).starProjection
  have hm : P ∈ A := centralSupport_mem_centralizer s p hp
  have hf : P*p=p := centralSupport_fixes A p
  rcases hfactor P hm isStarProjection_starProjection (fun S hS => centralSupport_commutes A p S hS) with hP|hP
  · apply hpne
    rw [hP,zero_mul] at hf
    exact hf.symm
  · apply hqne
    have hh := centralSupport_annihilated A p q h
    change q*P=0 at hh
    simpa only [hP,mul_one] using hh

end FreeGroupFactorMain.Amplification.Polar
namespace FreeGroupFactorMain.Amplification.OperatorSum
variable {E : Type u_22} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem factor_partial_comparison (s : Set (Operator E))
    (hfactor : ∀ P ∈ StarSubalgebra.centralizer ℂ s, IsStarProjection P →
      (∀ S ∈ StarSubalgebra.centralizer ℂ s, Commute P S) → P=0 ∨ P=1)
    (p q : Operator E) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpm : p ∈ StarSubalgebra.centralizer ℂ s) (hqm : q ∈ StarSubalgebra.centralizer ℂ s) :
    ∃ V ∈ StarSubalgebra.centralizer ℂ s, IsPartial V ∧ q*V=V ∧ V*p=V ∧
      (star V*V=p ∨ V*star V=q) := by
  obtain ⟨V,hV,hpart,hqV,hVp,hcross⟩ := commutant_maximal_partial s p q hp hq hpm hqm
  refine ⟨V,hV,hpart,hqV,hVp,?_⟩
  by_cases h : p-star V*V=0
  · exact Or.inl (sub_eq_zero.mp h).symm
  · by_cases h' : q-V*star V=0
    · exact Or.inr (sub_eq_zero.mp h').symm
    · obtain ⟨T,hT,hne⟩ := Polar.cross_corner_nonzero s hfactor (p-star V*V) (q-V*star V)
        (sub_mem hpm (mul_mem (star_mem hV) hV)) h h'
      exact (hne (hcross T hT)).elim

end FreeGroupFactorMain.Amplification.OperatorSum
namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
open OperatorSum
variable {E : Type u_23} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem projection_inner (p : E →L[ℂ] E) (hp : IsStarProjection p) (x : E) :
    inner ℂ x (p x)=(‖p x‖^2 : ℂ) := by
  have he := ContinuousLinearMap.adjoint_inner_right p x (p x)
  rw [← ContinuousLinearMap.star_eq_adjoint,hp.isSelfAdjoint.star_eq] at he
  have hh : p (p x)=p x := congrArg (fun T : E →L[ℂ] E => T x) hp.isIdempotentElem.eq
  rw [hh] at he
  exact he.trans (inner_self_eq_norm_sq_to_K (p x))

 theorem partial_initial_norm_sq (V : E →L[ℂ] E) (hV : IsPartial V) (x : E) :
    ‖(star V*V) x‖^2=‖V x‖^2 := by
  have he : (‖(star V*V) x‖ : ℂ)^2=(‖V x‖ : ℂ)^2 := by
    rw [← projection_inner _ (initial_projection hV)]
    exact (ContinuousLinearMap.adjoint_inner_right V x (V x)).trans (inner_self_eq_norm_sq_to_K (V x))
  exact_mod_cast he

 theorem orthogonal_projection_norm_sq (p q : E →L[ℂ] E)
    (hp : IsSelfAdjoint p) (hpq : p*q=0) (x : E) :
    ‖(p+q) x‖^2=‖p x‖^2+‖q x‖^2 := by
  change ‖p x+q x‖^2=_
  rw [sq,sq,sq]
  apply norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
  have he := ContinuousLinearMap.adjoint_inner_right p x (q x)
  rw [← ContinuousLinearMap.star_eq_adjoint,hp.star_eq] at he
  have hz : p (q x)=0 := congrArg (fun T : E →L[ℂ] E => T x) hpq
  rw [hz,inner_zero_right] at he
  exact he.symm

 variable {G : Type u_24} [Group G]

 theorem stabilizedProjectionTrace_faithful (T : stabilization G)
    (h : stabilizedProjectionTrace T=0) : T=0 := by
  classical
  have hdelta (j : ℕ) : (T : GroupOperator (ℕ × G)) (lp.single 2 (j,1) (1 : ℂ))=0 := by
    have hh := (ENNReal.tsum_eq_zero.mp h) j
    have hzero : ‖(T : GroupOperator (ℕ × G)) (lp.single 2 (j,1) (1 : ℂ))‖^2=0 :=
      le_antisymm (ENNReal.ofReal_eq_zero.mp hh) (sq_nonneg _)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  apply Subtype.ext
  apply matrixEntry_ext
  intro i j
  have hm := (mem_stabilization_iff_matrix _).mp T.property i j
  have hz : matrixEntry (T : GroupOperator (ℕ × G)) i j (lp.single 2 (1 : G) (1 : ℂ))=0 := by
    ext g
    rw [matrixEntry_apply,productSingle_single,hdelta]
    rfl
  have he := groupVN_separating ⟨_,hm⟩ hz
  calc
    matrixEntry (T : GroupOperator (ℕ × G)) i j=0 := congrArg (fun A : groupVonNeumann G => (A : GroupOperator G)) he
    _ = matrixEntry (0 : GroupOperator (ℕ × G)) i j := by
      apply ContinuousLinearMap.ext
      intro ξ
      ext g
      rw [matrixEntry_apply]
      rfl

 theorem stabilizedProjectionTrace_initial (V : stabilization G)
    (hV : IsPartial (V : GroupOperator (ℕ × G))) :
    stabilizedProjectionTrace (star V*V)=stabilizedProjectionTrace V := by
  classical
  apply tsum_congr
  intro j
  congr 1
  exact partial_initial_norm_sq (V : GroupOperator (ℕ × G)) hV _

 theorem stabilizedProjectionTrace_initial_final (V : stabilization G)
    (hV : IsPartial (V : GroupOperator (ℕ × G))) :
    stabilizedProjectionTrace (star V*V)=stabilizedProjectionTrace (V*star V) := by
  classical
  rw [stabilizedProjectionTrace_initial V hV]
  have he := stabilizedProjectionTrace_initial (star V) (partial_star hV)
  rw [star_star,stabilizedProjectionTrace_star] at he
  exact he.symm

 theorem stabilizedProjectionTrace_orthogonal_add (p q : stabilization G)
    (hp : IsSelfAdjoint p) (hpq : p*q=0) :
    stabilizedProjectionTrace (p+q)=stabilizedProjectionTrace p+stabilizedProjectionTrace q := by
  classical
  rw [stabilizedProjectionTrace,stabilizedProjectionTrace,stabilizedProjectionTrace,← ENNReal.tsum_add]
  apply tsum_congr
  intro j
  change ENNReal.ofReal (‖((p : GroupOperator (ℕ × G))+(q : GroupOperator (ℕ × G))) (lp.single 2 (j,1) (1 : ℂ))‖^2)=_
  rw [orthogonal_projection_norm_sq (p : GroupOperator (ℕ × G)) q
    (show IsSelfAdjoint (p : GroupOperator (ℕ × G)) from congrArg Subtype.val hp)
    (congrArg Subtype.val hpq),ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]

end
open scoped ENNReal
open OperatorSum

end FreeGroupFactorMain.Amplification

end

end OAI
end


