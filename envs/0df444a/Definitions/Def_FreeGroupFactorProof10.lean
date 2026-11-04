-- Prove2me | Definitions.Def_FreeGroupFactorProof10
-- name    : FreeGroupFactorProof10
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T01:43:06.191883+00:00
-- url     : https://prove2.me/theorems/7edf449a-a9a1-4302-9579-d0fd13d0b8b9
-- title:
--   Free group factors: supporting development, part 10
-- statement:
--   Part 10 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof09

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

section
namespace FreeGroupFactorMain.GramSpatial
variable {I : Type u_1} {E : Type u_2} {F : Type u_3}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

end FreeGroupFactorMain.GramSpatial
namespace FreeGroupFactorMain.GaussianRecognition
variable (A : Type u_4) (E : Type u_5) (I : Type u_6) [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {A E I} {covariance : I → I → A → A}
variable (X : System A E I covariance)

namespace System

variable {F : Type u_9} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (Y : System A F I covariance)

variable
  (hstate : ∀ a, inner ℂ Y.root (Y.coeff a Y.root)=inner ℂ X.root (X.coeff a X.root))
  (hX : (Submodule.span ℂ (Set.range X.family)).topologicalClosure=⊤)
  (hY : (Submodule.span ℂ (Set.range Y.family)).topologicalClosure=⊤)

end System
end FreeGroupFactorMain.GaussianRecognition

end

namespace FreeGroupFactorMain.GaussianRecognition
open CyclicSpectral

end FreeGroupFactorMain.GaussianRecognition

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification CyclicSpectral GaussianRecognition WeightedCornerIndex

theorem absorbedCreation_cov_diagonal (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (i : WeightedCornerIndex.Index × ℕ) (a : UniformAlgebra) :
    star (absorbedCreation u v hv hvu i)*weightedUniform u v hv hvu a*absorbedCreation u v hv hvu i=
      uniformState a • 1 := by
  let b := weightedUniformBase u v hv hvu a
  have hc := (cornerAbsorption u v hv hvu).output_cov i.1 i.1 i.2 i.2 b
  rw [ite_eq_left ⟨rfl,rfl⟩,cornerAbsorption_trace,weightedUniformBase_trace] at hc
  have hs (X : PCorner ℕ) : pRepresentation (star X)=star (pRepresentation X) :=
    (pRepresentation (ι := ℕ)).map_star' X
  have hm (c : ℂ) (X : PCorner ℕ) : pRepresentation (c • X)=c • pRepresentation X :=
    (pRepresentation (ι := ℕ)).map_smul' c X
  have hh := congrArg (fun X : PCorner ℕ => pRepresentation X) hc
  simp only [map_mul,hs,hm,map_one] at hh
  rw [weightedUniformBase_rep] at hh
  exact hh

theorem absorbedCreation_cov_off (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (i j : WeightedCornerIndex.Index × ℕ) (h : i≠j) (a : UniformAlgebra) :
    star (absorbedCreation u v hv hvu i)*weightedUniform u v hv hvu a*absorbedCreation u v hv hvu j=0 := by
  let b := weightedUniformBase u v hv hvu a
  have hc := (cornerAbsorption u v hv hvu).output_cov i.1 j.1 i.2 j.2 b
  have hn : ¬(i.1=j.1 ∧ i.2=j.2) := fun he => h (Prod.ext he.1 he.2)
  rw [ite_eq_right hn] at hc
  have hs (X : PCorner ℕ) : pRepresentation (star X)=star (pRepresentation X) :=
    (pRepresentation (ι := ℕ)).map_star' X
  have hh := congrArg (fun X : PCorner ℕ => pRepresentation X) hc
  simp only [map_mul,hs,map_zero] at hh
  rw [weightedUniformBase_rep] at hh
  exact hh

theorem absorbedCreation_annihilate (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (i : WeightedCornerIndex.Index × ℕ) (a : UniformAlgebra) :
    star (absorbedCreation u v hv hvu i) (weightedUniform u v hv hvu a pRoot)=0 := by
  have hh := pAnnihilator_root u v (hv.trans hvu).ne'
    ((cornerAbsorption u v hv hvu).output i.1 i.2)
    (cornerAbsorption_annihilator u v hv hvu i.1 i.2) (weightedUniformBase u v hv hvu a)
  rw [weightedUniformBase_rep] at hh
  exact hh

def weightedSystem (u v : ℝ) (hv : 0<v) (hvu : v<u) :
    GaussianRecognition.System UniformAlgebra (PRange ℕ) (WeightedCornerIndex.Index × ℕ) uniformCovariance where
  coeff := weightedUniform u v hv hvu
  root := pRoot
  create := absorbedCreation u v hv hvu
  contract i j a := by
    by_cases h : i=j
    · subst j
      simpa only [uniformCovariance,ite_true,map_smul,map_one] using
        absorbedCreation_cov_diagonal u v hv hvu i a
    · simpa only [uniformCovariance,ite_eq_right h,map_zero] using
        absorbedCreation_cov_off u v hv hvu i j h a
  annihilate := absorbedCreation_annihilate u v hv hvu
end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

section
namespace FreeGroupFactorMain.CornerRerouting
variable {A : Type u_1} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

end FreeGroupFactorMain.CornerRerouting

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification CyclicSpectral
variable {ι : Type u_3} [DecidableEq ι]

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

end

section
open FreeFock Amplification WeightedCornerIndex
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

variable {ι : Type u_4} [DecidableEq ι]

end

section
open FreeFock Amplification WeightedCornerIndex
variable {ι : Type u_5} [DecidableEq ι]

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)
variable (M : StarSubalgebra ℂ (PCorner ℕ))
    (hbase : ∀ a : Base u v,(a:PCorner ℕ)∈M)
    (hout : ∀ i n,(cornerAbsorption u v hv hvu).output i n+
      star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈M)

end

open FreeFock Amplification WeightedCornerIndex GaussianRecognition
variable {ι : Type u_6} [DecidableEq ι]

def pAmbient (u v : ℝ) : StarSubalgebra ℂ (PCorner ι) :=
  subalgebraCorner (ambientAlgebra u v) P projection_P (P_mem_ambient u v)

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

namespace FreeGroupFactorMain.Amplification
variable {A : Type u_1} [CStarAlgebra A]

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.FreeFock

section
open scoped ENNReal
variable {α : Type u_2} [DecidableEq α]

 def creationWord : List α → Operator α
  | [] => 1
  | a::w => creation a*creationWord w

@[simp] theorem creationWord_nil : creationWord ([] : List α)=1 := rfl
@[simp] theorem creationWord_cons (a : α) (w : List α) :
    creationWord (a::w)=creation a*creationWord w := rfl

 theorem creationWord_append (v w : List α) :
    creationWord (v++w)=creationWord v*creationWord w := by
  induction v with
  | nil => simp
  | cons a v ih => simp only [List.cons_append,creationWord_cons,ih,mul_assoc]

 theorem creationWord_vacuum (w : List α) : creationWord w vacuum=lp.single 2 w 1 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change creation a (creationWord w vacuum)=_
    rw [ih,creation_single]

 theorem creationWord_star_vacuum (w : List α) :
    star (creationWord w) vacuum=if w=[] then vacuum else 0 := by
  cases w with
  | nil => simp
  | cons a w =>
    simp only [creationWord_cons,star_mul,List.cons_ne_nil,ite_false]
    change star (creationWord w) (star (creation a) (lp.single 2 [] 1))=0
    rw [annihilation_single_nil,map_zero]

 def wick (w : List α) : Operator α :=
  ∑ k ∈ Finset.range (w.length+1), creationWord (w.take k)*star (creationWord (w.drop k).reverse)

 @[simp] theorem wick_nil : wick ([] : List α)=1 := by simp [wick]

 theorem wick_star (w : List α) : star (wick w)=wick w.reverse := by
  rw [wick,star_sum (R := Operator α)]
  simp only [star_mul,star_star]
  have hs := Finset.sum_range_reflect
    (fun k => creationWord (w.reverse.take k)*star (creationWord (w.reverse.drop k).reverse)) (w.length+1)
  calc
    _ = ∑ k ∈ Finset.range (w.length+1),
        creationWord (w.reverse.take (w.length+1-1-k))*
          star (creationWord (w.reverse.drop (w.length+1-1-k)).reverse) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      simp only [Nat.add_sub_cancel,List.take_reverse,List.drop_reverse,List.reverse_reverse]
      rw [Nat.sub_sub_self hk']
    _ = wick w.reverse := by simpa only [wick,List.length_reverse] using hs

 theorem wick_vacuum (w : List α) : wick w vacuum=lp.single 2 w 1 := by
  classical
  rw [wick,sum_apply]
  calc
    _ = (creationWord (w.take w.length)*star (creationWord (w.drop w.length).reverse)) vacuum := by
      apply Finset.sum_eq_single w.length
      · intro k hk hkn
        have hk' : k < w.length := lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hkn
        change creationWord (w.take k) (star (creationWord (w.drop k).reverse) vacuum)=0
        rw [creationWord_star_vacuum]
        have hn : (w.drop k).reverse ≠ [] := by
          intro he
          have hh := congrArg List.length he
          simp only [List.length_reverse,List.length_drop,List.length_nil] at hh
          omega
        rw [ite_eq_right hn,map_zero]
      · intro h
        exact False.elim (h (Finset.mem_range.mpr (Nat.lt_succ_self _)))
    _ = _ := by
      simp only [List.take_length,List.drop_length,List.reverse_nil,creationWord_nil,star_one,mul_one]
      exact creationWord_vacuum w

 theorem wick_creation_formula (a : α) (w : List α) :
    wick (a::w)=creation a*wick w+star (creation a)*star (creationWord w.reverse) := by
  rw [wick,List.length_cons,Finset.sum_range_succ']
  have he (k : ℕ) :
      creationWord ((a::w).take (k+1))*star (creationWord ((a::w).drop (k+1)).reverse)=
      creation a*(creationWord (w.take k)*star (creationWord (w.drop k).reverse)) := by
    simp only [List.take_succ_cons,List.drop_succ_cons,creationWord_cons,mul_assoc]
  simp_rw [he]
  rw [← Finset.mul_sum]
  simp only [List.take_zero,List.drop_zero,creationWord_nil,one_mul,List.reverse_cons,
    creationWord_append,creationWord_cons,creationWord_nil,mul_one,star_mul]
  rfl

 theorem wick_semicircular_cons (a : α) (w : List α) :
    wick (a::w)=semicircular a*wick w-
      (match w with | [] => 0 | b::v => if a=b then wick v else 0) := by
  cases w with
  | nil => simp [wick_creation_formula,semicircular]
  | cons b v =>
    rw [wick_creation_formula a,wick_creation_formula b]
    change creation a*(creation b*wick v+star (creation b)*star (creationWord v.reverse))+
       star (creation a)*star (creationWord (b::v).reverse)=
      (creation a+star (creation a))*(creation b*wick v+star (creation b)*star (creationWord v.reverse))-
        (if a=b then wick v else 0)
    simp only [List.reverse_cons,creationWord_append,creationWord_cons,creationWord_nil,mul_one,star_mul]
    have he : (star (creation a)*creation b)*wick v=if a=b then wick v else 0 := by
      rw [annihilation_creation]
      by_cases h : a=b <;> simp [h]
    rw [← he]
    noncomm_ring

end

section
variable {α : Type u_3} [DecidableEq α]

def runSpan (i : α) : Submodule ℂ (Operator α) :=
  Submodule.span ℂ (Set.range (fun n : ℕ => wick (List.replicate n i)))

def positiveRunSpan (i : α) : Submodule ℂ (Operator α) :=
  Submodule.span ℂ (Set.range (fun n : ℕ => wick (List.replicate (n+1) i)))

 theorem run_mem (i : α) (n : ℕ) : wick (List.replicate n i) ∈ runSpan i :=
  Submodule.subset_span (Set.mem_range_self n)

 theorem semicircular_mul_runSpan (i : α) (x : Operator α) (hx : x∈runSpan i) :
    semicircular i*x∈runSpan i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n,rfl⟩ := hx
    have h := wick_semicircular_cons i (List.replicate n i)
    cases n with
    | zero => simpa [wick_semicircular_cons] using run_mem i 1
    | succ n =>
      have he : semicircular i*wick (List.replicate (n+1) i)=
          wick (List.replicate (n+2) i)+wick (List.replicate n i) := by
        simpa only [List.replicate_succ,ite_true] using (eq_add_of_sub_eq h.symm)
      rw [he]
      exact (runSpan i).add_mem (run_mem i (n+2)) (run_mem i n)
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add] using (runSpan i).add_mem hx hy
  | smul c x _ hx => simpa only [mul_smul_comm] using (runSpan i).smul_mem c hx

 theorem run_mul_runSpan (i : α) (n : ℕ) (x : Operator α) (hx : x∈runSpan i) :
    wick (List.replicate n i)*x∈runSpan i := by
  suffices ∀ n, (wick (List.replicate n i)*x∈runSpan i) ∧
      (wick (List.replicate (n+1) i)*x∈runSpan i) from (this n).1
  intro n
  induction n with
  | zero =>
    constructor
    · simpa using hx
    · simpa [wick_semicircular_cons] using semicircular_mul_runSpan i x hx
  | succ n ih =>
    refine ⟨ih.2,?_⟩
    have he : wick (List.replicate (n+1+1) i)=
        semicircular i*wick (List.replicate (n+1) i)-wick (List.replicate n i) := by
      conv_lhs => rw [List.replicate_succ,wick_semicircular_cons]
      simp only [List.replicate_succ,ite_true]
    rw [he,sub_mul,mul_assoc]
    exact (runSpan i).sub_mem (semicircular_mul_runSpan i _ ih.2) ih.1

def runAlgebra (i : α) : StarSubalgebra ℂ (Operator α) where
  carrier := (runSpan i : Set (Operator α))
  zero_mem' := (runSpan i).zero_mem
  add_mem' := (runSpan i).add_mem
  algebraMap_mem' c := by
    change algebraMap ℂ (Operator α) c∈runSpan i
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (runSpan i).smul_mem c (show (1 : Operator α)∈runSpan i by simpa using run_mem i 0)
  one_mem' := by simpa using run_mem i 0
  mul_mem' {a b} hx hy := by
    change a∈runSpan i at hx
    change b∈runSpan i at hy
    change a*b∈runSpan i
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨n,rfl⟩ := hx; exact run_mul_runSpan i n _ hy
    | zero => simp
    | add x y _ _ hx hy => simpa only [add_mul] using (runSpan i).add_mem hx hy
    | smul c x _ hx => simpa only [smul_mul_assoc] using (runSpan i).smul_mem c hx
  star_mem' {a} hx := by
    change a∈runSpan i at hx
    change star a∈runSpan i
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨n,rfl⟩ := hx; simpa only [wick_star,List.reverse_replicate] using run_mem i n
    | zero => simpa only [star_zero (R := Operator α)] using (runSpan i).zero_mem
    | add x y _ _ hx hy => simpa only [star_add (R := Operator α)] using (runSpan i).add_mem hx hy
    | smul c x _ hx => simpa only [star_smul] using (runSpan i).smul_mem (star c) hx

 theorem vacuumTrace_linear : IsLinearMap ℂ (@vacuumTrace α _) where
  map_add := by intro x y; simp [vacuumTrace]
  map_smul := by intro c x; simp [vacuumTrace]

 theorem vacuumTrace_continuous : Continuous (@vacuumTrace α _) := by
  exact continuous_const.inner (continuous_id.clm_apply continuous_const)

 theorem vacuumTrace_run (i : α) (n : ℕ) :
    vacuumTrace (wick (List.replicate n i))=if n=0 then 1 else 0 := by
  cases n with
  | zero => simpa using (vacuumTrace_one (α := α))
  | succ n =>
    unfold vacuumTrace
    rw [wick_vacuum]
    simp [vacuum,lp.inner_single_left,lp.single_apply]

end
variable {α : Type u_4} [DecidableEq α]

theorem run_star_creation (a j : α) (h : a≠j) (n : ℕ) :
    star (creationWord (List.replicate (n+1) a))*creation j=0 := by
  rw [List.replicate_succ,creationWord_cons,star_mul,mul_assoc,annihilation_creation,ite_eq_right h,mul_zero]

theorem run_creation (a j : α) (h : a≠j) (n : ℕ) :
    wick (List.replicate n a)*creation j=creationWord (List.replicate n a)*creation j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ,wick_creation_formula,add_mul,mul_assoc,ih]
    have hz : star (creation a)*star (creationWord (List.replicate n a).reverse)*creation j=0 := by
      rw [List.reverse_replicate]
      have he : star (creation a)*star (creationWord (List.replicate n a))=
          star (creationWord (List.replicate (n+1) a)) := by
        rw [show List.replicate (n+1) a=List.replicate n a++[a] from (List.replicate_add _ _ _).trans (by simp),
          creationWord_append,star_mul,creationWord_cons,creationWord_nil,mul_one]
      rw [he,run_star_creation a j h]
    rw [hz,add_zero,creationWord_cons,mul_assoc]

theorem run_coarse_covariance (a i j : α) (hi : i≠a) (hj : j≠a) (n : ℕ) :
    star (creation i)*wick (List.replicate n a)*creation j=
      vacuumTrace (wick (List.replicate n a)) • (if i=j then (1:Operator α) else 0) := by
  rw [mul_assoc,run_creation a j hj.symm,vacuumTrace_run]
  cases n with
  | zero => simp [annihilation_creation]
  | succ n =>
    rw [List.replicate_succ,creationWord_cons,← mul_assoc,← mul_assoc,annihilation_creation,
      ite_eq_right hi,zero_mul,zero_mul]
    simp [zero_smul ℂ (A := Operator α)]

theorem polynomial_coarse_covariance (a i j : α) (hi : i≠a) (hj : j≠a)
    (T : Operator α) (hT : T∈runSpan a) :
    star (creation i)*T*creation j=vacuumTrace T • (if i=j then (1:Operator α) else 0) := by
  induction hT using Submodule.span_induction with
  | mem T hT => obtain ⟨n,rfl⟩ := hT; exact run_coarse_covariance a i j hi hj n
  | zero => simp [vacuumTrace,zero_smul ℂ (A := Operator α)]
  | add T U _ _ hT hU =>
    simp only [mul_add,add_mul,hT,hU,(vacuumTrace_linear (α := α)).map_add,
      add_smul (R := ℂ) (M := Operator α)]
  | smul c T _ hT =>
    simp only [mul_smul_comm,smul_mul_assoc,hT,(vacuumTrace_linear (α := α)).map_smul,smul_smul,smul_eq_mul]

theorem closed_coarse_covariance (a i j : α) (hi : i≠a) (hj : j≠a)
    (T : (runAlgebra a).topologicalClosure) :
    star (creation i)*(T:Operator α)*creation j=vacuumTrace (T:Operator α) • (if i=j then (1:Operator α) else 0) := by
  exact closure_minimal (fun x hx => polynomial_coarse_covariance a i j hi hj x hx)
    (isClosed_eq ((continuous_const.mul continuous_id).mul continuous_const)
      (vacuumTrace_continuous.smul continuous_const)) T.property

theorem closed_coefficient_annihilation (a i : α) (hi : i≠a)
    (T : (runAlgebra a).topologicalClosure) : star (creation i) ((T:Operator α) vacuum)=0 := by
  apply closure_minimal (t := {T:Operator α | star (creation i) (T vacuum)=0}) ?_
    (isClosed_eq ((star (creation i)).continuous.comp (continuous_id.clm_apply continuous_const)) continuous_const) T.property
  intro T hT
  change T∈runSpan a at hT
  change star (creation i) (T vacuum)=0
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨n,rfl⟩ := hT
    rw [wick_vacuum]
    cases n with
    | zero => exact annihilation_single_nil i 1
    | succ n => rw [List.replicate_succ,annihilation_single_cons,ite_eq_right hi]
  | zero => simp
  | add T U _ _ hT hU => simp only [add_apply,map_add,hT,hU,add_zero]
  | smul c T _ hT => simp only [smul_apply,map_smul,hT,smul_zero]
end FreeGroupFactorMain.FreeFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.FreeFock

section
open Filter Topology
open scoped ENNReal
variable {α : Type u_1} [DecidableEq α]

omit [DecidableEq α] in
 theorem repeat_coordinates_decay (i : α) (ξ : Fock α) :
    Tendsto (fun n => ξ (List.replicate n i)) atTop (𝓝 0) := by
  have hf : Function.Injective (fun n => List.replicate n i) := by
    intro n m h
    simpa only [List.length_replicate] using congrArg List.length h
  have hs : Summable (fun w : List α => ‖ξ w‖^2) := by
    simpa using (lp.memℓp ξ).summable (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)
  have ht := (hs.comp_injective hf).tendsto_atTop_zero
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh

 theorem semicircular_repeat_zero (i : α) :
    semicircular i (lp.single 2 [] 1)=lp.single 2 [i] 1 := by
  simp only [semicircular,add_apply,creation_single,annihilation_single_nil,add_zero]

 theorem semicircular_repeat_succ (i : α) (n : ℕ) :
    semicircular i (lp.single 2 (List.replicate (n+1) i) 1)=
      lp.single 2 (List.replicate (n+2) i) 1+lp.single 2 (List.replicate n i) 1 := by
  simp only [semicircular,add_apply,creation_single,List.replicate_succ,
    annihilation_single_cons,ite_true]

end

section
open MeasureTheory
variable {α : Type u_2} [DecidableEq α]

end
section
open CyclicSpectral MeasureTheory
variable {α : Type u_3} [DecidableEq α]

end

open CyclicSpectral GaussianRecognition CircularRotation WeightedCornerIndex

end FreeGroupFactorMain.FreeFock

end

end OAI
end


