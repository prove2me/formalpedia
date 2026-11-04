-- Prove2me | Definitions.Def_FreeGroupFactorProof12
-- name    : FreeGroupFactorProof12
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T01:56:46.567606+00:00
-- url     : https://prove2.me/theorems/cb127eae-e1d3-45a4-abfe-5a84c87fed1c
-- title:
--   Free group factors: supporting development, part 12
-- statement:
--   Part 12 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof11

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace FreeGroupFactorMain.GaussianRecognition
section Algebraic
variable {A : Type u_1} {B : Type u_2} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]

end Algebraic

variable {E : Type u_3} {F : Type u_4}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

namespace System
variable {A : Type u_6} {I : Type u_7} [Ring A] [StarRing A] [Algebra ℂ A]
variable {covariance : I → I → A → A}
variable (X : System A E I covariance) (Y : System A F I covariance)
variable
  (hstate : ∀ a,inner ℂ Y.root (Y.coeff a Y.root)=inner ℂ X.root (X.coeff a X.root))
  (hX : (Submodule.span ℂ (Set.range X.family)).topologicalClosure=⊤)
  (hY : (Submodule.span ℂ (Set.range Y.family)).topologicalClosure=⊤)

end System
end FreeGroupFactorMain.GaussianRecognition

namespace FreeGroupFactorMain.GaussianRecognition.System
variable {A : Type u_8} {E : Type u_9} {I : Type u_10} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

theorem normalHull_preserve (T : Operator E) (hT : ∀ ξ∈X.normalSpan,T ξ∈X.normalSpan)
    {ξ : E} (hξ : ξ∈X.normalHull) : T ξ∈X.normalHull :=
  closure_minimal (t := {ξ:E | T ξ∈X.normalHull})
    (fun ξ hξ => X.normalSpan.le_topologicalClosure (hT ξ hξ))
    (X.normalSpan.isClosed_topologicalClosure.preimage T.continuous) hξ

theorem normalHull_root : X.root∈X.normalHull := by
  have hh := X.normalSpan.le_topologicalClosure (X.normal_mem 1 [])
  simpa only [normal,map_one,one_apply_eq_self,normalHull] using hh

theorem normalHull_coeff (a : A) {ξ : E} (hξ : ξ∈X.normalHull) : X.coeff a ξ∈X.normalHull :=
  X.normalHull_preserve _ (fun _ h => X.normalSpan_coeff a h) hξ

theorem normalHull_create (i : I) {ξ : E} (hξ : ξ∈X.normalHull) : X.create i ξ∈X.normalHull :=
  X.normalHull_preserve _ (fun _ h => X.normalSpan_create i h) hξ

theorem normalHull_annihilate (i : I) {ξ : E} (hξ : ξ∈X.normalHull) : star (X.create i) ξ∈X.normalHull :=
  X.normalHull_preserve _ (fun _ h => X.normalSpan_annihilate i h) hξ

theorem normalHull_projection_coeff (a : A) : Commute X.normalHull.starProjection (X.coeff a) := by
  apply projection_commutes_of_invariant X.normalHull
  · exact fun _ h => X.normalHull_coeff a h
  · simpa only [← map_star] using (fun ξ h => X.normalHull_coeff (star a) (ξ := ξ) h)

theorem normalHull_projection_create (i : I) : Commute X.normalHull.starProjection (X.create i) :=
  projection_commutes_of_invariant X.normalHull _
    (fun _ h => X.normalHull_create i h) (fun _ h => X.normalHull_annihilate i h)

theorem normalHull_projection_annihilate (i : I) : Commute X.normalHull.starProjection (star (X.create i)) :=
  projection_commutes_of_invariant X.normalHull _
    (fun _ h => X.normalHull_annihilate i h) (by simpa only [star_star] using (fun ξ h => X.normalHull_create i (ξ := ξ) h))

theorem normalHull_projection_generator (σ : I → I) (i : I) :
    Commute X.normalHull.starProjection (X.generator σ i) :=
  (X.normalHull_projection_create i).add_right (X.normalHull_projection_annihilate (σ i))

theorem normalHull_bicommutant (σ : I → I) (T : Operator E) (hT : T∈X.generated σ) : T X.root∈X.normalHull := by
  have hP : X.normalHull.starProjection∈StarSubalgebra.centralizer ℂ (X.generators σ) := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro U hU
    rcases hU with ⟨a,rfl⟩ | ⟨i,rfl⟩
    · exact ⟨(X.normalHull_projection_coeff a).eq.symm,
        (by simpa only [map_star] using (X.normalHull_projection_coeff (star a)).eq.symm)⟩
    · refine ⟨(X.normalHull_projection_generator σ i).eq.symm,?_⟩
      change star (X.create i+star (X.create (σ i)))*_= _*star (X.create i+star (X.create (σ i)))
      rw [star_add (R := Operator E),star_star]
      exact ((X.normalHull_projection_annihilate i).add_right (X.normalHull_projection_create (σ i))).eq.symm
  have hh := DFunLike.congr_fun ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT _ hP).1 X.root
  change X.normalHull.starProjection (T X.root)=T (X.normalHull.starProjection X.root) at hh
  rw [X.normalHull.starProjection_eq_self_iff.mpr X.normalHull_root] at hh
  exact X.normalHull.starProjection_eq_self_iff.mp hh
end FreeGroupFactorMain.GaussianRecognition.System

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.FreeFock

section
open scoped ENNReal
variable {α : Type u_1} [DecidableEq α]

 def appendEmbedding (b : α) : List α ↪ List α :=
  ⟨fun w => w++[b],fun _ _ h => List.append_cancel_right h⟩

 def rightCreation (b : α) : Operator α :=
  (hilbertEmbedding (appendEmbedding b)).toContinuousLinearMap

@[simp] theorem rightCreation_single (b : α) (w : List α) (z : ℂ) :
    rightCreation b (lp.single 2 w z)=lp.single 2 (w++[b]) z :=
  hilbertEmbedding_single (appendEmbedding b) w z

 theorem creation_rightCreation (a b : α) :
    creation a*rightCreation b=rightCreation b*creation a := by
  apply operator_basis_ext (α := List α)
  intro w
  simp only [mul_apply_eq_comp,creation_single,rightCreation_single,List.cons_append]

 def vacuumProjection : Operator α := InnerProductSpace.rankOne ℂ vacuum vacuum

@[simp] theorem vacuumProjection_nil (z : ℂ) :
    vacuumProjection (lp.single 2 ([] : List α) z)=lp.single 2 [] z := by
  classical
  ext w
  simp [vacuumProjection,InnerProductSpace.rankOne_apply,vacuum,lp.inner_single_left,
    lp.single_apply,Pi.single_apply]

@[simp] theorem vacuumProjection_cons (a : α) (w : List α) (z : ℂ) :
    vacuumProjection (lp.single 2 (a::w) z)=0 := by
  simp [vacuumProjection,InnerProductSpace.rankOne_apply,vacuum,lp.inner_single_left,lp.single_apply]

 theorem annihilation_rightCreation (a b : α) :
    star (creation a)*rightCreation b=
      rightCreation b*star (creation a)+(if a=b then vacuumProjection else 0) := by
  apply operator_basis_ext (α := List α)
  intro w
  cases w with
  | nil =>
    simp only [mul_apply_eq_comp,add_apply,rightCreation_single,
      List.nil_append,annihilation_single_cons,annihilation_single_nil,map_zero,zero_add]
    by_cases h : a=b <;> simp [h]
  | cons c w =>
    simp only [mul_apply_eq_comp,add_apply,rightCreation_single,
      List.cons_append,annihilation_single_cons]
    have hp : (if a=b then (vacuumProjection : Operator α) else 0) (lp.single 2 (c::w) 1)=0 := by
      split_ifs <;> simp
    rw [hp,add_zero]
    by_cases h : a=c
    · rw [ite_eq_left h,ite_eq_left h,rightCreation_single]
    · rw [ite_eq_right h,ite_eq_right h,map_zero]

 theorem vacuumProjection_selfAdjoint : star (vacuumProjection (α := α))=vacuumProjection := by
  simp [vacuumProjection,ContinuousLinearMap.star_eq_adjoint]

 theorem creation_rightAnnihilation (a b : α) :
    creation a*star (rightCreation b)=
      star (rightCreation b)*creation a-(if a=b then vacuumProjection else 0) := by
  have h := congrArg star (annihilation_rightCreation a b)
  simp only [star_mul,star_star,star_add (R := Operator α)] at h
  have he : star (if a=b then (vacuumProjection : Operator α) else 0)=
      if a=b then vacuumProjection else 0 := by
    split_ifs <;> simp [vacuumProjection_selfAdjoint,star_zero (R := Operator α)]
  rw [he] at h
  exact eq_sub_of_add_eq h.symm

 def rightSemicircular (a : α) : Operator α := rightCreation a+star (rightCreation a)

 theorem semicircular_rightSemicircular (a b : α) :
    Commute (semicircular a) (rightSemicircular b) := by
  have hc := creation_rightCreation a b
  have ha := congrArg star hc
  simp only [star_mul] at ha
  have hL := annihilation_rightCreation a b
  have hR := creation_rightAnnihilation a b
  change (creation a+star (creation a))*(rightCreation b+star (rightCreation b))=
    (rightCreation b+star (rightCreation b))*(creation a+star (creation a))
  noncomm_ring [hc,ha,hL,hR]

end
section
open scoped ENNReal ComplexConjugate
variable {α : Type u_2} [DecidableEq α]

 def reverseEmbedding : List α ↪ List α := ⟨List.reverse,List.reverse_injective⟩
 def reverseIsometry : Fock α →ₗᵢ[ℂ] Fock α := hilbertEmbedding reverseEmbedding
 def reverseOperator : Operator α := reverseIsometry.toContinuousLinearMap

@[simp] theorem reverseOperator_single (w : List α) (z : ℂ) :
    reverseOperator (lp.single 2 w z)=lp.single 2 w.reverse z :=
  hilbertEmbedding_single reverseEmbedding w z

 theorem reverseOperator_square : (reverseOperator : Operator α)*reverseOperator=1 := by
  apply operator_basis_ext (α := List α)
  intro w
  simp only [mul_apply_eq_comp,reverseOperator_single,List.reverse_reverse,one_apply_eq_self]

 theorem reverseOperator_involutive (ξ : Fock α) :
    reverseOperator (reverseOperator ξ)=ξ := by
  have hi := DFunLike.congr_fun (reverseOperator_square (α := α)) ξ
  exact hi

 def reverseEquiv : Fock α ≃ₗᵢ[ℂ] Fock α :=
  LinearIsometryEquiv.ofSurjective reverseIsometry (fun ξ =>
    ⟨reverseOperator ξ,reverseOperator_involutive ξ⟩)

@[simp] theorem reverseEquiv_apply (ξ : Fock α) : reverseEquiv ξ=reverseOperator ξ := rfl
@[simp] theorem reverseEquiv_symm_apply (ξ : Fock α) : reverseEquiv.symm ξ=reverseOperator ξ := by
  apply reverseEquiv.injective
  rw [LinearIsometryEquiv.apply_symm_apply,reverseEquiv_apply,reverseOperator_involutive]

 theorem reverse_conj_creation (a : α) :
    reverseEquiv.conjStarAlgEquiv (creation a)=rightCreation a := by
  apply operator_basis_ext (α := List α)
  intro w
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,reverseEquiv_symm_apply,
    reverseEquiv_apply,reverseOperator_single,creation_single,rightCreation_single,
    List.reverse_cons,List.reverse_reverse]

 theorem reverse_conj_semicircular (a : α) :
    reverseEquiv.conjStarAlgEquiv (semicircular a)=rightSemicircular a := by
  simp only [semicircular,map_add,map_star,reverse_conj_creation,rightSemicircular]

 theorem wick_mem_any (A : StarSubalgebra ℂ (Operator α))
    (h : ∀ a, semicircular a ∈ A) (w : List α) : wick w ∈ A := by
  suffices ∀ w : List α, wick w ∈ A ∧ ∀ a, wick (a::w) ∈ A from (this w).1
  intro w
  induction w with
  | nil =>
    refine ⟨by rw [wick_nil]; exact A.one_mem,?_⟩
    intro a
    simpa only [wick_semicircular_cons,wick_nil,mul_one,sub_zero] using h a
  | cons b w ih =>
    refine ⟨ih.2 b,?_⟩
    intro a
    rw [wick_semicircular_cons]
    refine A.sub_mem (A.mul_mem (h a) (ih.2 b)) ?_
    change (if a=b then wick w else 0) ∈ A
    by_cases hab : a=b
    · rw [ite_eq_left hab]; exact ih.1
    · rw [ite_eq_right hab]; exact A.zero_mem

 def gaussianCommutant (α : Type u_3) [DecidableEq α] : StarSubalgebra ℂ (Operator α) :=
  StarSubalgebra.centralizer ℂ (Set.range (semicircular : α → Operator α))

 def gaussianAlgebra (α : Type u_4) [DecidableEq α] : StarSubalgebra ℂ (Operator α) :=
  StarSubalgebra.centralizer ℂ (gaussianCommutant α : Set (Operator α))

 theorem rightSemicircular_mem (b : α) : rightSemicircular b ∈ gaussianCommutant α := by
  rw [gaussianCommutant,StarSubalgebra.mem_centralizer_iff]
  rintro _ ⟨a,rfl⟩
  have hs := (semicircular_selfAdjoint a).star_eq
  refine ⟨(semicircular_rightSemicircular a b).eq,?_⟩
  rw [hs]
  exact (semicircular_rightSemicircular a b).eq

 def rightWick (w : List α) : Operator α := reverseEquiv.conjStarAlgEquiv (wick w)

 theorem rightWick_mem (w : List α) : rightWick w ∈ gaussianCommutant α := by
  apply wick_mem_any ((gaussianCommutant α).comap reverseEquiv.conjStarAlgEquiv.toStarAlgHom)
  intro a
  change reverseEquiv.conjStarAlgEquiv (semicircular a) ∈ gaussianCommutant α
  rw [reverse_conj_semicircular]
  exact rightSemicircular_mem a

@[simp] theorem rightWick_vacuum (w : List α) : rightWick w vacuum=lp.single 2 w.reverse 1 := by
  simp only [rightWick,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    reverseEquiv_symm_apply,reverseEquiv_apply]
  have hv : reverseOperator (vacuum : Fock α)=vacuum := reverseOperator_single [] 1
  rw [hv,wick_vacuum,reverseOperator_single]

 theorem gaussian_commute_rightWick (T : gaussianAlgebra α) (w : List α) :
    rightWick w*(T : Operator α)=(T : Operator α)*rightWick w :=
  ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _ (rightWick_mem w)).1

end
open GaussianRecognition CyclicSpectral CircularRotation
open Filter Topology
open scoped ENNReal
variable {α : Type u_5} [DecidableEq α]

theorem fock_closed_total (K : Submodule ℂ (Fock α)) (hK : IsClosed (K:Set (Fock α)))
    (hδ : ∀ w : List α,lp.single 2 w (1:ℂ)∈K) : K=⊤ := by
  apply top_unique
  intro ξ _
  apply hK.mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) ξ)
  filter_upwards [] with s
  apply K.sum_mem
  intro w _
  have he : lp.single (E := fun _ : List α => ℂ) 2 w (ξ w)=(ξ w) • lp.single 2 w 1 := by
    ext v
    simp [lp.single_apply,Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (hδ w)

theorem gaussian_commutant_total :
    (Submodule.span ℂ (Set.range (fun B : StarSubalgebra.centralizer ℂ
      (gaussianAlgebra α:Set (Operator α)) => (B:Operator α) vacuum))).topologicalClosure=⊤ := by
  apply fock_closed_total _ (Submodule.isClosed_topologicalClosure _)
  intro w
  have hB : rightWick w.reverse∈StarSubalgebra.centralizer ℂ (gaussianAlgebra α:Set (Operator α)) :=
    WeightedFock.centralizer_bicommutant (Set.range (semicircular : α → Operator α))
      ⟨_,rightWick_mem w.reverse⟩
  apply Submodule.le_topologicalClosure _
  have hh : rightWick w.reverse vacuum=lp.single 2 w 1 := by
    rw [rightWick_vacuum,List.reverse_reverse]
  rw [← hh]
  exact Submodule.subset_span ⟨⟨rightWick w.reverse,hB⟩,rfl⟩

theorem semicircular_mem_uniform_bicommutant (i : α) :
    semicircular i∈Bicommutant.algebra (Set.range (scalarUniform i)) := by
  let : Nontrivial (Fock α) := by
    apply nontrivial_of_ne (vacuum : Fock α) 0
    intro h
    have hh := congrArg (fun ξ : Fock α => ξ []) h
    simp [vacuum,lp.single_apply] at hh
  let := semicircular_spectral_noAtoms i
  have h := operator_mem_haar_bicommutant (semicircular i) (semicircular_selfAdjoint i) vacuum
    (gaussianAlgebra α) (Set.isClosed_centralizer _)
    (Bicommutant.subset (Set.range (semicircular : α → Operator α)) (Set.mem_range_self i))
    gaussian_commutant_total
  apply Bicommutant.mono _ (Set.range (scalarUniform i)) ?_ h
  intro T hT
  rcases hT with rfl
  exact ⟨uniformPhase,(uniformHom_phase (semicircular i) (semicircular_selfAdjoint i) vacuum).symm⟩

def scalarFlip (i : WeightedCornerIndex.Index × ℕ) : WeightedCornerIndex.Index × ℕ := (flip i.1,i.2)

theorem scalarCoeff_mem_gaussian (a : UniformAlgebra) :
    scalarSystem.coeff a∈gaussianAlgebra ScalarIndex := by
  let := semicircular_spectral_noAtoms (none:ScalarIndex)
  exact uniformHom_mem (semicircular (none:ScalarIndex)) (semicircular_selfAdjoint none) vacuum
    (gaussianAlgebra ScalarIndex) (Set.isClosed_centralizer _)
    (Bicommutant.subset _ (Set.mem_range_self none)) a

theorem scalarGenerator_mem_gaussian (i : WeightedCornerIndex.Index × ℕ) :
    scalarSystem.generator scalarFlip i∈gaussianAlgebra ScalarIndex := by
  exact (rotate_generation (fun j => creation (some (j,i.2))) (gaussianAlgebra ScalarIndex)).mp
    (fun j => Bicommutant.subset (Set.range (semicircular : ScalarIndex → Operator ScalarIndex))
      (Set.mem_range_self (some (j,i.2)))) i.1

theorem scalar_semicircular_mem_generated (i : ScalarIndex) :
    semicircular i∈scalarSystem.generated scalarFlip := by
  cases i with
  | none =>
    exact Bicommutant.mono _ _ (Set.subset_union_left)
      (semicircular_mem_uniform_bicommutant (none:ScalarIndex))
  | some i =>
    exact (rotate_generation (fun j => creation (some (j,i.2)))
      (scalarSystem.generated scalarFlip)).mpr
      (fun j => Bicommutant.subset _ (Set.mem_union_right _ (Set.mem_range_self (j,i.2)))) i.1

theorem scalar_generated_eq_gaussian : scalarSystem.generated scalarFlip=gaussianAlgebra ScalarIndex := by
  apply le_antisymm
  · apply Bicommutant.generated_le
    rintro T (⟨a,rfl⟩ | ⟨i,rfl⟩)
    · exact scalarCoeff_mem_gaussian a
    · exact scalarGenerator_mem_gaussian i
  · apply Bicommutant.generated_le
    rintro T ⟨i,rfl⟩
    exact scalar_semicircular_mem_generated i

theorem scalarSystem_total :
    (Submodule.span ℂ (Set.range scalarSystem.family)).topologicalClosure=⊤ := by
  apply fock_closed_total _ (Submodule.isClosed_topologicalClosure _)
  intro w
  have hw : wick w∈scalarSystem.generated scalarFlip := by
    rw [scalar_generated_eq_gaussian]
    exact wick_mem_any _ (fun i => Bicommutant.subset _ (Set.mem_range_self i)) w
  have h := scalarSystem.normalHull_bicommutant scalarFlip (wick w) hw
  change lp.single 2 w 1∈scalarSystem.normalHull
  simpa only [show scalarSystem.root=(vacuum : Fock ScalarIndex) from rfl,wick_vacuum] using h
end FreeGroupFactorMain.FreeFock

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification WeightedCornerIndex GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

def representedAmbient : StarSubalgebra ℂ (PRange ℕ →L[ℂ] PRange ℕ) :=
  (pAmbient u v).comap (pRepresentation (ι := ℕ)).symm.toStarAlgHom

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace FreeGroupFactorMain.GaussianRecognition.System
variable {A : Type u_1} {E : Type u_2} {I : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

end FreeGroupFactorMain.GaussianRecognition.System

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification GaussianRecognition
variable {ι : Type u_4} [DecidableEq ι]

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

end

open FreeFock Amplification GaussianRecognition
variable {ι : Type u_5} [DecidableEq ι]

variable (u v : ℝ)

def rightEdge : Operator ℕ := reverseConj (edgePolar u v (0:ℕ))

def pRightEdge : PRange ℕ →L[ℂ] PRange ℕ := pRepresentation (pSandwich (rightEdge u v))

variable (hv : 0<v) (hvu : v<u)

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

def vertexOld (u v : ℝ) (r : Bool) : oldAlgebra u v (∅ : Set ι) :=
  ⟨vertex r,by cases r;exact sub_mem (one_mem _) (P_mem_old u v ∅);exact P_mem_old u v ∅⟩

variable (u v : ℝ) (i : ι)

end

section
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

end

section
open FreeFock GaussianOrthogonal
variable {ι : Type u_3} [DecidableEq ι]

end

open FreeFock WeightedCornerIndex

end FreeGroupFactorMain.WeightedFock

end

end OAI
end


