-- Prove2me | Definitions.Def_FreeGroupFactorProof11
-- name    : FreeGroupFactorProof11
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T01:53:56.914567+00:00
-- url     : https://prove2.me/theorems/5c58c2fb-70c8-4d98-81b7-12c4e71f76b2
-- title:
--   Free group factors: supporting development, part 11
-- statement:
--   Part 11 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof10

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.FreeFock

section
open Filter Topology
open scoped ENNReal
variable {α : Type u_1} [DecidableEq α]

 theorem semicircular_eigen_root_zero (i : α) (z : ℂ) (ξ : Fock α)
    (hξ : semicircular i ξ=z • ξ) : ξ []=0 := by
  have he (n : ℕ) : inner ℂ (semicircular i (lp.single 2 (List.replicate n i) 1)) ξ=
      z*ξ (List.replicate n i) := by
    rw [← (semicircular_selfAdjoint i).star_eq,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left,hξ,inner_smul_right]
    simp [lp.inner_single_left,RCLike.inner_apply]
  have hb : (1:ℂ)*ξ (List.replicate 1 i)=z*ξ (List.replicate 0 i) := by
    have h := he 0
    rw [List.replicate_zero,semicircular_repeat_zero] at h
    simpa only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one,one_mul,
      List.replicate_one,List.replicate_zero] using h
  have ht (n : ℕ) : (1:ℂ)*ξ (List.replicate (n+2) i)=
      z*ξ (List.replicate (n+1) i)-(1:ℂ)*ξ (List.replicate n i) := by
    have h := he (n+1)
    rw [semicircular_repeat_succ] at h
    simp only [inner_add_left,lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] at h
    linear_combination h
  exact JacobiNonatom.semicircular_eigenvector_zero 1 z one_ne_zero
    (fun n => ξ (List.replicate n i)) (repeat_coordinates_decay i ξ) hb ht 0

end

section
open MeasureTheory
variable {α : Type u_2} [DecidableEq α]

 theorem semicircular_spectral_noAtoms (i : α) :
    NullSingletonClass (CyclicSpectral.measure (semicircular i) (semicircular_selfAdjoint i) vacuum) := by
  apply CyclicSpectral.noAtoms
  intro r η hη
  have hc : semicircular i η=(r:ℂ) • η := by
    exact hη.trans (by
      apply Subtype.ext
      funext w
      change r • η w=(r:ℂ)*η w
      exact Complex.real_smul)
  have hz := semicircular_eigen_root_zero i (r:ℂ) η hc
  change (inner ℂ vacuum η).re=0
  simp only [vacuum,lp.inner_single_left,RCLike.inner_apply,map_one,mul_one,hz,Complex.zero_re]

end
section
open CyclicSpectral MeasureTheory
variable {α : Type u_3} [DecidableEq α]

instance scalarSpectral_probability (i : α) :
    IsProbabilityMeasure (measure (semicircular i) (semicircular_selfAdjoint i) (vacuum : Fock α)) :=
  probability _ _ _ (by simp [vacuum,lp.norm_single])

def scalarUniform (i : α) : UniformAlgebra →⋆ₐ[ℂ] Operator α := by
  letI := semicircular_spectral_noAtoms i
  exact uniformHom (semicircular i) (semicircular_selfAdjoint i) vacuum

theorem scalarUniform_state (i : α) (a : UniformAlgebra) :
    vacuumTrace (scalarUniform i a)=uniformState a := by
  let := semicircular_spectral_noAtoms i
  exact uniformHom_state _ _ _ a

theorem scalarUniform_mem (i : α) (a : UniformAlgebra) :
    scalarUniform i a∈(runAlgebra i).topologicalClosure := by
  let := semicircular_spectral_noAtoms i
  apply uniformHom_mem (semicircular i) (semicircular_selfAdjoint i) vacuum
    ((runAlgebra i).topologicalClosure) (StarSubalgebra.isClosed_topologicalClosure _) ?_ a
  apply StarSubalgebra.le_topologicalClosure
  change semicircular i∈runSpan i
  simpa [wick_semicircular_cons] using run_mem i 1

theorem scalarUniform_covariance {I : Type u_4} [DecidableEq I] (i j : I) (a : UniformAlgebra) :
    star (creation (some i))*scalarUniform (none : Option I) a*creation (some j)=
      if i=j then uniformState a • (1:Operator (Option I)) else 0 := by
  have h := closed_coarse_covariance (none : Option I) (some i) (some j)
    (by simp) (by simp) ⟨_,scalarUniform_mem none a⟩
  change _=vacuumTrace (scalarUniform (none:Option I) a) • (if some i=some j then 1 else 0) at h
  rw [scalarUniform_state] at h
  by_cases he : i=j
  · simpa only [he,ite_true] using h
  · simpa only [Option.some.injEq,ite_eq_right he,
      smul_zero (M := ℂ) (A := Operator (Option I))] using h

theorem scalarUniform_annihilation {I : Type u_5} [DecidableEq I] (i : I) (a : UniformAlgebra) :
    star (creation (some i)) (scalarUniform (none : Option I) a vacuum)=0 :=
  closed_coefficient_annihilation none (some i) (by simp) ⟨_,scalarUniform_mem none a⟩
end

open CyclicSpectral GaussianRecognition CircularRotation WeightedCornerIndex

abbrev ScalarIndex := Option (WeightedCornerIndex.Index × ℕ)
instance scalarIndexDecidableEq : DecidableEq ScalarIndex :=
  fun a b => @Option.instDecidableEq (WeightedCornerIndex.Index × ℕ)
    (fun x y => instDecidableEqProd x y) a b

def rotatedCreation (i : WeightedCornerIndex.Index × ℕ) : Operator ScalarIndex :=
  rotate (fun j => creation (some (j,i.2))) i.1

theorem rotatedCreation_covariance (i j : WeightedCornerIndex.Index × ℕ) (a : UniformAlgebra) :
    star (rotatedCreation i)*scalarUniform (none : ScalarIndex) a*rotatedCreation j=
      if i=j then uniformState a • (1:Operator ScalarIndex) else 0 := by
  rcases i with ⟨i,n⟩
  rcases j with ⟨j,m⟩
  by_cases hnm : n=m
  · subst m
    have hh := rotate_covariance (fun i : WeightedCornerIndex.Index => creation (some (i,n)))
      (scalarUniform (none : ScalarIndex) a) (uniformState a • (1:Operator ScalarIndex))
      (fun i j => by simpa only [Prod.mk.injEq,and_true] using scalarUniform_covariance (i,n) (j,n) a) i j
    simpa only [rotatedCreation,Prod.mk.injEq,and_true] using hh
  · have he (i j : WeightedCornerIndex.Index) :
        star (creation (some (i,n)))*scalarUniform (none : ScalarIndex) a*creation (some (j,m))=0 := by
      simpa only [Prod.mk.injEq,hnm,and_false,ite_false] using scalarUniform_covariance (i,n) (j,m) a
    simp only [Prod.mk.injEq,hnm,and_false,ite_false]
    rcases i with i | ⟨i,b⟩ <;> rcases j with j | ⟨j,c⟩
    · exact he (.inl i) (.inl j)
    · cases c <;> simp [rotatedCreation,rotate,plus,minus,mul_add,mul_sub,he]
    · cases b <;> simp only [rotatedCreation,rotate,plus,minus,star_smul,
        star_add (R := Operator ScalarIndex),star_sub (R := Operator ScalarIndex),add_mul,
        sub_mul,smul_mul_assoc (α := ℂ) (β := Operator ScalarIndex),he,
        smul_zero (M := ℂ) (A := Operator ScalarIndex),add_zero,sub_zero]
    · cases b <;> cases c <;>
        simp only [rotatedCreation,rotate,plus,minus,star_smul,
          star_add (R := Operator ScalarIndex),star_sub (R := Operator ScalarIndex),add_mul,
          sub_mul,mul_add,mul_sub,smul_mul_assoc (α := ℂ) (β := Operator ScalarIndex),
          mul_smul_comm (α := ℂ) (β := Operator ScalarIndex),he,
          smul_zero (M := ℂ) (A := Operator ScalarIndex),add_zero,sub_zero]

theorem rotatedCreation_annihilation (i : WeightedCornerIndex.Index × ℕ) (a : UniformAlgebra) :
    star (rotatedCreation i) (scalarUniform (none : ScalarIndex) a vacuum)=0 := by
  rcases i with ⟨i,n⟩
  rcases i with i | ⟨i,b⟩
  · exact scalarUniform_annihilation (I := WeightedCornerIndex.Index × ℕ) (.inl i,n) a
  · have hf := scalarUniform_annihilation (I := WeightedCornerIndex.Index × ℕ) (.inr (i,false),n) a
    have ht := scalarUniform_annihilation (I := WeightedCornerIndex.Index × ℕ) (.inr (i,true),n) a
    cases b <;> simp only [rotatedCreation,rotate,plus,minus,star_smul,
      star_add (R := Operator ScalarIndex),star_sub (R := Operator ScalarIndex),
      add_apply,sub_apply,smul_apply,hf,ht,smul_zero,add_zero,sub_zero]

def scalarSystem : GaussianRecognition.System UniformAlgebra (Fock ScalarIndex)
    (WeightedCornerIndex.Index × ℕ) uniformCovariance where
  coeff := scalarUniform none
  root := vacuum
  create := rotatedCreation
  contract i j a := by
    rw [rotatedCreation_covariance]
    by_cases h : i=j
    · simp only [uniformCovariance,h,ite_true,map_smul,map_one]
    · simp only [uniformCovariance,ite_eq_right h,map_zero]
  annihilate := rotatedCreation_annihilation

end FreeGroupFactorMain.FreeFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace FreeGroupFactorMain.GaussianRecognition
section Algebraic
variable {A : Type u_1} {B : Type u_2} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]

theorem centralizer_transport (Φ : A ≃⋆ₐ[ℂ] B) (s : Set A) (T : A) :
    Φ T ∈ StarSubalgebra.centralizer ℂ (Φ '' s) ↔ T ∈ StarSubalgebra.centralizer ℂ s := by
  rw [StarSubalgebra.mem_centralizer_iff,StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h g hg
    have hh := h (Φ g) ⟨g,hg,rfl⟩
    constructor
    · apply Φ.injective
      change Φ (g*T)=Φ (T*g)
      simpa only [map_mul] using hh.1
    · apply Φ.injective
      change Φ (star g*T)=Φ (T*star g)
      simpa only [map_mul,map_star] using hh.2
  · rintro h _ ⟨g,hg,rfl⟩
    exact ⟨by simpa only [map_mul] using congrArg Φ (h g hg).1,
      by simpa only [map_mul,map_star] using congrArg Φ (h g hg).2⟩

theorem centralizer_image (Φ : A ≃⋆ₐ[ℂ] B) (s : Set A) :
    (StarSubalgebra.centralizer ℂ (Φ '' s) : Set B)=
      Φ '' (StarSubalgebra.centralizer ℂ s : Set A) := by
  ext T
  constructor
  · intro h
    refine ⟨Φ.symm T,?_,Φ.apply_symm_apply T⟩
    apply (centralizer_transport Φ s (Φ.symm T)).mp
    rw [Φ.apply_symm_apply]
    exact h
  · rintro ⟨T,h,rfl⟩
    exact (centralizer_transport Φ s T).mpr h

theorem bicommutant_transport (Φ : A ≃⋆ₐ[ℂ] B) (s : Set A) (T : A) :
    Φ T ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (Φ '' s) : Set B) ↔
    T ∈ StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set A) := by
  rw [centralizer_image,centralizer_transport]
end Algebraic

variable {E : Type u_3} {F : Type u_4}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

@[instance_reducible] def ultraweak (E : Type u_5) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : TopologicalSpace (Operator E) :=
  ⨅ (ξ : lp (fun _ : ℕ => E) 2) (η : lp (fun _ : ℕ => E) 2),
    TopologicalSpace.induced (fun T : Operator E => ∑' k : ℕ, inner ℂ (η k) (T (ξ k))) inferInstance

namespace System
variable {A : Type u_6} {I : Type u_7} [Ring A] [StarRing A] [Algebra ℂ A]
variable {covariance : I → I → A → A}
variable (X : System A E I covariance) (Y : System A F I covariance)
variable
  (hstate : ∀ a,inner ℂ Y.root (Y.coeff a Y.root)=inner ℂ X.root (X.coeff a X.root))
  (hX : (Submodule.span ℂ (Set.range X.family)).topologicalClosure=⊤)
  (hY : (Submodule.span ℂ (Set.range Y.family)).topologicalClosure=⊤)

def generators (σ : I → I) : Set (Operator E) := Set.range X.coeff ∪ Set.range (X.generator σ)
def generated (σ : I → I) : StarSubalgebra ℂ (Operator E) :=
  StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ (X.generators σ) : Set (Operator E))

@[instance_reducible] def generatedTopology (σ : I → I) : TopologicalSpace (X.generated σ) :=
  TopologicalSpace.induced (fun T : X.generated σ => (T : Operator E)) (ultraweak E)

theorem spatial_generators (σ : I → I) :
    (X.spatial Y hstate hX hY).conjStarAlgEquiv '' X.generators σ=Y.generators σ := by
  rw [generators, generators, Set.image_union]
  congr 1
  · ext T
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨a,(spatial_coeff X Y hstate hX hY a).symm⟩
    · rintro ⟨a,rfl⟩
      exact ⟨X.coeff a,⟨a,rfl⟩,spatial_coeff X Y hstate hX hY a⟩
  · ext T
    constructor
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i,(spatial_generator X Y hstate hX hY σ i).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨X.generator σ i,⟨i,rfl⟩,spatial_generator X Y hstate hX hY σ i⟩

theorem spatial_generated (σ : I → I) (T : Operator E) :
    (X.spatial Y hstate hX hY).conjStarAlgEquiv T ∈ Y.generated σ ↔ T ∈ X.generated σ := by
  have hh := bicommutant_transport (X.spatial Y hstate hX hY).conjStarAlgEquiv
    (X.generators σ) T
  rw [spatial_generators X Y hstate hX hY σ] at hh
  exact hh

def generatedIso (σ : I → I) : X.generated σ ≃⋆ₐ[ℂ] Y.generated σ where
  toFun T := ⟨(X.spatial Y hstate hX hY).conjStarAlgEquiv T,
    (spatial_generated X Y hstate hX hY σ T).mpr T.property⟩
  invFun T := ⟨(X.spatial Y hstate hX hY).conjStarAlgEquiv.symm T,
    (spatial_generated X Y hstate hX hY σ _).mp (by
      rw [StarAlgEquiv.apply_symm_apply]; exact T.property)⟩
  left_inv T := Subtype.ext (StarAlgEquiv.symm_apply_apply
    (X.spatial Y hstate hX hY).conjStarAlgEquiv (T : Operator E))
  right_inv T := Subtype.ext (StarAlgEquiv.apply_symm_apply
    (X.spatial Y hstate hX hY).conjStarAlgEquiv (T : Operator F))
  map_mul' T U := Subtype.ext (map_mul _ (T : Operator E) (U : Operator E))
  map_add' T U := Subtype.ext (map_add _ (T : Operator E) (U : Operator E))
  map_smul' c T := Subtype.ext (map_smul _ c (T : Operator E))
  map_star' T := Subtype.ext (map_star _ (T : Operator E))

end System
end FreeGroupFactorMain.GaussianRecognition

namespace FreeGroupFactorMain.GaussianRecognition.System
variable {A : Type u_8} {E : Type u_9} {I : Type u_10} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

def normalSpan : Submodule ℂ E := Submodule.span ℂ (Set.range X.family)
def normalHull : Submodule ℂ E := X.normalSpan.topologicalClosure

instance normalHull_complete : CompleteSpace X.normalHull := by
  unfold normalHull
  infer_instance

theorem normal_mem (a : A) (w : List (I×A)) : X.normal a w∈X.normalSpan :=
  Submodule.subset_span ⟨(a,w),rfl⟩

theorem normalSpan_coeff (a : A) {ξ : E} (hξ : ξ∈X.normalSpan) : X.coeff a ξ∈X.normalSpan := by
  induction hξ using Submodule.span_induction with
  | mem ξ hξ => obtain ⟨⟨b,w⟩,rfl⟩ := hξ; exact (X.coeff_normal a b w) ▸ X.normal_mem (a*b) w
  | zero => simpa only [map_zero] using X.normalSpan.zero_mem
  | add ξ η _ _ hξ hη => simpa only [map_add] using X.normalSpan.add_mem hξ hη
  | smul c ξ _ hξ => simpa only [map_smul] using X.normalSpan.smul_mem c hξ

theorem normalSpan_create (i : I) {ξ : E} (hξ : ξ∈X.normalSpan) : X.create i ξ∈X.normalSpan := by
  induction hξ using Submodule.span_induction with
  | mem ξ hξ => obtain ⟨⟨a,w⟩,rfl⟩ := hξ; exact (X.create_normal i a w) ▸ X.normal_mem 1 ((i,a)::w)
  | zero => simpa only [map_zero] using X.normalSpan.zero_mem
  | add ξ η _ _ hξ hη => simpa only [map_add] using X.normalSpan.add_mem hξ hη
  | smul c ξ _ hξ => simpa only [map_smul] using X.normalSpan.smul_mem c hξ

theorem normalSpan_annihilate (i : I) {ξ : E} (hξ : ξ∈X.normalSpan) : star (X.create i) ξ∈X.normalSpan := by
  induction hξ using Submodule.span_induction with
  | mem ξ hξ =>
    obtain ⟨⟨a,w⟩,rfl⟩ := hξ
    change star (X.create i) (X.normal a w)∈X.normalSpan
    cases w with
    | nil => rw [X.annihilate_normal_nil]; exact X.normalSpan.zero_mem
    | cons q w => rcases q with ⟨j,b⟩; rw [X.annihilate_normal_cons]; exact X.normal_mem _ _
  | zero => simpa only [map_zero] using X.normalSpan.zero_mem
  | add ξ η _ _ hξ hη => simpa only [map_add] using X.normalSpan.add_mem hξ hη
  | smul c ξ _ hξ => simpa only [map_smul] using X.normalSpan.smul_mem c hξ

end FreeGroupFactorMain.GaussianRecognition.System

end

end OAI
end


