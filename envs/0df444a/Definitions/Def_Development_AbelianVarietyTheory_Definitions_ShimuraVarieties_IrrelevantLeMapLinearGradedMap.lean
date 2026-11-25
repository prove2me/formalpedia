-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
-- name    : Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T08:40:44.052314+00:00
-- url     : https://prove2.me/theorems/70e3cdf5-74b0-5b7c-9963-b9ae00c99557
-- title:
--   Irrelevant Le Map Linear Graded Map
-- statement:
--   Definitions and structural lemmas for Irrelevant Le Map Linear Graded Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_AddLaw_map_diagXYZ
import Theorems.Thm_GlobalTheory_ProjPoint_ofHom_map
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_some
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_zero
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_zeroOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_zeroOver
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_some
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_zero
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_zeroOver


set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open HomogeneousIdeal
universe u
noncomputable section
namespace GlobalTheory
section SpecOver
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
def specOverMap (g : A →ₐ[R] B) : specOver R B ⟶ specOver R A :=
  Over.homMk (Spec.map (CommRingCat.ofHom (g : A →+* B))) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, g.comp_algebraMap])
@[simp] theorem specOverMap_left (g : A →ₐ[R] B) :
    (specOverMap g).left = Spec.map (CommRingCat.ofHom (g : A →+* B)) := rfl
end SpecOver
namespace WeierstrassCurve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
@[reassoc]
theorem specOverMap_ptOver {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (g : A →ₐ[R] B) (P : Fin 3 → A) (h : IsUnimodularSol (W.baseChange A) P) :
    specOverMap g ≫ ptOver W P h = ptOver W (g ∘ P) (h.baseChange g) :=
  Over.OverMorphism.ext (SpecMap_pt W P h g)
section Linear
variable {W' : WeierstrassCurve R} (L : Fin 3 → HomRing W') (hL : ∀ i, L i ∈ grading W' 1)
  (h : (W.baseChange (HomRing W')).toProjective.Equation L)
def linearGradedMap : grading W →+*ᵍ grading W' where
  toRingHom := evalHom W (algebraMap R (HomRing W')) L h
  map_mem := by
    rintro n _ ⟨p, hp, rfl⟩
    change MvPolynomial.eval₂ _ _ p ∈ _
    rw [MvPolynomial.eval₂_eq]
    refine sum_mem fun d hd => ?_
    rw [← Algebra.smul_def, MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hd]
    refine Submodule.smul_mem _ _ (SetLike.prod_mem_graded _ _ _ fun i _ => ?_)
    simpa using SetLike.pow_mem_graded (d i) (hL i)
variable (hs : ∀ i, coord W' i ∈ Ideal.span (Set.range L))
include hs in

theorem irrelevant_le_map_linearGradedMap :
    irrelevant (grading W') ≤ (irrelevant (grading W)).map (linearGradedMap W L hL h) := by
  rw [← toIdeal_le_toIdeal_iff, irrelevant_eq_span_coord, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  refine (Ideal.span_le.mpr ?_ : Ideal.span (Set.range L) ≤ _) (hs i)
  rintro _ ⟨j, rfl⟩
  rw [← evalHom_coord W (algebraMap R (HomRing W')) L h j]
  exact Ideal.mem_map_of_mem (linearGradedMap W L hL h)
    (mem_irrelevant_of_mem _ one_pos (coord_mem W j))
def linearHom : scheme W' ⟶ scheme W :=
  Proj.map (linearGradedMap W L hL h) (irrelevant_le_map_linearGradedMap W L hL h hs)
variable {A : Type u} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
  (hP : IsUnimodularSol (W'.map ρ) P)
include h hs in

theorem isUnimodularSol_linear :
    IsUnimodularSol (W.map ρ) (evalHom W' ρ P hP.equation ∘ L) := by
  constructor
  · have e : (evalHom W' ρ P hP.equation).comp (algebraMap R (HomRing W')) = ρ :=
      RingHom.ext (evalHom_algebraMap W' ρ P hP.equation)
    have := h.map (evalHom W' ρ P hP.equation)
    change (W.map ((evalHom W' ρ P hP.equation).comp
      (algebraMap R (HomRing W')))).toProjective.Equation _ at this
    rwa [e] at this
  · rw [Set.range_comp, ← Ideal.map_span, _root_.eq_top_iff, ← hP.span_eq_top, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [← evalHom_coord W' ρ P hP.equation i]
    exact Ideal.mem_map_of_mem _ (hs i)
@[reassoc]
theorem ptHom_linearHom : ptHom W' ρ P hP ≫ linearHom W L hL h hs =
    ptHom W ρ (evalHom W' ρ P hP.equation ∘ L) (isUnimodularSol_linear W L h hs ρ P hP) := by
  refine (ProjPoint.ofHom_map (linearGradedMap W L hL h)
    (irrelevant_le_map_linearGradedMap W L hL h hs) _ (map_irrelevant_evalHom W' hP)).trans ?_
  have : (evalHom W' ρ P hP.equation).comp (linearGradedMap W L hL h).toRingHom =
      evalHom W ρ _ (isUnimodularSol_linear W L h hs ρ P hP).equation :=
    homRing_hom_ext W
      (fun r => ((congrArg (evalHom W' ρ P hP.equation)
        (evalHom_algebraMap W (algebraMap R (HomRing W')) L h r)).trans
          (evalHom_algebraMap ..)).trans (evalHom_algebraMap ..).symm)
      (fun i => (congrArg (evalHom W' ρ P hP.equation)
        (evalHom_coord W (algebraMap R (HomRing W')) L h i)).trans (evalHom_coord W ρ
          (evalHom W' ρ P hP.equation ∘ L)
          (isUnimodularSol_linear W L h hs ρ P hP).equation i).symm)
  simp only [this]
  rfl
@[reassoc (attr := simp)]
theorem linearHom_toSpec : linearHom W L hL h hs ≫ toSpec W = toSpec W' := by
  apply scheme_hom_ext
  · rw [chartY, pt_toSpec, pt_eq_ptHom, ptHom_linearHom_assoc, ptHom_toSpec]
  · rw [chartZ, pt_toSpec, pt_eq_ptHom, ptHom_linearHom_assoc, ptHom_toSpec]
end Linear
section Neg
variable {A : Type*} [CommRing A]
theorem equation_neg {V : WeierstrassCurve A} {P : Fin 3 → A} (h : V.toProjective.Equation P) :
    V.toProjective.Equation (V.toProjective.neg P) := by
  rw [WeierstrassCurve.Projective.equation_iff] at h ⊢
  simp only [WeierstrassCurve.Projective.neg_X, WeierstrassCurve.Projective.neg_Y,
    WeierstrassCurve.Projective.neg_Z, WeierstrassCurve.Projective.negY]
  linear_combination h
theorem mem_span_neg (V : WeierstrassCurve A) (P : Fin 3 → A) (i : Fin 3) :
    P i ∈ Ideal.span (Set.range (V.toProjective.neg P)) := by
  have h : ∀ j, V.toProjective.neg P j ∈ Ideal.span (Set.range (V.toProjective.neg P)) :=
    fun j => Ideal.subset_span ⟨j, rfl⟩
  fin_cases i
  · exact h 0
  · have e : P 1 = -V.toProjective.neg P 1 - V.a₁ * V.toProjective.neg P 0
        - V.a₃ * V.toProjective.neg P 2 := by
      simp only [WeierstrassCurve.Projective.neg_X, WeierstrassCurve.Projective.neg_Y,
        WeierstrassCurve.Projective.neg_Z, WeierstrassCurve.Projective.negY]
      ring
    change P 1 ∈ _
    rw [e]
    exact sub_mem (sub_mem (neg_mem (h 1)) (Ideal.mul_mem_left _ _ (h 0)))
      (Ideal.mul_mem_left _ _ (h 2))
  · exact h 2
theorem IsUnimodularSol.neg {V : WeierstrassCurve A} {P : Fin 3 → A} (h : IsUnimodularSol V P) :
    IsUnimodularSol V (V.toProjective.neg P) := by
  refine ⟨equation_neg h.equation, ?_⟩
  rw [_root_.eq_top_iff, ← h.span_eq_top, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact mem_span_neg V P i
theorem neg_coord_mem (i : Fin 3) :
    (W.baseChange (HomRing W)).toProjective.neg (coord W) i ∈ grading W 1 := by
  fin_cases i
  · exact coord_mem W 0
  · change -coord W 1 - algebraMap R _ W.a₁ * coord W 0 - algebraMap R _ W.a₃ * coord W 2 ∈ _
    rw [← Algebra.smul_def, ← Algebra.smul_def]
    exact sub_mem (sub_mem (neg_mem (coord_mem W 1)) (Submodule.smul_mem _ _ (coord_mem W 0)))
      (Submodule.smul_mem _ _ (coord_mem W 2))
  · exact coord_mem W 2
def negHom : scheme W ⟶ scheme W :=
  linearHom W _ (neg_coord_mem W) (equation_neg (equation_coord W)) (mem_span_neg _ _)
@[reassoc]
theorem ptHom_negHom {A : Type u} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) :
    ptHom W ρ P hP ≫ negHom W = ptHom W ρ ((W.map ρ).toProjective.neg P) hP.neg := by
  rw [negHom, ptHom_linearHom]
  refine ptHom_congr W _ _ _ rfl ?_ _
  ext i
  fin_cases i <;>
    simp [WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY,
      WeierstrassCurve.baseChange]
@[reassoc (attr := simp)]
theorem negHom_toSpec : negHom W ≫ toSpec W = toSpec W := linearHom_toSpec ..
def negOver : schemeOver W ⟶ schemeOver W := Over.homMk (negHom W) (negHom_toSpec W)
@[simp] theorem negOver_left : (negOver W).left = negHom W := rfl
@[reassoc]
theorem ptOver_negOver {A : Type u} [CommRing A] [Algebra R A] (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.baseChange A) P) :
    ptOver W P hP ≫ negOver W = ptOver W ((W.baseChange A).toProjective.neg P) hP.neg :=
  Over.OverMorphism.ext (ptHom_negHom W _ P hP)
@[reassoc]
theorem negHom_mapHom {R' : Type u} [CommRing R'] {W' : WeierstrassCurve R'} (f : R →+* R')
    (h : W.map f = W') : negHom W' ≫ mapHom W f h = mapHom W f h ≫ negHom W := by
  subst h
  apply scheme_hom_ext
  · rw [chartY, pt_eq_ptHom, ptHom_negHom_assoc, ptHom_mapHom, ptHom_mapHom_assoc, ptHom_negHom]
    rfl
  · rw [chartZ, pt_eq_ptHom, ptHom_negHom_assoc, ptHom_mapHom, ptHom_mapHom_assoc, ptHom_negHom]
    rfl
def zeroUnit : 𝟙_ (Over (Spec (.of R))) ⟶ schemeOver W := Over.homMk (zero W) (zero_toSpec W)
@[simp] theorem zeroUnit_left : (zeroUnit W).left = zero W := rfl
end Neg
section Sum
open AddLaw
variable {A B : Type*} [CommRing A] [CommRing B]
structure IsSumTriple (V : WeierstrassCurve A) (P Q T : Fin 3 → A) : Prop where

  add : Proportional T (V.toProjective.addXYZ P Q)

  diag : Proportional T (diagXYZ V.toProjective P Q)
variable {V : WeierstrassCurve A} {P Q T : Fin 3 → A}
theorem IsSumTriple.map (h : IsSumTriple V P Q T) (g : A →+* B) :
    IsSumTriple (V.map g) (g ∘ P) (g ∘ Q) (g ∘ T) := by
  constructor
  · have e : (V.map g).toProjective.addXYZ (g ∘ P) (g ∘ Q) = g ∘ V.toProjective.addXYZ P Q :=
      WeierstrassCurve.Projective.map_addXYZ ..
    rw [e]
    exact fun i j => by simpa using congrArg g (h.add i j)
  · have e : diagXYZ (V.map g).toProjective (g ∘ P) (g ∘ Q) = g ∘ diagXYZ V.toProjective P Q :=
      map_diagXYZ ..
    rw [e]
    exact fun i j => by simpa using congrArg g (h.diag i j)
theorem IsSumTriple.baseChange {R : Type*} [CommRing R] [Algebra R A] [Algebra R B]
    {W : WeierstrassCurve R} (h : IsSumTriple (W.baseChange A) P Q T) (g : A →ₐ[R] B) :
    IsSumTriple (W.baseChange B) (g ∘ P) (g ∘ Q) (g ∘ T) := by
  have := h.map (g : A →+* B)
  rwa [WeierstrassCurve.map_baseChange] at this
end Sum
section Reduced
variable [W.IsElliptic]
def fieldAdd (k : Type u) [Field k] [Algebra R k] (a b : specOver R k ⟶ schemeOver W) :
    specOver R k ⟶ schemeOver W :=
  projectivePointEquiv W k ((projectivePointEquiv W k).symm a + (projectivePointEquiv W k).symm b)
end Reduced
end WeierstrassCurve
end GlobalTheory


