-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_isOpenImmersion_isPullback_of_glue_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/af91c583-e79d-598b-a045-f62cab9c32cc

import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isPullback_of_glue_cocycle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlueCocycleAux

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {ι : Type u} (t : ι → ι → (U ≅ U))

private noncomputable def tt' (i k : ι) : pullback j j ⟶ pullback j j :=
  pullback.fst j j ≫ (t i k).hom ≫ inv (pullback.fst j j)

@[reassoc (attr := simp)]
private lemma tt'_fst (i k : ι) : tt' j t i k ≫ pullback.fst j j = pullback.fst j j ≫ (t i k).hom := by
  simp [tt']

@[reassoc (attr := simp)]
private lemma tt'_snd (i k : ι) : tt' j t i k ≫ pullback.snd j j = pullback.fst j j ≫ (t i k).hom := by
  rw [← fst_eq_snd_of_mono_eq]; simp [tt']

private lemma t_hom_inv (ht_refl : ∀ i, t i i = Iso.refl U)
    (ht_trans : ∀ i k l, (t i k).hom ≫ (t k l).hom = (t i l).hom) (i k : ι) :
    (t i k).hom ≫ (t k i).hom = 𝟙 U := by
  rw [ht_trans, ht_refl]; rfl

private lemma tt'_cocycle (ht_refl : ∀ i, t i i = Iso.refl U)
    (ht_trans : ∀ i k l, (t i k).hom ≫ (t k l).hom = (t i l).hom) (i k l : ι) :
    tt' j t i k ≫ tt' j t k l ≫ tt' j t l i = 𝟙 _ := by
  simp only [tt', Category.assoc, IsIso.inv_hom_id_assoc]
  rw [reassoc_of% (ht_trans i k l), reassoc_of% (ht_trans i l i), ht_refl]
  simp

variable (ht_refl : ∀ i, t i i = Iso.refl U)
    (ht_trans : ∀ i k l, (t i k).hom ≫ (t k l).hom = (t i l).hom)

private noncomputable def glueData' : CategoryTheory.GlueData' Scheme.{u} where
  J := ι
  U := fun _ => X
  V := fun _ _ _ => U
  f := fun _ _ _ => j
  t := fun i k _ => (t i k).hom
  t' := fun i k l _ _ _ => tt' j t i k
  t_fac := fun i k l _ _ _ => tt'_snd j t i k
  t_inv := fun i k _ => t_hom_inv t ht_refl ht_trans i k
  cocycle := fun i k l _ _ _ => tt'_cocycle j t ht_refl ht_trans i k l

private noncomputable def glueData : Scheme.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (glueData' j t ht_refl ht_trans)
  f_open := by
    intro i k
    dsimp [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', glueData']
    split_ifs <;> infer_instance

private noncomputable def chart (i : ι) : X ⟶ (glueData j t ht_refl ht_trans).glued :=
  (glueData j t ht_refl ht_trans).ι i

private lemma isOpenImmersion_chart (i : ι) : IsOpenImmersion (chart j t ht_refl ht_trans i) :=
  inferInstanceAs <| IsOpenImmersion ((glueData j t ht_refl ht_trans).ι i)

private lemma iUnion_range_chart :
    (⋃ i, Set.range (chart j t ht_refl ht_trans i).base) = Set.univ := by
  refine Set.iUnion_eq_univ_iff.mpr fun x => ?_
  obtain ⟨i, y, hy⟩ := (glueData j t ht_refl ht_trans).ι_jointly_surjective x
  exact ⟨i, y, hy⟩

private lemma compat {S : Scheme.{u}} (f : X ⟶ S) (ht_over : ∀ i k, (t i k).hom ≫ j ≫ f = j ≫ f)
    (i k : (glueData j t ht_refl ht_trans).J) :
    (glueData j t ht_refl ht_trans).f i k ≫ f =
      ((glueData j t ht_refl ht_trans).t i k ≫ (glueData j t ht_refl ht_trans).f k i) ≫ f := by
  dsimp [glueData, CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', glueData']
  split_ifs with h
  · subst h; simp
  · rw [dif_neg (Ne.symm h)]
    simp [ht_over]

private noncomputable def toBase {S : Scheme.{u}} (f : X ⟶ S)
    (ht_over : ∀ i k, (t i k).hom ≫ j ≫ f = j ≫ f) :
    (glueData j t ht_refl ht_trans).glued ⟶ S :=
  Multicoequalizer.desc _ S (fun _ => f) (fun ik => compat j t ht_refl ht_trans f ht_over ik.1 ik.2)

@[reassoc (attr := simp)]
private lemma chart_toBase {S : Scheme.{u}} (f : X ⟶ S)
    (ht_over : ∀ i k, (t i k).hom ≫ j ≫ f = j ≫ f) (i : ι) :
    chart j t ht_refl ht_trans i ≫ toBase j t ht_refl ht_trans f ht_over = f :=
  Multicoequalizer.π_desc _ _ _ _ _

private lemma isPullback (i k : ι) (hik : i ≠ k) :
    IsPullback j ((t i k).hom ≫ j) (chart j t ht_refl ht_trans i) (chart j t ht_refl ht_trans k) := by
  have H := IsPullback.of_isLimit ((glueData j t ht_refl ht_trans).vPullbackConeIsLimit i k)
  have hV : (glueData j t ht_refl ht_trans).V (i, k) = U := dif_neg hik
  refine H.of_iso (eqToIso hV) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (Category.comp_id _) (Category.comp_id _)
  · dsimp [Scheme.GlueData.vPullbackCone, glueData, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', glueData']
    split_ifs with h
    · exact absurd h hik
    · simp
  · dsimp [Scheme.GlueData.vPullbackCone, glueData, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', glueData']
    split_ifs with h
    · exact absurd h hik
    · simp [dif_neg (Ne.symm h)]

end GlueCocycleAux

theorem solution
    {S X U : Scheme.{u}} (f : X ⟶ S) (j : U ⟶ X) [IsOpenImmersion j]
    {ι : Type u} (t : ι → ι → (U ≅ U))
    (ht_over : ∀ i k, (t i k).hom ≫ j ≫ f = j ≫ f)
    (ht_refl : ∀ i, t i i = Iso.refl U)
    (ht_trans : ∀ i k l, (t i k).hom ≫ (t k l).hom = (t i l).hom) :
    ∃ (N : Scheme.{u}) (gN : N ⟶ S) (e : ι → (X ⟶ N)),
      (∀ i, IsOpenImmersion (e i)) ∧
      (∀ i, e i ≫ gN = f) ∧
      (⋃ i, Set.range (e i).base) = Set.univ ∧
      (∀ i k, i ≠ k → IsPullback j ((t i k).hom ≫ j) (e i) (e k)) :=
  ⟨_, GlueCocycleAux.toBase j t ht_refl ht_trans f ht_over, GlueCocycleAux.chart j t ht_refl ht_trans,
    GlueCocycleAux.isOpenImmersion_chart j t ht_refl ht_trans, GlueCocycleAux.chart_toBase j t ht_refl ht_trans f ht_over,
    GlueCocycleAux.iUnion_range_chart j t ht_refl ht_trans,
    GlueCocycleAux.isPullback j t ht_refl ht_trans⟩

end S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isPullback_of_glue_cocycle
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isPullback_of_glue_cocycle (solution)
