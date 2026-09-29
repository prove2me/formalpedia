-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_iso_comp_eq_of_isOpenImmersion_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1b9b2714-3ae1-52eb-b402-4946b30f6dc8

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk
import Theorems.Thm_AlgebraicGeometry_valuationRing_stalk_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_irreducibleSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace ProperCurveExtension

variable {K : Type u} [Field K]

private theorem _root_.ProperCurveExtension.existence {Y S : Scheme.{u}} (g : Y ⟶ S) [IsProper g] :
    ValuativeCriterion.Existence g := by
  have h : IsProper g := inferInstance
  rw [IsProper.eq_valuativeCriterion] at h
  exact h.1.1.1.existence

p2m_export "ProperCurveExtension" "existence"

theorem isSeparated_of_isSeparated_over {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K))
    [IsSeparated g] : Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from g]; infer_instance⟩

theorem isDominant_ι {X : Scheme.{u}} [IrreducibleSpace X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : IsDominant U.ι :=
  ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact U.2.dense hU⟩

section Totalise

variable {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  [IsIntegral X] [IsProper sY] (hval : ∀ x : X, ValuationRing (X.presheaf.stalk x))
  (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX)

include hval hf in

theorem domain_eq_top : f.toRationalMap.domain = ⊤ :=
  top_unique fun x _ =>
    Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk sX sY (existence sY) f hf x
      (hval x)

def extend : X ⟶ Y :=
  haveI : Y.IsSeparated := isSeparated_of_isSeparated_over sY
  X.topIso.inv ≫ X.homOfLE (domain_eq_top sX sY hval f hf).ge ≫ f.toRationalMap.toPartialMap.hom

theorem ι_extend : f.domain.ι ≫ extend sX sY hval f hf = f.hom := by
  haveI : Y.IsSeparated := isSeparated_of_isSeparated_over sY
  have key := f.toPartialMap_toRationalMap_restrict
  rw [Scheme.PartialMap.restrict_hom] at key
  rw [← key, extend]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono (Scheme.Opens.ι _)]
  simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.toIso_inv_ι, Category.comp_id]
  exact (X.homOfLE_ι _).symm

theorem extend_over : extend sX sY hval f hf ≫ sY = sX := by
  haveI := isDominant_ι f.domain f.dense_domain.nonempty
  refine ext_of_isDominant f.domain.ι ?_
  rw [reassoc_of% (ι_extend sX sY hval f hf), hf]

end Totalise

end ProperCurveExtension

open ProperCurveExtension in
theorem solution {K : Type u} [Field K] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (c' : C' ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    [IsIntegral C'] [IsProper c'] [Smooth c']
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (j : (U : Scheme.{u}) ⟶ C') [IsOpenImmersion j] (hj : j ≫ c' = U.ι ≫ c) :
    ∃ e : C ≅ C', e.hom ≫ c' = c ∧ U.ι ≫ e.hom = j := by

  have hvalC : ∀ x : C, ValuationRing (C.presheaf.stalk x) :=
    valuationRing_stalk_of_smoothOfRelativeDimension_one c

  let V : C'.Opens := j.opensRange
  have hV : (V : Set C').Nonempty := ⟨j ⟨_, hU.some_mem⟩, Set.mem_range_self _⟩
  have hVc' : V.ι ≫ c' = j.isoOpensRange.inv ≫ U.ι ≫ c := by
    rw [← hj, Scheme.Hom.isoOpensRange_inv_comp_assoc]
  haveI : SmoothOfRelativeDimension 1 (V.ι ≫ c') := by
    rw [hVc']
    have h : SmoothOfRelativeDimension (0 + (0 + 1)) (j.isoOpensRange.inv ≫ U.ι ≫ c) :=
      inferInstance
    simpa using h
  haveI : SmoothOfRelativeDimension 1 c' := smoothOfRelativeDimension_of_irreducibleSpace 1 c' V hV
  have hvalC' : ∀ y : C', ValuationRing (C'.presheaf.stalk y) :=
    valuationRing_stalk_of_smoothOfRelativeDimension_one c'

  have hUd : Dense (U : Set C) := U.2.dense hU
  have hVd : Dense (V : Set C') := V.2.dense hV
  have hG : (j.isoOpensRange.inv ≫ U.ι) ≫ c = V.ι ≫ c' := by rw [Category.assoc, hVc']
  let fwd : C ⟶ C' := extend c c' hvalC ⟨U, hUd, j⟩ hj
  let bwd : C' ⟶ C := extend c' c hvalC' ⟨V, hVd, j.isoOpensRange.inv ≫ U.ι⟩ hG
  have h₁ : U.ι ≫ fwd = j := ι_extend c c' hvalC ⟨U, hUd, j⟩ hj
  have h₂ : V.ι ≫ bwd = j.isoOpensRange.inv ≫ U.ι :=
    ι_extend c' c hvalC' ⟨V, hVd, j.isoOpensRange.inv ≫ U.ι⟩ hG

  haveI : C.IsSeparated := isSeparated_of_isSeparated_over c
  haveI : C'.IsSeparated := isSeparated_of_isSeparated_over c'
  haveI := isDominant_ι U hU
  haveI := isDominant_ι V hV
  have hfb : fwd ≫ bwd = 𝟙 C := by
    refine ext_of_isDominant U.ι ?_
    rw [Category.comp_id, reassoc_of% h₁, ← j.isoOpensRange_hom_ι, Category.assoc, h₂,
      Iso.hom_inv_id_assoc]
  have hbf : bwd ≫ fwd = 𝟙 C' := by
    refine ext_of_isDominant V.ι ?_
    rw [Category.comp_id, reassoc_of% h₂, h₁, Scheme.Hom.isoOpensRange_inv_comp]
  exact ⟨⟨fwd, bwd, hfb, hbf⟩, extend_over c c' hvalC ⟨U, hUd, j⟩ hj, h₁⟩

end

end S_AlgebraicGeometry_Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper (solution)
