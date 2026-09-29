-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_isClosedImmersion_comp_eq_id_of_retraction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c869c4f0-5541-5d79-aefa-31d6907e1629

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_comp_eq_id_of_retraction

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_comp_eq_id_of_retraction.AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_comp_eq_id_of_retraction.AlgebraicCurve.TwoChartIntegralModel"
open scoped TensorProduct

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel isClosed_singleton_of_ne_genericPoint"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlgFin ιFin toBase ιFin_toBase fibre"
namespace SectionCompGen
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

theorem range_subset_of_isOpen {A : Type u} [CommRing A] [IsLocalRing A] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of A) ⟶ Y) {U : Set Y} (hU : IsOpen U)
    (h : f (IsLocalRing.closedPoint A) ∈ U) : Set.range f ⊆ U := by
  rintro _ ⟨x, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint x).map f.continuous).mem_open hU h

section Chart

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
  (κ : Type u) [CommRing κ] [Algebra R κ]

theorem isPullback_chart
    (c : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F j))) ⟶
      pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom) ≫ ιFin R F j)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j))))) :
    IsPullback c (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom)) (pullback.fst _ _) (ιFin R F j) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd _ _)
    (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap R κ))) (h₂₂ := toBase R F j) ?_ hcfst
    (IsPullback.of_hasPullback _ _).flip
  rw [hcsnd, ιFin_toBase]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ ↥(chartAlgFin R F j))

theorem isOpenImmersion_chart
    (c : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F j))) ⟶
      pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom) ≫ ιFin R F j)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j))))) :
    IsOpenImmersion c := by
  rw [← (isPullback_chart R F j κ c hcfst hcsnd).isoPullback_hom_fst]
  infer_instance

theorem mem_range_chart
    (c : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F j))) ⟶
      pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom) ≫ ιFin R F j)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j)))))
    (x : ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))))
    (hx : (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) x ∈ Set.range (ιFin R F j)) : x ∈ Set.range c := by
  have H := isPullback_chart R F j κ c hcfst hcsnd
  have hx' : x ∈ Set.range (pullback.fst (pullback.fst (toBase R F j)
      (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) (ιFin R F j)) := by
    rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨t, rfl⟩ := hx'
  exact ⟨H.isoPullback.inv t, by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst]⟩

end Chart

theorem isDominant_of_isOpenImmersion {U X : Scheme.{u}} [IrreducibleSpace X] (f : U ⟶ X) [IsOpenImmersion f]
    [Nonempty U] : IsDominant f := by
  refine ⟨?_⟩
  have hη : genericPoint X ∈ Set.range f.base :=
    ((genericPoint_spec X).mem_open_set_iff f.isOpenEmbedding.isOpen_range).mpr (by simpa using Set.range_nonempty _)
  intro y
  have : y ∈ closure ({genericPoint X} : Set X) := by
    rw [(genericPoint_spec X).def]; trivial
  exact closure_mono (Set.singleton_subset_iff.mpr hη) this

end AlgebraicCurve.TwoChartIntegralModel.SectionCompGen

open AlgebraicCurve.TwoChartIntegralModel.SectionCompGen in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (R : Type u) [CommRing R]
    (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (F₀ : Type u) [Field F₀] [Algebra R F₀] (j₀ : F₀) [Fact (j₀ ≠ 0)]
    [IsProper (toBase R F j)] [IsProper (toBase R F₀ j₀)]

    (π : TwoChartIntegralModel R F j ⟶ TwoChartIntegralModel R F₀ j₀) (hπ : π ≫ toBase R F₀ j₀ = toBase R F j)
    (ι : ↥(chartAlgFin R F₀ j₀) →ₐ[R] ↥(chartAlgFin R F j))
    (hπchart : ιFin R F j ≫ π = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ ιFin R F₀ j₀)

    (κ : Type u) [Field κ] [Algebra R κ]
    [IsIntegral (pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))]
    [SmoothOfRelativeDimension 1
      (pullback.snd (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))]
    [Nontrivial (κ ⊗[R] ↥(chartAlgFin R F₀ j₀))]

    (πκ : pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) ⟶
      pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hπκfst : πκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π)
    (hπκsnd : πκ ≫ pullback.snd _ _ = pullback.snd _ _)

    (c₀ : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F₀ j₀))) ⟶
      pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F₀ j₀))).toRingHom) ≫ ιFin R F₀ j₀)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(chartAlgFin R F₀ j₀)))))
    (c : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F j))) ⟶
      pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom) ≫ ιFin R F j)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j)))))

    (σ₀ : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] κ ⊗[R] ↥(chartAlgFin R F₀ j₀))
    (hσ₀ : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z) :
    ∃ comp₀ : pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) ⟶
        pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))),
      comp₀ ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      IsClosedImmersion comp₀ ∧
      comp₀ ≫ πκ = 𝟙 _ ∧
      c₀ ≫ comp₀ = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c ∧

      (∀ x, comp₀.base x ∈ Set.range c.base → x ∈ Set.range c₀.base) := by
  classical

  haveI hcO : IsOpenImmersion c := isOpenImmersion_chart R F j κ c hcfst hcsnd
  haveI hc₀O : IsOpenImmersion c₀ := isOpenImmersion_chart R F₀ j₀ κ c₀ hc₀fst hc₀snd
  haveI hne : Nonempty ↥(Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F₀ j₀)))) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance

  have hcπ : c ≫ πκ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) ι).toRingHom) ≫ c₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hc₀fst, hπκfst, ← Category.assoc, hcfst,
        Category.assoc, hπchart, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 3
    · rw [Category.assoc, Category.assoc, hc₀snd, hπκsnd, hcsnd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a
      simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeftRingHom_apply]

  have hσSpec : Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) ι).toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1
    rw [← CommRingCat.ofHom_id]
    congr 1
    exact RingHom.ext fun z => hσ₀ z

  have hf : (Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c) ≫
      pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) =
      c₀ ≫ pullback.snd (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) := by
    rw [Category.assoc, hcsnd, hc₀snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [show a ⊗ₜ[R] (1 : ↥(chartAlgFin R F j)) = algebraMap κ _ a by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply],
      AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

  have hηmem : genericPoint ↑(pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) ∈ Set.range c₀.base :=
    ((genericPoint_spec _).mem_open_set_iff c₀.isOpenEmbedding.isOpen_range).mpr (by simpa using Set.range_nonempty _)
  have hreg : ∀ x : ↑(pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))), x ∉ Set.range c₀.base →
      IsDiscreteValuationRing ((pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).presheaf.stalk x) := by
    intro x hx
    have hxη : x ≠ genericPoint _ := fun h => hx (h ▸ hηmem)
    exact SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed
      (pullback.snd (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) x
      (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
        (pullback.snd (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) x hxη)

  obtain ⟨comp₀, hover, hchart⟩ :=
    AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk
      (pullback.snd (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) c₀ hreg
      (pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
      (Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c) hf

  have hπsnd : πκ ≫
      pullback.snd (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) =
      pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) := hπκsnd
  haveI : IsDominant c₀ := isDominant_of_isOpenImmersion c₀
  have hsec : comp₀ ≫ πκ = 𝟙 _ := by
    refine ext_of_isDominant_of_isSeparated
      (pullback.snd (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) ?_ c₀ ?_
    · rw [Category.assoc, hπsnd, hover, Category.id_comp]
    · rw [← Category.assoc, hchart, Category.assoc, hcπ, ← Category.assoc, hσSpec, Category.id_comp, Category.comp_id]

  haveI : IsSeparated (πκ) := by
    haveI : IsSeparated (πκ ≫
        pullback.snd (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) := by
      rw [hπsnd]; infer_instance
    exact IsSeparated.of_comp _
      (pullback.snd (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
  have hci : IsClosedImmersion comp₀ := by
    haveI : IsClosedImmersion (comp₀ ≫ πκ) := by
      rw [hsec]; infer_instance
    exact IsClosedImmersion.of_comp comp₀ (πκ)

  refine ⟨comp₀, hover, hci, hsec, hchart, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hx
  have h1 : x = (πκ).base (comp₀.base x) := by
    rw [← Scheme.Hom.comp_apply, hsec]; rfl
  rw [h1, ← hy, ← Scheme.Hom.comp_apply, hcπ, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

end S_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_comp_eq_id_of_retraction
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_comp_eq_id_of_retraction (solution)
