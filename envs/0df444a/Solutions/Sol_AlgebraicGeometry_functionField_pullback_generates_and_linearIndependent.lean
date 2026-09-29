-- Prove2me | solution 1 for AlgebraicGeometry.functionField_pullback_generates_and_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9971e02d-86a5-5cda-b5bc-983391308589

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing
import Theorems.Thm_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_functionField_pullback_generates_and_linearIndependent
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

open scoped TensorProduct

theorem solution
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of k)) [IsIntegral Y]
    [IsIntegral (Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))))]
    (prStar : ↑Y.functionField →+* ↑(Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K)))).functionField)
    (hpr : ∀ (U : Y.Opens) (hU : genericPoint Y ∈ U)
      (hU' : genericPoint (Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) ∈
        (Limits.pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⁻¹ᵁ U)
      (sec : Y.presheaf.obj (Opposite.op U)),
      prStar ((Y.presheaf.germ U (genericPoint Y) hU).hom sec) =
        ((Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.germ _ (genericPoint (Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) hU').hom
          (((Limits.pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K)))).app U).hom sec)) :
    (Subfield.closure
        (Set.range (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k K))))) ∪
          Set.range prStar) = ⊤) ∧
    (∀ (t : Finset ↑Y.functionField),
      (∀ c : t → k, (∑ x : t, AlgebraicCurve.baseToFunctionField g (c x) * (x : ↑Y.functionField)) = 0 → ∀ x : t, c x = 0) →
      ∀ c : t → K, (∑ x : t, AlgebraicCurve.baseToFunctionField (Limits.pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (c x) *
          prStar (x : ↑Y.functionField)) = 0 → ∀ x : t, c x = 0) := by
  classical
  letI instk : Algebra k ↑Y.functionField := (AlgebraicCurve.baseToFunctionField g).toAlgebra
  letI instK : Algebra K
      ↑(Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K)))).functionField :=
    (AlgebraicCurve.baseToFunctionField
      (Limits.pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k K))))).toAlgebra
  obtain ⟨Φ, hinj, hfrac, hgerm⟩ :=
    AlgebraicGeometry.exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing K g

  have hgen : ∀ U : Y.Opens, genericPoint Y ∈ U →
      genericPoint (Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) ∈
        (Limits.pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⁻¹ᵁ U := by
    intro U hU
    have h := AlgebraicGeometry.genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
      (R := k) (K := K) (algebraMap k K).injective g
      (𝟙 (Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))))) U ⟨_, hU⟩
    simpa using h

  have hΦ : ∀ f : ↑Y.functionField, Φ ((1 : K) ⊗ₜ[k] f) = prStar f := by
    intro f
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf f
    have hU' := hgen U hU
    haveI : Nonempty (U : Scheme.{u}) := ⟨⟨_, hU⟩⟩
    haveI : Nonempty (((Limits.pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⁻¹ᵁ U :
        (Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Opens) : Scheme.{u}) :=
      ⟨⟨_, hU'⟩⟩
    have h1 := hgerm U s
    have h2 := hpr U hU hU' s
    exact h1.trans h2.symm
  refine ⟨?_, ?_⟩
  ·
    set S := Subfield.closure
        (Set.range (AlgebraicCurve.baseToFunctionField
            (Limits.pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k K))))) ∪
          Set.range prStar) with hS
    have hΦmem : ∀ a : K ⊗[k] ↑Y.functionField, Φ a ∈ S := by
      intro a
      induction a using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact S.zero_mem
      | tmul x y =>
          have hxy : x ⊗ₜ[k] y = x • ((1 : K) ⊗ₜ[k] y) := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rw [hxy, map_smul, hΦ, Algebra.smul_def]
          exact mul_mem (Subfield.subset_closure (Or.inl ⟨x, rfl⟩))
            (Subfield.subset_closure (Or.inr ⟨y, rfl⟩))
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨a, b, -, hab⟩ :=
      @IsFractionRing.div_surjective (K ⊗[k] ↑Y.functionField) _ _ _ Φ.toRingHom.toAlgebra hfrac z
    rw [← hab]
    exact div_mem (hΦmem a) (hΦmem b)
  ·
    intro t ht c hc
    have hli : LinearIndependent k (fun x : t => (x : ↑Y.functionField)) := by
      rw [Fintype.linearIndependent_iff]
      intro d hd
      refine ht d ?_
      simp only [Algebra.smul_def] at hd
      exact hd
    have hliK := Module.Flat.linearIndependent_one_tmul (S := K) hli
    have hsum : ∑ x : t, c x • ((1 : K) ⊗ₜ[k] (x : ↑Y.functionField)) = 0 := by
      apply hinj
      rw [map_sum, map_zero]
      simp_rw [map_smul]
      simp_rw [hΦ, Algebra.smul_def]
      exact hc
    exact Fintype.linearIndependent_iff.mp hliK c hsum

end S_AlgebraicGeometry_functionField_pullback_generates_and_linearIndependent
end P2MW
export P2MW.S_AlgebraicGeometry_functionField_pullback_generates_and_linearIndependent (solution)
