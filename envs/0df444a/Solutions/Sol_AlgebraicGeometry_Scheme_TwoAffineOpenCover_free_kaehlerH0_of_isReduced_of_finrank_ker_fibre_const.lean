-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.free_kaehlerH0_of_isReduced_of_finrank_ker_fibre_const
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f3d65091-222a-539f-8ef3-5d0be9234851

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Theorems.Thm_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective
import Theorems.Thm_TwoChartCech_projective_ker_of_isReduced_of_kerMapBaseChange_bijective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_kaehlerH0_of_isReduced_of_finrank_ker_fibre_const

set_option autoImplicit false

noncomputable section

namespace KaehlerH0Free
universe u
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem flat_prod {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ f hf
  have key : (TensorProduct.prodRight R R Q M N).toLinearMap ∘ₗ f.rTensor (M × N) =
      ((f.rTensor M).prodMap (f.rTensor N)) ∘ₗ (TensorProduct.prodRight R R P M N).toLinearMap := by
    apply TensorProduct.ext'
    intro p mn
    simp [TensorProduct.prodRight_tmul]
  have hinj : Function.Injective ((TensorProduct.prodRight R R Q M N).toLinearMap ∘ₗ f.rTensor (M × N)) := by
    rw [key]
    exact (Function.Injective.prodMap (Module.Flat.rTensor_preserves_injective_linearMap f hf)
      (Module.Flat.rTensor_preserves_injective_linearMap f hf)).comp
        (TensorProduct.prodRight R R P M N).injective
  exact fun x y h => hinj (by simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h])

theorem main {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [_root_.IsReduced R]
    {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    [Module.Flat R Ω[(𝒱.cover c).A0⁄R]] [Module.Flat R Ω[(𝒱.cover c).A1⁄R]]
    [Module.Flat R Ω[(𝒱.cover c).A01⁄R]]
    (hfin : Module.Finite R (𝒱.kaehlerSections c).H0 ∧ Module.Finite R (𝒱.kaehlerSections c).H1) {n : ℕ}
    (hH0 : ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
      (LinearMap.ker ((𝒱.kaehlerSections c).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) = n) :
    Module.Free R (𝒱.kaehlerSections c).H0 ∧
      Module.finrank R (𝒱.kaehlerSections c).H0 = n ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom (𝒱.kaehlerSections c).cechDiff A) := by
  haveI : Module.Flat R ((𝒱.kaehlerSections c).M0 × (𝒱.kaehlerSections c).M1) := flat_prod
  haveI : Module.Finite R (LinearMap.ker (𝒱.kaehlerSections c).cechDiff) := hfin.1
  haveI : Module.Finite R ((𝒱.kaehlerSections c).M01 ⧸ LinearMap.range (𝒱.kaehlerSections c).cechDiff) := hfin.2
  obtain ⟨G, ι0, ι1, comm, hG⟩ :=
    TwoChartCech.exists_twoTermComplex_kerMapBaseChange_bijective (𝒱.kaehlerSections c).cechDiff
  obtain ⟨hproj, hbc, hrank⟩ :=
    TwoChartCech.projective_ker_of_isReduced_of_kerMapBaseChange_bijective G ι0 ι1 comm hG hH0
  haveI : Module.Projective R (𝒱.kaehlerSections c).H0 := hproj
  haveI : Module.Flat R (𝒱.kaehlerSections c).H0 := Module.Flat.of_projective
  haveI hfree : Module.Free R (𝒱.kaehlerSections c).H0 := Module.free_of_flat_of_isLocalRing
  refine ⟨hfree, ?_, hbc⟩
  obtain ⟨𝔭⟩ := (inferInstance : Nonempty (PrimeSpectrum R))
  rw [← hrank 𝔭]
  exact (Module.finrank_baseChange).symm

end KaehlerH0Free

end

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [_root_.IsReduced R]
    {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    [Module.Flat R Ω[(𝒱.cover c).A0⁄R]] [Module.Flat R Ω[(𝒱.cover c).A1⁄R]]
    [Module.Flat R Ω[(𝒱.cover c).A01⁄R]]
    (hfin : Module.Finite R (𝒱.kaehlerSections c).H0 ∧ Module.Finite R (𝒱.kaehlerSections c).H1) {n : ℕ}
    (hH0 : ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
      (LinearMap.ker ((𝒱.kaehlerSections c).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) = n) :
    Module.Free R (𝒱.kaehlerSections c).H0 ∧
      Module.finrank R (𝒱.kaehlerSections c).H0 = n ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom (𝒱.kaehlerSections c).cechDiff A) :=
  KaehlerH0Free.main 𝒱 c hfin hH0

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_kaehlerH0_of_isReduced_of_finrank_ker_fibre_const
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_kaehlerH0_of_isReduced_of_finrank_ker_fibre_const (solution)
