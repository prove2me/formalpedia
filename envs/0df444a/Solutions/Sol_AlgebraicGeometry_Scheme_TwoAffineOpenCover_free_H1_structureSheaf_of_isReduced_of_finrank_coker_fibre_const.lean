-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.free_H1_structureSheaf_of_isReduced_of_finrank_coker_fibre_const
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/997e9f4c-3fd0-553b-a128-d9873d57566b

import Theorems.Thm_Module_projective_of_isReduced_of_finrank_fiber_const
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_H1_structureSheaf_of_isReduced_of_finrank_coker_fibre_const

set_option autoImplicit false

noncomputable section

universe u v w

namespace H1FreeProof

open scoped TensorProduct

section Coker

variable {R : Type u} [CommRing R] {C0 : Type v} {C1 : Type v} [AddCommGroup C0] [Module R C0]
  [AddCommGroup C1] [Module R C1]

theorem surjective_mkQ_baseChange (d : C0 →ₗ[R] C1) (A : Type w) [CommRing A] [Algebra R A] :
    Function.Surjective ((LinearMap.range d).mkQ.baseChange A) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _)

theorem ker_mkQ_baseChange (d : C0 →ₗ[R] C1) (A : Type w) [CommRing A] [Algebra R A] :
    LinearMap.ker ((LinearMap.range d).mkQ.baseChange A) = LinearMap.range (d.baseChange A) := by
  have hex : Function.Exact (d.baseChange A) ((LinearMap.range d).mkQ.baseChange A) := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact A (LinearMap.exact_map_mkQ_range d) (Submodule.mkQ_surjective _)
  exact LinearMap.exact_iff.mp hex

noncomputable def cokerBaseChangeEquiv (d : C0 →ₗ[R] C1) (A : Type w) [CommRing A] [Algebra R A] :
    ((A ⊗[R] C1) ⧸ LinearMap.range (d.baseChange A)) ≃ₗ[A] A ⊗[R] (C1 ⧸ LinearMap.range d) :=
  (Submodule.quotEquivOfEq _ _ (ker_mkQ_baseChange d A).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (surjective_mkQ_baseChange d A))

theorem cokerBaseChangeEquiv_mk (d : C0 →ₗ[R] C1) (A : Type w) [CommRing A] [Algebra R A]
    (x : A ⊗[R] C1) :
    cokerBaseChangeEquiv d A (Submodule.Quotient.mk x) = (LinearMap.range d).mkQ.baseChange A x :=
  rfl

theorem cokerBaseChangeEquiv_symm_tmul (d : C0 →ₗ[R] C1) (A : Type w) [CommRing A] [Algebra R A]
    (a : A) (y : C1) :
    (cokerBaseChangeEquiv d A).symm (a ⊗ₜ[R] Submodule.Quotient.mk y) = Submodule.Quotient.mk (a ⊗ₜ[R] y) := by
  rw [LinearEquiv.symm_apply_eq, cokerBaseChangeEquiv_mk, LinearMap.baseChange_tmul, Submodule.mkQ_apply]

theorem projective_coker [IsReduced R] (d : C0 →ₗ[R] C1)
    [Module.FinitePresentation R (C1 ⧸ LinearMap.range d)] {n : ℕ}
    (hH1 : ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
      ((𝔭.asIdeal.ResidueField ⊗[R] C1) ⧸ LinearMap.range (d.baseChange 𝔭.asIdeal.ResidueField)) = n) :
    Module.Projective R (C1 ⧸ LinearMap.range d) ∧
      ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
          (𝔭.asIdeal.ResidueField ⊗[R] (C1 ⧸ LinearMap.range d)) = n := by
  have h : ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
      (𝔭.asIdeal.ResidueField ⊗[R] (C1 ⧸ LinearMap.range d)) = n := fun 𝔭 =>
    ((cokerBaseChangeEquiv d 𝔭.asIdeal.ResidueField).finrank_eq).symm.trans (hH1 𝔭)
  exact ⟨Module.projective_of_isReduced_of_finrank_fiber_const h, h⟩

end Coker

end H1FreeProof

namespace H1FreeProof

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem free_H1
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [_root_.IsReduced R]
    {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (hfin : Module.Finite R (𝒱.structureSheafSections c).H1) {n : ℕ}
    (hH1 : ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
      ((𝔭.asIdeal.ResidueField ⊗[R] (𝒱.cover c).A01) ⧸
        LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) = n) :
    Module.Free R (𝒱.structureSheafSections c).H1 ∧
      Module.finrank R (𝒱.structureSheafSections c).H1 = n ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        ∃ (e01 : (A ⊗[R] (𝒱.cover c).A01) ≃ₐ[A]
            ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
          (e : A ⊗[R] (𝒱.structureSheafSections c).H1 ≃ₗ[A]
            ((𝒱.pullback c A).structureSheafSections
              (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H1),
          (∀ s, e01 ((1 : A) ⊗ₜ[R] s)
              = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s) ∧
          ∀ (a : A) (y : (𝒱.cover c).A01),
            e (a ⊗ₜ[R] Submodule.Quotient.mk y) = Submodule.Quotient.mk (e01 (a ⊗ₜ[R] y)) := by
  haveI := hfin
  haveI : Module.FinitePresentation R (𝒱.structureSheafSections c).H1 :=
    Module.finitePresentation_of_finite R _

  obtain ⟨hproj, hrank⟩ := projective_coker (𝒱.structureSheafSections c).cechDiff hH1
  haveI : Module.Projective R (𝒱.structureSheafSections c).H1 := hproj
  haveI : Module.Flat R (𝒱.structureSheafSections c).H1 := Module.Flat.of_projective

  haveI hfree : Module.Free R (𝒱.structureSheafSections c).H1 := Module.free_of_flat_of_isLocalRing
  refine ⟨hfree, ?_, fun A _ _ => ?_⟩
  ·
    obtain ⟨𝔭⟩ := (inferInstance : Nonempty (PrimeSpectrum R))
    rw [← hrank 𝔭]
    exact (Module.finrank_baseChange).symm
  ·
    obtain ⟨e0, e1, e01, eH0, eH1, -, -, h01, -, hH1'⟩ :=
      AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf 𝒱 c A
    refine ⟨e01, (cokerBaseChangeEquiv (𝒱.structureSheafSections c).cechDiff A).symm.trans eH1, h01,
      fun a y => ?_⟩
    rw [LinearEquiv.trans_apply, cokerBaseChangeEquiv_symm_tmul, hH1']

end H1FreeProof

open scoped TensorProduct in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [_root_.IsReduced R]
    {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (hfin : Module.Finite R (𝒱.structureSheafSections c).H1) {n : ℕ}
    (hH1 : ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
      ((𝔭.asIdeal.ResidueField ⊗[R] (𝒱.cover c).A01) ⧸
        LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) = n) :
    Module.Free R (𝒱.structureSheafSections c).H1 ∧
      Module.finrank R (𝒱.structureSheafSections c).H1 = n ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        ∃ (e01 : (A ⊗[R] (𝒱.cover c).A01) ≃ₐ[A]
            ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
          (e : A ⊗[R] (𝒱.structureSheafSections c).H1 ≃ₗ[A]
            ((𝒱.pullback c A).structureSheafSections
              (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H1),
          (∀ s, e01 ((1 : A) ⊗ₜ[R] s)
              = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s) ∧
          ∀ (a : A) (y : (𝒱.cover c).A01),
            e (a ⊗ₜ[R] Submodule.Quotient.mk y) = Submodule.Quotient.mk (e01 (a ⊗ₜ[R] y)) :=
  H1FreeProof.free_H1 𝒱 c hfin hH1

end

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_H1_structureSheaf_of_isReduced_of_finrank_coker_fibre_const
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_H1_structureSheaf_of_isReduced_of_finrank_coker_fibre_const (solution)
